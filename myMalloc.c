#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from tche base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
  (void) raw_size;


  header * result;

  if (raw_size == 0) {
	  return NULL;
  }
  
  if (raw_size <= 8) {
	  raw_size = 16;
  }
  size_t blockSize = 0;
  if ((raw_size%8) == 0) {
	  blockSize = raw_size+ALLOC_HEADER_SIZE;
  }
  else {
	  blockSize = ((raw_size/8)+1) * 8 + ALLOC_HEADER_SIZE;
  }
  
  for (int i = 0; i < N_LISTS; i++) {
	  header * head_of_list = &freelistSentinels[i];
	  header * freelist = &freelistSentinels[i];
	  while (freelist->next != head_of_list) {
		  freelist = freelist->next;
		  if (get_size(freelist) >= blockSize) {
			 if (get_size(freelist) - blockSize < 2 * ALLOC_HEADER_SIZE) {

				freelist->next->prev = freelist->prev;
				freelist->prev->next = freelist->next;

				set_state(freelist, ALLOCATED);
				result = freelist;
			 }
			 else {	
				 get_right_header(freelist)->left_size = blockSize;
			  	 result = get_header_from_offset(freelist, (get_size(freelist) - blockSize));
                                 set_size(result, blockSize);
                                 set_state(result, ALLOCATED);
                                 result->left_size = get_size(freelist) - blockSize;

                                 set_size(freelist, result->left_size);
                                 set_state(freelist, UNALLOCATED);
				 if (get_size(freelist) < 488) {
				 	freelist->next->prev = freelist->prev;
                                 	freelist->prev->next = freelist->next;

					int index = 0;
                                 	if ((get_size(freelist)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
                                 	        index = N_LISTS-1;
                                 	}
                                 	else {
                                         	if ((get_size(freelist)-ALLOC_HEADER_SIZE)%8 != 0) {
                                                	 index = ((get_size(freelist)-ALLOC_HEADER_SIZE)/8);
                                        	}
                                         	else {
                                                	 index = ((get_size(freelist)-ALLOC_HEADER_SIZE)/8)-1;
                                       	 	}
                                 	}
                                 	header * sentinel = &freelistSentinels[index];

                                 	freelist->next = sentinel->next;
                                 	freelist->prev = sentinel;
                                 	sentinel->next->prev = freelist;
                                 	sentinel->next = freelist;
				 }
			 }
			  return (get_header_from_offset(result, ALLOC_HEADER_SIZE));
		  }
		  
	  }

  }

  bool flag = false;
  while (flag == false) {

	  header * newChunk = allocate_chunk(ARENA_SIZE);
  	  header * prevFencePost = get_header_from_offset(newChunk, -ALLOC_HEADER_SIZE);
	  header * sentinel2 = &freelistSentinels[N_LISTS-1];

	if (get_right_header(lastFencePost) == get_left_header(newChunk)) {	  
	  	if (get_state(get_left_header(lastFencePost)) == UNALLOCATED) {
			  
			  header * left2 = get_left_header(lastFencePost);
			  size_t oldSize = get_size(left2);
			  set_size(left2, get_size(left2)+ARENA_SIZE);
			  get_right_header(newChunk)->left_size = get_size(left2);

			  if (oldSize < 488) {
			  	left2->next->prev = left2->prev;
			  	left2->prev->next = left2->next;
			  
			  	left2->next = sentinel2->next;
                          	left2->prev = sentinel2;
                          	sentinel2->next->prev = left2;
                          	sentinel2->next = left2;
			  }
			  if (get_size(left2) >= blockSize) {
                          	if (get_size(left2) - blockSize < 2 * ALLOC_HEADER_SIZE) {

                                	left2->next->prev = left2->prev;
                                	left2->prev->next = left2->next;

                               		 set_state(left2, ALLOCATED);
                               		 result = left2;
					 lastFencePost = get_header_from_offset(newChunk, ARENA_SIZE-2*ALLOC_HEADER_SIZE);
                                	return (get_header_from_offset(result, ALLOC_HEADER_SIZE));
                         	}
                        	 else {
                                 get_right_header(newChunk)->left_size = blockSize;
				 result = get_header_from_offset(newChunk, (get_size(newChunk) - blockSize));
                                 set_size(result, blockSize);
                                 set_state(result, ALLOCATED);
                                 result->left_size = get_size(left2) - blockSize;

				 set_size(left2, result->left_size);
                                 set_state(left2, UNALLOCATED);
				 if (get_size(left2) < 488) {
                                 	left2->next->prev = left2->prev;
                                 	left2->prev->next = left2->next;
					int index = 0;
                                 	if ((get_size(left2)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
                                        	 index = N_LISTS-1;
                                 	}
                                 	else {
                                         	if ((get_size(left2)-ALLOC_HEADER_SIZE)%8 != 0) {
                                                	 index = ((get_size(left2)-ALLOC_HEADER_SIZE)/8);
                                        	}
                                         	else {
                                                	 index = ((get_size(left2)-ALLOC_HEADER_SIZE)/8)-1;
                                        	}
                                 	}
                                 	header * sentinel = &freelistSentinels[index];

                                 	left2->next = sentinel->next;
                                 	left2->prev = sentinel;
                                 	sentinel->next->prev = left2;
                                 	sentinel->next = left2;
                         
				 }

                                 lastFencePost = get_header_from_offset(newChunk, ARENA_SIZE-2*ALLOC_HEADER_SIZE);
                                 return (get_header_from_offset(result, ALLOC_HEADER_SIZE));
                         }
			  }
		  }
		  else if (get_state(get_left_header(lastFencePost)) == ALLOCATED) {
			  set_state(lastFencePost, UNALLOCATED);
			  set_size(lastFencePost, ARENA_SIZE);
			  get_right_header(newChunk)->left_size = get_size(lastFencePost);
			  
			  lastFencePost->next = sentinel2->next;
			  lastFencePost->prev = sentinel2;
			  sentinel2->next->prev = lastFencePost;
			  sentinel2->next = lastFencePost;


			  if (get_size(lastFencePost) >= blockSize) {
                               
				 if (get_size(lastFencePost) - blockSize < 2 * ALLOC_HEADER_SIZE) {

                                lastFencePost->next->prev = lastFencePost->prev;
                                lastFencePost->prev->next = lastFencePost->next;

                                set_state(lastFencePost, ALLOCATED);
                                result = lastFencePost;
				lastFencePost = get_header_from_offset(newChunk, ARENA_SIZE-2*ALLOC_HEADER_SIZE);
				return (get_header_from_offset(result, ALLOC_HEADER_SIZE));
                         }
                         else {

                                 get_right_header(newChunk)->left_size = blockSize;
                                 lastFencePost->next->prev = lastFencePost->prev;
                                 lastFencePost->prev->next = lastFencePost->next;

                                 result = get_header_from_offset(newChunk, (get_size(newChunk) - blockSize));
                                 set_size(result, blockSize);
                                 set_state(result, ALLOCATED);
                                 result->left_size = get_size(newChunk) - blockSize + ALLOC_HEADER_SIZE*2;

				 newChunk = lastFencePost;
                                 set_size(newChunk, result->left_size);
                                 set_state(newChunk, UNALLOCATED);
                                 int index = 0;
                                 if ((get_size(newChunk)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
                                         index = N_LISTS-1;
                                 }
                                 else {
                                         if ((get_size(newChunk)-ALLOC_HEADER_SIZE)%8 != 0) {
                                                 index = ((get_size(newChunk)-ALLOC_HEADER_SIZE)/8);
                                        }
                                         else {
                                                 index = ((get_size(newChunk)-ALLOC_HEADER_SIZE)/8)-1;
                                        }
                                 }
                                 header * sentinel = &freelistSentinels[index];

                                 newChunk->next = sentinel->next;
                                 newChunk->prev = sentinel;
                                 sentinel->next->prev = newChunk;
                                 sentinel->next = newChunk;
				 lastFencePost = get_header_from_offset(newChunk, ARENA_SIZE);
				 return (get_header_from_offset(result, ALLOC_HEADER_SIZE));
			 }
		    }
	       }
	  }
	  else {
		  insert_os_chunk(prevFencePost);
		  newChunk->next = sentinel2->next;
		  newChunk->prev = sentinel2;
		  sentinel2->next->prev = newChunk;
		  sentinel2->next = newChunk;
		  if (get_size(newChunk) >= blockSize) {

			  if (get_size(newChunk) - blockSize < 2 * ALLOC_HEADER_SIZE) {

                                newChunk->next->prev = newChunk->prev;
                                newChunk->prev->next = newChunk->next;

                                set_state(newChunk, ALLOCATED);
                                result = newChunk;
                         }
                         else {

                                 get_right_header(newChunk)->left_size = blockSize;
                                 newChunk->next->prev = newChunk->prev;
                                 newChunk->prev->next = newChunk->next;

                                 result = get_header_from_offset(newChunk, (get_size(newChunk) - blockSize));
                                 set_size(result, blockSize);
                                 set_state(result, ALLOCATED);
                                 result->left_size = get_size(newChunk) - blockSize;

                                 set_size(newChunk, result->left_size);
                                 set_state(newChunk, UNALLOCATED);
                                 int index = 0;
                                 if ((get_size(newChunk)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
                                         index = N_LISTS-1;
                                 }
                                 else {
					 index = ((get_size(newChunk)-ALLOC_HEADER_SIZE)/8)-1;              
                                      
                                 }
                                 header * sentinel = &freelistSentinels[index];

                                 newChunk->next = sentinel->next;
                                 newChunk->prev = sentinel;
                                 sentinel->next->prev = newChunk;
                                 sentinel->next = newChunk;

			  lastFencePost = get_header_from_offset(newChunk, ARENA_SIZE-(2 * ALLOC_HEADER_SIZE));

			  return (get_header_from_offset(result, ALLOC_HEADER_SIZE));
	 	  }
	       }
	  }
  }

  return result;
  //assert(false);
  //exit(1);
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  (void) p;
  if (p == NULL) {
	  return;
  }

  header * input = ptr_to_header(p);
  if (get_state(input) != ALLOCATED) {
//	  printf("case1\n");
	  printf("Double Free Detected\n");
	  assert(false);
	  exit(1);
  }

  //printf("case2\n");
  if (get_state(get_right_header(input))!=UNALLOCATED && get_state(get_left_header(input))!=UNALLOCATED) {
	  set_state(input, UNALLOCATED);

	  int index = 0;
          if ((get_size(input)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
		  index = N_LISTS-1;
	  }
	  else {
		  index = ((get_size(input)-ALLOC_HEADER_SIZE)/8)-1;
	  }

	  header * sentinel = &freelistSentinels[index];
	  input->next = sentinel->next;
	  input->prev = sentinel;
	  sentinel->next->prev = input;
	  sentinel->next = input;
  } else if (get_state(get_right_header(input))!=UNALLOCATED && get_state(get_left_header(input))==UNALLOCATED) {
	  //f
	  set_state(input, UNALLOCATED);
	  header * left = get_left_header(input);
	  header * right = get_right_header(input);
	  size_t oldSize = get_size(left);
	  set_size(left, (get_size(left)+get_size(input)));
	  right->left_size = get_size(left);

	  if (get_size(left) - oldSize >= 8 && oldSize < 488) {
		  int index = 0;
		  //printf("left size is %ld\n", get_size(left));
		  if ((get_size(left)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
			  index = N_LISTS-1;
		  }
     		  else {
	     		  
                      	index = ((get_size(left)-ALLOC_HEADER_SIZE)/8)-1;
			  	
                  }
		  //printf("index is %d\n", index);

		  left->next->prev = left->prev;
		  left->prev->next = left->next;

		  header * sentinel = &freelistSentinels[index];
		  left->next = sentinel->next;
		  left->prev = sentinel;
		  sentinel->next->prev = left;
		  sentinel->next = left;
          }
	  
	  
  } else if (get_state(get_left_header(input))!=UNALLOCATED && get_state(get_right_header(input))==UNALLOCATED) {
	  header * right = get_right_header(input);
	  header * rightRight = get_right_header(right);
          size_t oldSize = get_size(right);
          set_size(input, (get_size(right)+get_size(input)));
	  set_state(input, UNALLOCATED);
	  rightRight->left_size = get_size(input);

          if (get_size(input) - oldSize >= 8 && oldSize < 488) {
                  int index = 0;          
                  if ((get_size(input)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
                          index = N_LISTS-1;                        
                  }                  
                  else {             
                     
                       	  index = ((get_size(input)-ALLOC_HEADER_SIZE)/8)-1;
			 
		  }

		  right->next->prev = right->prev;
                  right->prev->next = right->next;

                  header * sentinel = &freelistSentinels[index];          
                  input->next = sentinel->next;
                  input->prev = sentinel;
                  sentinel->next->prev = input;
                  sentinel->next = input;
          } else {
		  right->prev->next = input;
                  right->next->prev = input;
		  input->prev = right->prev;
		  input->next = right->next;
		  //right->prev->next = input;
		  //right->next->prev = input;
	  }
		  
  } else if (get_state(get_left_header(input))==UNALLOCATED && get_state(get_right_header(input))==UNALLOCATED) {
	  set_state(input, UNALLOCATED);
	  header * left = get_left_header(input);
	  header * right = get_right_header(input);
	  header * rightRight = get_right_header(right);
          size_t oldSizeLeft = get_size(left);
	  size_t oldSizeRight = get_size(right);
          set_size(left, (oldSizeLeft+oldSizeRight+get_size(input)));
	  
	  rightRight->left_size = get_size(left);

          if (get_size(left) - oldSizeLeft  >= 8 && oldSizeLeft < 488) {
                  int index = 0;          
                  if ((get_size(left)-ALLOC_HEADER_SIZE)/8 >= N_LISTS) {
                          index = N_LISTS-1;                        
                  }                  
                  else {             
                          if ((get_size(left)-ALLOC_HEADER_SIZE)%8 != 0) {
                                  index = ((get_size(left)-ALLOC_HEADER_SIZE)/8);
                          }
                  	  else {
                       	 	  index = ((get_size(left)-ALLOC_HEADER_SIZE)/8)-1;
                  	  }
		  }

		  left->next->prev = left->prev;
                  left->prev->next = left->next;
		  right->next->prev = right->prev;
                  right->prev->next = right->next;

                  header * sentinel = &freelistSentinels[index];          
                  left->next = sentinel->next;
                  left->prev = sentinel;
                  sentinel->next->prev = left;
                  sentinel->next = left;
          }
	  else {
	  	  right->next->prev = right->prev;
         	  right->prev->next = right->next;
  
	  }
  }
		  
			  
  //assert(false);
  //exit(1);
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
