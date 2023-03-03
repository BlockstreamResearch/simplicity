#ifndef SIMPLICITY_CALLONCE_H
#define SIMPLICITY_CALLONCE_H

#ifdef SINGLE_THREADED

typedef struct { _Bool flag; } once_flag;
#define ONCE_FLAG_INIT { 0 }

static inline void call_once(once_flag* initialized, void (*initialize)(void)) {
  if (!initialized->flag) {
    initialized->flag = 1;
    initialize();
  }
}

#elif __STDC_VERSION__ >= 201112L && !defined(__STDC_NO_THREADS__)

#include <threads.h>

#else

#include <pthread.h>

#define once_flag pthread_once_t
#define ONCE_FLAG_INIT PTHREAD_ONCE_INIT
#define call_once pthread_once

#endif

#endif
