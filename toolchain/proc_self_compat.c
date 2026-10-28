#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
/* Lean 4.19 uses /proc/<getpid()>/exe; this container exposes /proc/self/exe
   but its PID namespace does not expose that numeric path. No Lean kernel or
   proof routines are altered: only the equivalent executable path is used. */
ssize_t readlink(const char *path, char *buf, size_t bufsiz) {
  static ssize_t (*real_readlink)(const char *, char *, size_t) = 0;
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  char expected[64];
  snprintf(expected, sizeof(expected), "/proc/%d/exe", getpid());
  if (strcmp(path, expected) == 0) path = "/proc/self/exe";
  return real_readlink(path, buf, bufsiz);
}
