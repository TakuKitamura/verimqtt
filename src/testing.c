#include "Test.h"

#define MK_CHECK(n)                                                            \
  void check##n(int##n##_t x, int##n##_t y) {                                  \
    if (x != y) {                                                              \
      printf("Test check failure: %" PRId##n " != %" PRId##n "\n", x, y);      \
    }                                                                          \
  }
MK_CHECK(8)
MK_CHECK(16)
MK_CHECK(32)
MK_CHECK(64)

#define MK_UCHECK(n)                                                           \
  void checku##n(uint##n##_t x, uint##n##_t y) {                               \
    if (x != y) {                                                              \
      printf("Test check failure: %" PRIu##n " != %" PRIu##n "\n", x, y);      \
    }                                                                          \
  }
MK_UCHECK(8)
MK_UCHECK(16)
MK_UCHECK(32)
MK_UCHECK(64)

void check(bool b) {
  if (!b) {
    printf("Test check failure!\n");
    // exit(253);
  }
}