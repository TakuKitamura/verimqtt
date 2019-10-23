#include "Testing.h"
#include <stdbool.h>
#include <string.h>
#include <limits.h>

static unsigned int total = 0;
static unsigned int pass = 0;

void Testing_test_start() {
  puts("TEST START.");
}

void Testing_test_end() {
  if (total != pass) {
    printf("\x1b[35mSOME TESTS FAILED (%u/%u) (PASS/TOTAL)\x1b[0m\n", pass, total);
    exit(1);
  } else {
    puts("\x1b[36mALL TESTS PASSED!\x1b[0m\n");
  }
}

void test_static(bool is_pass) {
  total++;
  if (total == UINT_MAX) {
    puts("test-code has so many tests.");
    exit(1);
  }

  if (is_pass == true) {
    pass++;
  }
}

#define MK_CHECK(n)\
  void Testing_eq_i##n(C_String_t title, int##n##_t expect, int##n##_t result) {\
    bool is_pass = (expect == result);\
    test_static(is_pass);\
    if (is_pass) {\
          printf("\x1b[32m✔\x1b[0m %s\n", title);\
    } else {\
          printf("\x1b[31m✘\x1b[0m %s\n\t expected is %" PRId##n " but result is %" PRId##n "\n", title, expect, result);\
    }\
  }
MK_CHECK(8)
MK_CHECK(16)
MK_CHECK(32)
MK_CHECK(64)

#define MK_UCHECK(n)\
  void Testing_eq_u##n(C_String_t title, uint##n##_t expect, uint##n##_t result) {\
    bool is_pass = (expect == result);\
    test_static(is_pass);\
    if (is_pass) {\
          printf("\x1b[32m✔\x1b[0m %s\n", title);\
    } else {\
          printf("\x1b[31m✘\x1b[0m %s\n\t expected is %" PRId##n " but result is %" PRId##n "\n", title, expect, result);\
    }\
  }
MK_UCHECK(8)
MK_UCHECK(16)
MK_UCHECK(32)
MK_UCHECK(64)

void Testing_eq_bool(C_String_t title, bool expect, bool result) {
  bool is_pass = (expect == result);
  test_static(is_pass);
  if (is_pass) {
    printf("\x1b[32m✔\x1b[0m %s\n", title);
  } else {
    printf("\x1b[31m✘\x1b[0m %s\n\t expected is true but result is false\n", title);
  }
}

void Testing_eq_str(C_String_t title, C_String_t expect, C_String_t result) {
  bool is_pass = (strcmp(expect, result) == 0);
  test_static(is_pass);
  if (is_pass) {
    printf("\x1b[32m✔\x1b[0m %s\n", title);
  } else {
    printf("\x1b[31m✘\x1b[0m %s\n\t expected is %s but result is %s\n", title, expect, result);
  }
}