#include <stdio.h>
#include <stdint.h>
#include "Utils.h"

void Utils_print_hex(uint8_t i) {
  printf("%02x", i);
}

C_String_t Utils_topic_name_uint8_to_c_string(uint8_t *u8_buffer) {
  return (char *)u8_buffer;
}

C_String_t Utils_payload_uint8_to_c_string(uint8_t *u8_buffer, uint32_t n) {
  return (char *)u8_buffer;
}