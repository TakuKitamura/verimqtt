#include <stdint.h>
#include "kremlib.h"

C_String_t topic_name_uint8_to_c_string(uint8_t *u8_buffer) {
  return (char *)u8_buffer;
}

C_String_t payload_uint8_to_c_string(uint8_t *u8_buffer, uint32_t min_packet_size, uint32_t max_packet_size, uint32_t n) {
  return (char *)u8_buffer;
}