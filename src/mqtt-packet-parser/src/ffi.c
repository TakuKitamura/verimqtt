#include <stdio.h>
#include <stdint.h>
#include "kremlib.h"

// 本番環境では削除
void print_hex(uint8_t i) {
  printf("%02x", i);
}

C_String_t topic_name_uint8_to_c_string(uint8_t *u8_buffer) {
  // for (int i = 0; i <= 50; i++)
  //   printf("aaa 0x%x\n", u8_buffer[i]);
  return (char *)u8_buffer;
}

C_String_t payload_uint8_to_c_string(uint8_t *u8_buffer, uint32_t min_packet_size, uint32_t max_packet_size, uint32_t n) {
  return (char *)u8_buffer;
}