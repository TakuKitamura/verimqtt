#include <stdio.h>
#include <stdint.h>

void print_hex(uint8_t i) {
  printf("%02x", i);
}

void print_buffer(uint8_t *buffer, uint32_t buffer_size) {
  printf("[");
  for (int i = 0; i < buffer_size; i++)
  {
    printf("%02x", buffer[i]);
    if (i != buffer_size - 1)
      printf(", ");
  }
  puts("]");
}