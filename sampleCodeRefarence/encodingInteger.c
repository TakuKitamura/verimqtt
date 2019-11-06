#include <stdio.h>

// encoding a non-negative integer 

int main() {
	size_t length = 123456789;
	printf("encode(%zu base10) = (0x", length);
	do {
		char d = length % 128;
		length /= 128;
		if (length > 0) {
			d |= 128;
		}
		printf("%02x", d & 255);
	} while (length > 0);
	puts(" base16)");
	return 0;
}