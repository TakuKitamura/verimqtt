#include <stdio.h>

// encoding a non-negative integer 

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901107
// 1.5.5 Variable Byte Integer
int main() {
	size_t length = 123456;
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
}