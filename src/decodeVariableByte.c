#include <stdio.h>

// decoding a variable byte integer 

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901107
// 1.5.5 Variable Byte Integer

// encode(54321 base10) = (0xb1a803 base16)
int main() {
	int multiplier = 1;
	size_t value = 0;
    int i = 0;
    char data[] = {0xb1, 0xa8, 0x03};
    char c;
	do {
        c = data[i];
		value += (c & 127) * multiplier;
        if (multiplier > 128*128*128) {
            puts("malformed variable byte integer");
            return 1;
        }
		multiplier *= 128;
        i++;
	} while ((c & 128) != 0);
    printf("value=%zd\n", value);
    return 0;
}