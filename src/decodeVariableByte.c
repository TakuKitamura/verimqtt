#include <stdio.h>

// decoding a variable byte integer 

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901107
// 1.5.5 Variable Byte Integer

// encode(54321 base10) = (0xb1a803 base16)
int main() {
	int multiplier = 1;
	size_t value = 0;
    int i = 0;
    char data[4] = {0x80, 0x80, 0x01, 0x01};
    unsigned char c;

    for(i = 0; i <= 3; i++) {
        printf("%d\n", i);
        c = data[i];
		value = value + ((c & 127) * multiplier);

        if ((c & 128) == 0) {
            printf("value=%zd\n", value);
            return value;
        }

        if (i == 3) {
            puts("malformed variable byte integer");
            return 1;
        }

        multiplier = multiplier * 128;
	}

    return 0;
}