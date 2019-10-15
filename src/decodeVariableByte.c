#include <stdio.h>

// decoding a variable byte integer 

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901107
// 1.5.5 Variable Byte Integer

// encode(54321 base10) = (0xb1a803 base16)
int main() {
	int multiplier = 1;
	size_t value = 0;
    int i = 0;
    char data[4] = {128, 128, 0x01, 0x01};
    char b, b1, b2;
    
    for(i = 0; i <= 3; i++) {
        printf("%d\n", i);

        // min: 0, max : 255
        b = data[i];

        // 最上位ビットを0に
        // min: 0, max: 127
        b1 = b & 127;

        // 最上位ビット以外を0に
        // 0 or 128
        b2 = b & 128;

        // i=0 min: 0, max:(128 - 1)
        // i=1 min: 128, max: (128*128 - 1)
        // i=2 min: 128*128, max: (128*128*128 - 1)
        // i=3 min: 128*128*128, max: (128*128*128*128 - 1)
		value = value + (b1 * multiplier);

        if (b2 == 0) {
            printf("value=%zd\n", value);
            return value;
        }

        if (i == 3) {
            puts("malformed variable byte integer");
            return 1;
        }

        // multiplier = 1 || 128 || 128*128 || 128*128*128
        multiplier = multiplier * 128;
	}

    return 0;
}