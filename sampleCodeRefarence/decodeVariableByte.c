#include <stdio.h>

// decoding a variable byte integer 

// https://docs.oasis-open.org/mqtt/mqtt/v5.0/os/mqtt-v5.0-os.html#_Toc3901107
// 1.5.5 Variable Byte Integer

// encode(54321 base10) = (0xb1a803 base16)
int main() {
	int multiplier = 1;
	size_t value = 0;
    int i = 0;
    unsigned char data[] = {0x9c, 0x4e, 0x00, 0x00};
    int dataLen = sizeof(data)/sizeof(data[0]);
    char b, b1, b2;
    printf("%d\n", dataLen);
    for (i = 0; i < 4; i++) {
        if (i < 2) {
            if (dataLen == 1) {
                if (data[i] < 0 || data[i] > 127) {
                    puts("err1");
                    return 1;
                }
            } else {
                if (i == (dataLen - 1)) {      
                    if (data[i] < 1 || data[i] > 127) {
                        puts("err2");
                        return 1;
                    }                            
                } else {
                    if (data[i] < 128 || data[i] > 255) {
                        puts("err3");
                        return 1;
                    }                         
                }               
            }
        }
    }
    
    for(i = 0; i <= (dataLen - 1); i++) {
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