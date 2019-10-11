#include <stdio.h>
#include <stdlib.h>

#include "Main.h"

// typedef struct Data
// {
//   uint8_t r;
//   uint8_t g;
//   uint8_t b;
// }
// data_s;

int main(int argc, char *argv[]) {
    FILE *fp;
    char *fname = "publishMessagePacket.bin";
    uint8_t request[10000];
    uint32_t  i;
    uint32_t size;
    // data_struct data;

    fp = fopen(fname, "rb");
    if( fp == NULL ){
        printf("%sファイルが開けません", fname);
        return 1;
    }

    size = fread( request, sizeof( unsigned char ), 10000, fp );
    fclose(fp);
    
    data_struct data = parse(request, size);

    printf("r=%uy\n", data.r);
    return 0;
}
