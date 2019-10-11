#include <stdio.h>
#include <stdlib.h>

#include "Main.h"

int main(int argc, char *argv[]) {
    FILE *fp;
    char *fname = "publishMessagePacket.bin";
    uint8_t request[10000];
    uint32_t  i;
    uint32_t size;

    fp = fopen( fname, "rb" );
    if( fp == NULL ){
    printf( "%sファイルが開けません", fname );
    return -1;
    }

    size = fread( request, sizeof( unsigned char ), 10000, fp );
    fclose(fp);
    // for(i=0; i<size; i++ ){
    //     printf("%02x\n", request[i]);
    // }
    
    parse(request, size);
    return 0;
}
