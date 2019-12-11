#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "Main.h"

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "%s [file_path]\n", argv[0]);
        exit(EXIT_FAILURE);
    }
    FILE *fp;
    char *file_name = argv[1];
    uint8_t *request;
    uint32_t  i;
    fpos_t fsize = 0;
    uint32_t packet_size;

    fp = fopen(file_name, "rb");

    if (fp == NULL) {
        fprintf(stderr, "%s open error.\n", file_name);
        exit(EXIT_FAILURE);
    }

    fseek(fp, 0, SEEK_END);
    if (fgetpos(fp, &fsize) != 0) {
        fprintf(stderr, "fgetpos error.\n");
        exit(EXIT_FAILURE);
    }
    fseek(fp, 0L, SEEK_SET);

    packet_size = fsize;

    request = (uint8_t*)malloc(sizeof(uint8_t) * (packet_size + 1));
    if(request == NULL) {
        fprintf(stderr, "malloc error.\n");
        exit(EXIT_FAILURE);
    }

    fread(request, sizeof(uint8_t), packet_size, fp);
    if (fclose(fp) == EOF) {
        fprintf(stderr, "fclose error.\n");
        exit(EXIT_FAILURE);
    }

    // parse関数が定理証明済み
    clock_t start,end;
    start = clock();
    struct_fixed_header data = mqtt_packet_parse(request, packet_size);
    end = clock();
    double time = (double)(end-start)/CLOCKS_PER_SEC;
    printf("packet_size=%u, time=%.8fs\n",packet_size, time);
    free(request);
    exit(EXIT_SUCCESS);
}
