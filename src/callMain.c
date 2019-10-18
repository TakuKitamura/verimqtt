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
    char *fname = "packet_example.bin";
    uint8_t request[255];
    uint32_t  i;
    fpos_t fsize = 0;
    uint32_t tcp_payload;

    fp = fopen(fname, "rb");

    fseek(fp, 0, SEEK_END);
    fgetpos(fp, &fsize);

    tcp_payload = fsize;

    fp = fopen(fname, "rb");

    fread(request, sizeof(uint8_t), tcp_payload, fp);
    fclose(fp);
    
    struct_fixed_header data = parse(request, tcp_payload);

    // printf("message_name=%s\n", data.message_name);
    printf("message_flag=%04x\n", data.message_type);
    printf("dup_flag=%01x\n", data.dup_flag);
    printf("qos_flag=%02x\n", data.qos_flag);
    printf("retain_flag=%01x\n", data.retain_flag);
    printf("remaining_length=%u\n", data.remaining_length);
    // printf("err_msg=%s\n", data.err_msg);
    return 0;
}
