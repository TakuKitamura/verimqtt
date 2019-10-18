#include <stdio.h>
#include <stdlib.h>

#include "Main.h"

int main(int argc, char *argv[]) {
    FILE *fp;
    char *fname = "packet_example.bin";
    uint8_t *request;
    uint32_t  i;
    fpos_t fsize = 0;
    uint32_t tcp_payload;

    fp = fopen(fname, "rb");

    fseek(fp, 0, SEEK_END);
    fgetpos(fp, &fsize);
    fseek(fp, 0L, SEEK_SET);

    tcp_payload = fsize;

    request = (uint8_t*)malloc(sizeof(uint8_t) * tcp_payload);

    fread(request, sizeof(uint8_t), tcp_payload, fp);
    fclose(fp);

    // parse関数が定理証明済み
    struct_fixed_header data = parse(request, tcp_payload);
    free(request); 

    printf("message_name=%s\n", data.message_name);
    printf("message_flag=%04x\n", data.message_type);
    printf("dup_flag=%01x\n", data.dup_flag);
    printf("qos_flag=%02x\n", data.qos_flag);
    printf("retain_flag=%01x\n", data.retain_flag);
    printf("remaining_length=%u\n", data.remaining_length);
    printf("error_message=\"%s\"\n", data.error_message);
    return 0;
}
