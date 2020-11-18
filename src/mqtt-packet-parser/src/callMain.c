#include <stdio.h>
#include <stdlib.h>

#include "Main.h"

long long int getFileSize(const char* fileName)
{
    FILE* fp = fopen(fileName, "rb");
    if (fp == NULL) {
        return -1LL;
    }

    long long int count = 0LL;
    for (;;) {
        if (fgetc(fp) == EOF) {
            if (feof(fp)) {
                break;
            }
            else if (ferror(fp)) {
                fclose(fp);
                return -1LL;
            }
            else {
                // EOF と同じ値をもつ有効な文字
            }
        }
        ++count;
    }

    fclose(fp);
    return count;
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "%s [file_path]\n", argv[0]);
        exit(EXIT_FAILURE);
    }
    FILE *fp;
    char *file_name = argv[1];
    uint8_t *request;

    fp = fopen(file_name, "rb");

    if (fp == NULL) {
        fprintf(stderr, "%s open error.\n", file_name);
        exit(EXIT_FAILURE);
    }

    long long int packet_size = getFileSize(file_name);

    request = (uint8_t*)malloc(sizeof(uint8_t) * (packet_size));
    if(request == NULL) {
        fprintf(stderr, "malloc error.\n");
        exit(EXIT_FAILURE);
    }

    size_t read_count = fread(request, sizeof(uint8_t), packet_size, fp);
    if (fclose(fp) == EOF) {
        fprintf(stderr, "fclose error.\n");
        exit(EXIT_FAILURE);
    }

    kremlinit_globals();
    parse_result data = mqtt_packet_parse(request, packet_size);

    printf("data.message_type = 0x%02x\n", data.message_type);
    printf("data.message_name = %s\n", data.message_name);
    printf("data.flags.flag = 0x%02x\n", data.flags.flag);
    printf("data.flags.dup_flag = 0x%02x\n", data.flags.dup_flag);
    printf("data.flags.qos_flag = 0x%02x\n", data.flags.qos_flag);
    printf("data.flags.retain_flag = 0x%02x\n", data.flags.retain_flag);
    printf("data.remaining_length = %u\n", data.remaining_length);

    puts("");

    if (data.message_type == 1) {
        printf("data.connect.protocol_name = %s\n", data.connect.protocol_name);
        printf("data.connect.protocol_version = %u\n", data.connect.protocol_version);
        printf("data.connect.flags.connect_flag = 0x%02x\n", data.connect.flags.connect_flag);
        printf("data.connect.flags.user_name = 0x%02x\n", data.connect.flags.user_name);
        printf("data.connect.flags.password = 0x%02x\n", data.connect.flags.password);
        printf("data.connect.flags.will_retain = 0x%02x\n", data.connect.flags.will_retain);
        printf("data.connect.flags.will_qos = 0x%02x\n", data.connect.flags.will_qos);
        printf("data.connect.flags.will_flag = 0x%02x\n", data.connect.flags.will_flag);
        printf("data.connect.flags.clean_start = 0x%02x\n", data.connect.flags.clean_start);
        printf("data.connect.keep_alive = 0x%02x\n", data.connect.keep_alive);

        if (data.connect.connect_id.utf8_string_status_code == 0) {
            printf("data.connect.connect_id.utf8_string_length = %u\n", data.connect.connect_id.utf8_string_length);
            printf("data.connect.connect_id.utf8_string_value = \n [");
            if (data.connect.connect_id.utf8_string_length > 0) {
                for (int i=0; i < data.connect.connect_id.utf8_string_length; i++) {
                    printf("0x%02X", data.connect.connect_id.utf8_string_value[i] & 0x000000FF);
                    if (i + 1 == data.connect.connect_id.utf8_string_length) 
                        puts("]");
                    else
                        printf(", ");
                }
            } else {
                puts("]");
            }

        }


        if (data.connect.will.connect_will_topic_name.utf8_string_status_code == 0) {
            if (data.connect.will.connect_will_property.property_id != 255) {
                if (data.connect.will.connect_will_property.property_type_struct.property_type_error.property_error_code == 0) {
                    printf("data.property.payload_start_index = %u\n", data.connect.will.connect_will_property.payload_start_index);
                    printf("data.connect.will.connect_will_property.property_id = %u\n", data.connect.will.connect_will_property.property_id);
                    printf("data.connect.will.connect_will_property.property_type_id = %u\n", data.connect.will.connect_will_property.property_type_id);

                    if (data.connect.will.connect_will_property.property_type_id == 1) {
                        printf("data.connect.will.connect_will_property.property_type_struct.one_byte_integer_struct.one_byte_integer_value = %u\n", data.connect.will.connect_will_property.property_type_struct.one_byte_integer_struct);
                    } else if (data.connect.will.connect_will_property.property_type_id == 2) {
                        printf("data.connect.will.connect_will_property.property_type_struct.two_byte_integer_struct.two_byte_integer_value = %u\n", data.connect.will.connect_will_property.property_type_struct.two_byte_integer_struct);           
                    } else if (data.connect.will.connect_will_property.property_type_id == 3) {
                        printf("data.connect.will.connect_will_property.property_type_struct.four_byte_integer_struct.four_byte_integer_value = %u\n", data.connect.will.connect_will_property.property_type_struct.four_byte_integer_struct);  
                    } else if (data.connect.will.connect_will_property.property_type_id == 4) {
                        printf("data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_length = %u\n", data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_length);
                        printf("data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_value = \n [");
                        for (int i=0; i < data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_length; i++) {
                            printf("0x%02X", data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_value[i] & 0x000000FF);
                            if (i + 1 == data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_length) 
                                puts("]");
                            else
                                printf(", ");
                        }
                    } else if (data.connect.will.connect_will_property.property_type_id == 5) {
                        printf("data.connect.will.connect_will_property.property_type_struct.variable_byte_integer_struct.variable_integer_value = %u\n", data.connect.will.connect_will_property.property_type_struct.variable_byte_integer_struct);  
                    } else if (data.connect.will.connect_will_property.property_type_id == 6) {
                        printf("data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_length = %u\n", data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_length);
                        printf("data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_value = \n [");
                        for (int i=0; i < data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_length; i++) {
                            printf("0x%02X", data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_value[i] & 0x000000FF);
                            if (i + 1 == data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_length) 
                                puts("]");
                            else
                                printf(", ");
                        }
                    } else if (data.connect.will.connect_will_property.property_type_id == 7) {
                        printf("data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length = %u\n", data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length);
                        printf("data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value = \n [");
                        for (int i=0; i < data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length; i++) {
                            printf("0x%02X", data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value[i] & 0x000000FF);
                            if (i + 1 == data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length) 
                                puts("]");
                            else
                                printf(", ");
                        }

                        printf("data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length = %u\n", data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length);
                        printf("data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value = \n [");
                        for (int i=0; i < data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length; i++) {
                            printf("0x%02X", data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value[i] & 0x000000FF);
                            if (i + 1 == data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length) 
                                puts("]");
                            else
                                printf(", ");
                        }
                        

                    }
                    puts("");
                } else {
                    // puts("property error");
                    printf("property error code = %u\n", data.connect.will.connect_will_property.property_type_struct.property_type_error.property_error_code);
                    printf("property error code name = %s\n", data.connect.will.connect_will_property.property_type_struct.property_type_error.property_error_code_name);
                }
            } else {
                puts("property type id is invalid");
            }

            printf("data.connect.will.connect_will_topic_name.utf8_string_length = %u\n", data.connect.will.connect_will_topic_name.utf8_string_length);
            printf("data.connect.will.connect_will_topic_name.utf8_string_value = \n [");
            if (data.connect.will.connect_will_topic_name.utf8_string_length > 0) {
                for (int i=0; i < data.connect.will.connect_will_topic_name.utf8_string_length; i++) {
                    printf("0x%02X", data.connect.will.connect_will_topic_name.utf8_string_value[i] & 0x000000FF);
                    if (i + 1 == data.connect.will.connect_will_topic_name.utf8_string_length) 
                        puts("]");
                    else
                        printf(", ");
                }
            } else {
                puts("]");
            }

            printf("data.connect.will.connect_will_payload.binary_length = %u\n", data.connect.will.connect_will_payload.binary_length);
            printf("data.connect.will.connect_will_payload.binary_value = \n [");
            for (int i=0; i < data.connect.will.connect_will_payload.binary_length; i++) {
                printf("0x%02X", data.connect.will.connect_will_payload.binary_value[i] & 0x000000FF);
                if (i + 1 == data.connect.will.connect_will_payload.binary_length) 
                    puts("]");
                else
                    printf(", ");
            }

            puts("");            
        }

        puts("");

        if (data.connect.user_name.utf8_string_status_code == 0) {
            printf("data.connect.user_name.utf8_string_length = %u\n", data.connect.user_name.utf8_string_length);
            printf("data.connect.user_name.utf8_string_value = \n [");
            if (data.connect.user_name.utf8_string_length > 0) {
                for (int i=0; i < data.connect.user_name.utf8_string_length; i++) {
                    printf("0x%02X", data.connect.user_name.utf8_string_value[i] & 0x000000FF);
                    if (i + 1 == data.connect.user_name.utf8_string_length) 
                        puts("]");
                    else
                        printf(", ");
                }
            } else {
                puts("]");
            }
        }

        if (data.connect.password.is_valid_binary_data) {
            printf("data.connect.password.binary_length = %u\n", data.connect.password.binary_length);
            printf("data.connect.password.binary_value = \n [");
            for (int i=0; i < data.connect.password.binary_length; i++) {
                printf("0x%02X", data.connect.password.binary_value[i] & 0x000000FF);
                if (i + 1 == data.connect.password.binary_length) 
                    puts("]");
                else
                    printf(", ");
            }
        }


        puts("");
    } else if (data.message_type == 3) {

        printf("data.publish.topic_length = %u\n", data.publish.topic_length);
        printf("data.publish.topic_name =\n [");
        for (int i=0; i < data.publish.topic_length; i++) {
            printf("0x%02X", data.publish.topic_name[i] & 0x000000FF);
            if (i + 1 == data.publish.topic_length) 
                puts("]\n");
            else
                printf(", ");
        }

        if (data.flags.qos_flag > 0) {
            printf("data.publish.packet_identifier = %d\n", data.publish.packet_identifier);
        }

        printf("data.publish.payload =\n [");
        for (int i=0; i < data.publish.payload.payload_length; i++) {
            printf("0x%02X", data.publish.payload.payload_value[i] & 0x000000FF);
            if (i + 1 == data.publish.payload.payload_length) 
                puts("]");
            else
                printf(", ");
        }
        printf("data.publish.payload_length = %u\n", data.publish.payload.payload_length);

        puts("");
    } else if (data.message_type == 14) {
        printf("data.disconnect.disconnect_reason_code = 0x%02x\n", data.disconnect.disconnect_reason_code);
        printf("data.disconnect.disconnect_reason_code_name = %s\n", data.disconnect.disconnect_reason_code_name);
        puts("");
    }

    puts("");
 
    if (data.property.property_type_id != 255) {
        if (data.property.property_type_struct.property_type_error.property_error_code == 0 &&
            data.property.property_type_id != 0) {
            printf("data.property.payload_start_index = %u\n", data.property.payload_start_index);
            printf("data.property.property_id = %u\n", data.property.property_id);
            printf("data.property.property_type_id = %u\n", data.property.property_type_id);

            if (data.property.property_type_id == 1) {
                printf("data.property.property_type_struct.one_byte_integer_struct.one_byte_integer_value = %u\n", data.property.property_type_struct.one_byte_integer_struct);
            } else if (data.property.property_type_id == 2) {
                printf("data.property.property_type_struct.two_byte_integer_struct.two_byte_integer_value = %u\n", data.property.property_type_struct.two_byte_integer_struct);           
            } else if (data.property.property_type_id == 3) {
                printf("data.property.property_type_struct.four_byte_integer_struct.four_byte_integer_value = %u\n", data.property.property_type_struct.four_byte_integer_struct);  
            } else if (data.property.property_type_id == 4) {
                printf("data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_length = %u\n", data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_length);
                printf("data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_value = \n [");
                for (int i=0; i < data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_length; i++) {
                    printf("0x%02X", data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_value[i] & 0x000000FF);
                    if (i + 1 == data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_length) 
                        puts("]");
                    else
                        printf(", ");
                }
            } else if (data.property.property_type_id == 5) {
                printf("data.property.property_type_struct.variable_byte_integer_struct.variable_integer_value = %u\n", data.property.property_type_struct.variable_byte_integer_struct);  
            } else if (data.property.property_type_id == 6) {
                printf("data.property.property_type_struct.binary_data_struct.binary_length = %u\n", data.property.property_type_struct.binary_data_struct.binary_length);
                printf("data.property.property_type_struct.binary_data_struct.binary_value = \n [");
                for (int i=0; i < data.property.property_type_struct.binary_data_struct.binary_length; i++) {
                    printf("0x%02X", data.property.property_type_struct.binary_data_struct.binary_value[i] & 0x000000FF);
                    if (i + 1 == data.property.property_type_struct.binary_data_struct.binary_length) 
                        puts("]");
                    else
                        printf(", ");
                }
            } else if (data.property.property_type_id == 7) {
                printf("data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length = %u\n", data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length);
                printf("data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value = \n [");
                for (int i=0; i < data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length; i++) {
                    printf("0x%02X", data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value[i] & 0x000000FF);
                    if (i + 1 == data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length) 
                        puts("]");
                    else
                        printf(", ");
                }

                printf("data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length = %u\n", data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length);
                printf("data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value = \n [");
                for (int i=0; i < data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length; i++) {
                    printf("0x%02X", data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value[i] & 0x000000FF);
                    if (i + 1 == data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length) 
                        puts("]");
                    else
                        printf(", ");
                }
                

            }
            puts("");
        } else {
            // puts("property error");
            printf("property error code = %u\n", data.property.property_type_struct.property_type_error.property_error_code);
            printf("property error code name = %s\n", data.property.property_type_struct.property_type_error.property_error_code_name);
        }
    } else {
        puts("property type id is invalid");
    }

    printf("data.error.code=%u\n", data.error.code);
    printf("data.error.message=%s\n", data.error.message);
    free(request);
    exit(EXIT_SUCCESS);
}
