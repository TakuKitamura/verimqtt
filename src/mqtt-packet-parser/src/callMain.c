
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <string.h>
#include <limits.h>

#include "Main.h"

static unsigned int total = 0;
static unsigned int pass = 0;

void Testing_test_start(C_String_t title) {
  printf("  \x1b[36m[%s]\x1b[0m\n", title);
}

void Testing_test_end() {
  if (total != pass) {
    printf("  \x1b[35mSOME TESTS FAILED (%u/%u) (PASS/TOTAL)\x1b[0m\n", pass, total);
  } else {
    puts("  \x1b[32mALL TESTS PASSED\x1b[0m\n");
  }
}

void test_static(bool is_pass) {
  total++;
  if (total == UINT_MAX) {
    puts("test-code has so many tests.");
    exit(1);
  }

  if (is_pass == true) {
    pass++;
  }
}

#define MK_CHECK(n)\
  void Testing_eq_i##n(C_String_t title, int##n##_t expect, int##n##_t result) {\
    bool is_pass = (expect == result);\
    test_static(is_pass);\
    if (is_pass) {\
    } else {\
          printf("\x1b[31m✘\x1b[0m %s\n\t expected is %" PRId##n " but result is %" PRId##n "\n", title, expect, result);\
    }\
  }
MK_CHECK(8)
MK_CHECK(16)
MK_CHECK(32)
MK_CHECK(64)

#define MK_UCHECK(n)\
  void Testing_eq_u##n(C_String_t title, uint##n##_t expect, uint##n##_t result) {\
    bool is_pass = (expect == result);\
    test_static(is_pass);\
    if (is_pass) {\
    } else {\
          printf("\x1b[31m✘\x1b[0m %s\n\t expected is %" PRIu##n " but result is %" PRIu##n "\n", title, expect, result);\
    }\
  }
MK_UCHECK(8)
MK_UCHECK(16)
MK_UCHECK(32)
MK_UCHECK(64)

void Testing_eq_bool(C_String_t title, bool expect, bool result) {
  bool is_pass = (expect == result);
  test_static(is_pass);
  if (is_pass) {
  } else {
    printf("\x1b[31m✘\x1b[0m %s\n\t expected is true but result is false\n", title);
  }
}

void Testing_eq_str(C_String_t title, C_String_t expect, C_String_t result) {
  bool is_pass = (strcmp(expect, result) == 0);
  test_static(is_pass);
  if (is_pass) {
  } else {
    printf("\x1b[31m✘\x1b[0m %s\n\t expected is \'%s\' but result is \'%s\'\n", title, expect, result);
  }
}

void Testing_eq_u8_array(C_String_t title, C_String_t expect, uint32_t expect_length, C_String_t result) {
  for(uint32_t i = 0; i <= expect_length; i++) {
      if(expect[i] != result[i]) {
          printf("\x1b[31m✘\x1b[0m %s\n\t expected is \'%s\' but result is '", title, expect);
          for(uint32_t i = 0; i <= expect_length; i++) {
            printf("%c",result[i] & 0x000000FF);
          }
          puts("'");
          test_static(false);
          return;
      }
  }

  test_static(true);
  return;
}

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
    FILE *fp;
    char *file_name = "/root/verimqtt/src/mqtt-packet-parser/bin/publish/normal_publish/normal_publish.bin";
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
    struct_fixed_header data = mqtt_packet_parse(request, packet_size);
    free(request);
    Testing_test_start("SAMPLE TEST");
    Testing_eq_u8("connect.connect_id.utf8_string_status_code", 0, data.connect.connect_id.utf8_string_status_code);
    Testing_eq_u8("connect.flags.clean_start", 0, data.connect.flags.clean_start);
    Testing_eq_u8("connect.flags.connect_flag", 0, data.connect.flags.connect_flag);
    Testing_eq_u8("connect.flags.password", 0, data.connect.flags.password);
    Testing_eq_u8("connect.flags.user_name", 0, data.connect.flags.user_name);
    Testing_eq_u8("connect.flags.will_flag", 0, data.connect.flags.will_flag);
    Testing_eq_u8("connect.flags.will_qos", 0, data.connect.flags.will_qos);
    Testing_eq_u8("connect.flags.will_retain", 0, data.connect.flags.will_retain);
    Testing_eq_u8("connect.protocol_version", 0, data.connect.protocol_version);
    Testing_eq_u8("connect.user_name.utf8_string_status_code", 0, data.connect.user_name.utf8_string_status_code);
    Testing_eq_u8("connect.will.connect_will_property.property_id", 0, data.connect.will.connect_will_property.property_id);
    Testing_eq_u8("connect.will.connect_will_property.property_type_id", 0, data.connect.will.connect_will_property.property_type_id);
    Testing_eq_u8("connect.will.connect_will_property.property_type_struct.one_byte_integer_struct", 0, data.connect.will.connect_will_property.property_type_struct.one_byte_integer_struct);
    Testing_eq_u8("connect.will.connect_will_property.property_type_struct.property_type_error.property_error_code", 0, data.connect.will.connect_will_property.property_type_struct.property_type_error.property_error_code);
    Testing_eq_u8("connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_status_code", 0, data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_status_code);
    Testing_eq_u8("connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code", 0, data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code);
    Testing_eq_u8("connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code", 0, data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code);
    Testing_eq_u8("connect.will.connect_will_topic_name.utf8_string_status_code", 0, data.connect.will.connect_will_topic_name.utf8_string_status_code);
    Testing_eq_u8("disconnect.disconnect_reason_code", 0, data.disconnect.disconnect_reason_code);
    Testing_eq_u8("error.code", 0, data.error.code);
    Testing_eq_u8("flags.dup_flag", 0, data.flags.dup_flag);
    Testing_eq_u8("flags.flag", 0, data.flags.flag);
    Testing_eq_u8("flags.qos_flag", 0, data.flags.qos_flag);
    Testing_eq_u8("flags.retain_flag", 0, data.flags.retain_flag);
    Testing_eq_u8("message_type", 0, data.message_type);
    Testing_eq_u8("property.property_id", 0, data.property.property_id);
    Testing_eq_u8("property.property_type_id", 0, data.property.property_type_id);
    Testing_eq_u8("property.property_type_struct.one_byte_integer_struct", 0, data.property.property_type_struct.one_byte_integer_struct);
    Testing_eq_u8("property.property_type_struct.property_type_error.property_error_code", 0, data.property.property_type_struct.property_type_error.property_error_code);
    Testing_eq_u8("property.property_type_struct.utf8_encoded_string_struct.utf8_string_status_code", 0, data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_status_code);
    Testing_eq_u8("property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code", 0, data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_status_code);
    Testing_eq_u8("property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code", 0, data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_status_code);
    Testing_eq_u16("connect.connect_id.utf8_string_length", 0, data.connect.connect_id.utf8_string_length);
    Testing_eq_u16("connect.keep_alive", 0, data.connect.keep_alive);
    Testing_eq_u16("connect.password.binary_length", 0, data.connect.password.binary_length);
    Testing_eq_u16("connect.user_name.utf8_string_length", 0, data.connect.user_name.utf8_string_length);
    Testing_eq_u16("connect.will.connect_will_payload.binary_length", 0, data.connect.will.connect_will_payload.binary_length);
    Testing_eq_u16("connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_length", 0, data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_length);
    Testing_eq_u16("connect.will.connect_will_property.property_type_struct.two_byte_integer_struct", 0, data.connect.will.connect_will_property.property_type_struct.two_byte_integer_struct);
    Testing_eq_u16("connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_length", 0, data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_length);
    Testing_eq_u16("connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length", 0, data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length);
    Testing_eq_u16("connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length", 0, data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length);
    Testing_eq_u16("connect.will.connect_will_topic_name.utf8_string_length", 0, data.connect.will.connect_will_topic_name.utf8_string_length);
    Testing_eq_u16("property.property_type_struct.binary_data_struct.binary_length", 0, data.property.property_type_struct.binary_data_struct.binary_length);
    Testing_eq_u16("property.property_type_struct.two_byte_integer_struct", 0, data.property.property_type_struct.two_byte_integer_struct);
    Testing_eq_u16("property.property_type_struct.utf8_encoded_string_struct.utf8_string_length", 0, data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_length);
    Testing_eq_u16("property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length", 0, data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length);
    Testing_eq_u16("property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length", 0, data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length);
    Testing_eq_u16("publish.packet_identifier", 0, data.publish.packet_identifier);
    Testing_eq_u32("connect.will.connect_will_property.property_type_struct.four_byte_integer_struct", 0, data.connect.will.connect_will_property.property_type_struct.four_byte_integer_struct);
    Testing_eq_u32("connect.will.connect_will_property.property_type_struct.variable_byte_integer_struct", 0, data.connect.will.connect_will_property.property_type_struct.variable_byte_integer_struct);
    Testing_eq_u32("property.property_type_struct.four_byte_integer_struct", 0, data.property.property_type_struct.four_byte_integer_struct);
    Testing_eq_u32("property.property_type_struct.variable_byte_integer_struct", 0, data.property.property_type_struct.variable_byte_integer_struct);
    Testing_eq_u32("publish.payload.payload_length", 0, data.publish.payload.payload_length);
    Testing_eq_u32("publish.topic_length", 0, data.publish.topic_length);
    Testing_eq_u32("remaining_length", 0, data.remaining_length);
    Testing_eq_u8_array("connect.connect_id.utf8_string_value", "hello", 5, (C_String_t)data.connect.connect_id.utf8_string_value);
    Testing_eq_u8_array("connect.password.binary_value", "hello", 5, (C_String_t)data.connect.password.binary_value);
    Testing_eq_u8_array("connect.user_name.utf8_string_value", "hello", 5, (C_String_t)data.connect.user_name.utf8_string_value);
    Testing_eq_u8_array("connect.will.connect_will_payload.binary_value", "hello", 5, (C_String_t)data.connect.will.connect_will_payload.binary_value);
    Testing_eq_u8_array("connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_value", "hello", 5, (C_String_t)data.connect.will.connect_will_property.property_type_struct.binary_data_struct.binary_value);
    Testing_eq_u8_array("connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_value", "hello", 5, (C_String_t)data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_value);
    Testing_eq_u8_array("connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value", "hello", 5, (C_String_t)data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value);
    Testing_eq_u8_array("connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value", "hello", 5, (C_String_t)data.connect.will.connect_will_property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value);
    Testing_eq_u8_array("connect.will.connect_will_topic_name.utf8_string_value", "hello", 5, (C_String_t)data.connect.will.connect_will_topic_name.utf8_string_value);
    Testing_eq_u8_array("property.property_type_struct.binary_data_struct.binary_value", "hello", 5, (C_String_t)data.property.property_type_struct.binary_data_struct.binary_value);
    Testing_eq_u8_array("property.property_type_struct.utf8_encoded_string_struct.utf8_string_value", "hello", 5, (C_String_t)data.property.property_type_struct.utf8_encoded_string_struct.utf8_string_value);
    Testing_eq_u8_array("property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value", "hello", 5, (C_String_t)data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value);
    Testing_eq_u8_array("property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value", "hello", 5, (C_String_t)data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value);
    Testing_eq_u8_array("publish.payload.payload_value", "hello", 5, (C_String_t)data.publish.payload.payload_value);
    Testing_eq_u8_array("connect.protocol_name", "hello", 5, (C_String_t)data.connect.protocol_name);
    Testing_eq_u8_array("connect.will.connect_will_property.property_type_struct.property_type_error.property_error_code_name", "hello", 5, (C_String_t)data.connect.will.connect_will_property.property_type_struct.property_type_error.property_error_code_name);
    Testing_eq_u8_array("disconnect.disconnect_reason_code_name", "hello", 5, (C_String_t)data.disconnect.disconnect_reason_code_name);
    Testing_eq_u8_array("error.message", "hello", 5, (C_String_t)data.error.message);
    Testing_eq_u8_array("message_name", "hello", 5, (C_String_t)data.message_name);
    Testing_eq_u8_array("property.property_type_struct.property_type_error.property_error_code_name", "hello", 5, (C_String_t)data.property.property_type_struct.property_type_error.property_error_code_name);
    Testing_eq_u8_array("publish.topic_name", "hello", 5, (C_String_t)data.publish.topic_name);
    Testing_eq_bool("connect.password.is_valid_binary_data", false, data.connect.password.is_valid_binary_data);
    Testing_eq_bool("connect.will.connect_will_payload.is_valid_binary_data", false, data.connect.will.connect_will_payload.is_valid_binary_data);
    Testing_eq_bool("connect.will.connect_will_property.property_type_struct.binary_data_struct.is_valid_binary_data", false, data.connect.will.connect_will_property.property_type_struct.binary_data_struct.is_valid_binary_data);
    Testing_eq_bool("property.property_type_struct.binary_data_struct.is_valid_binary_data", false, data.property.property_type_struct.binary_data_struct.is_valid_binary_data);
    Testing_eq_bool("publish.payload.is_valid_payload", false, data.publish.payload.is_valid_payload);

    Testing_test_end();

    return 0;
}

