from gron import gron
import flated_master
import sys
from distutils.util import strtobool
import ast

def err(message):
  print(message)
  exit(1)

argv = sys.argv

typedef_struct_json = flated_master.get_typedef_struct_json('../../../out/Const.h')
flated_master_list = gron(typedef_struct_json)
params_type_dict = {}
for line in flated_master_list:
  splited_line = line.split(' = ')
  params_name, params_data_type = splited_line[0], splited_line[1].replace('"', '')
  params_type_dict[params_name] = params_data_type

if (len(argv) == 2 and argv[1] == 'template'):

  params_template = []
  # '文字 #' を使うときは気をつける
  for _, (params_name, params_data_type) in enumerate(params_type_dict.items()):
    if params_data_type == 'uint8_t':
      params_template.append('{} = {} // {}'.format(params_name, 0, 'type:{}, max_u8:255'.format(params_data_type)))
    elif params_data_type == 'uint16_t':
      params_template.append('{} = {} // {}'.format(params_name, 0, 'type:{}, max_u16:65535'.format(params_data_type)))
    elif params_data_type == 'uint32_t':
      params_template.append('{} = {} // {}'.format(params_name, 0, 'type:{}, max_u32:4294967295'.format(params_data_type)))
    elif params_data_type == 'uint8_t*':
      params_template.append('{} = "{}" // {}'.format(params_name, 'hello', 'type:{}, can use uint8_array'.format(params_data_type)))
    elif params_data_type == 'const char*':
      params_template.append('{} = "{}" // {}'.format(params_name, 'hello', 'type:{}, can use uint8_array'.format(params_data_type)))
    elif params_data_type == 'bool':
      params_template.append('{} = {} // {}'.format(params_name, 'false', 'type:{}'.format(params_data_type)))
    else:
      err('unkown data type: ' + params_data_type)

  for line in params_template:
    print(line)
else:
  params_value_dict = {'uint8_t': {}, 'uint16_t': {}, 'uint32_t': {}, 'uint8_t*': {}, 'const char*': {}, 'bool': {}}
  with open('./template.txt') as f:
    for i, line in enumerate(f.readlines()):
      if line == '\n':
        continue
      splited_comment = line.strip().rsplit(' // ')
      splited_equal = splited_comment[0].split(' = ')
      params_name, params_value = splited_equal[0], splited_equal[1]
      params_data_type = params_type_dict[params_name]

      if params_data_type == 'uint8_t':
        if (int(params_value) < 0 or int(params_value) > 0xff):
          err('line: {}, param: {}, invalid {}'.format(i+1, params_name, params_data_type))
        params_value_dict[params_data_type][params_name] = int(params_value)
      elif params_data_type == 'uint16_t':
        if (int(params_value) < 0 or int(params_value) > 0xffff):
          err('line: {}, param: {}, invalid {}'.format(i+1, params_name, params_data_type))
        params_value_dict[params_data_type][params_name] = int(params_value)
      elif params_data_type == 'uint32_t':
        if (int(params_value) < 0 or int(params_value) > 0xffffffff):
          err('line: {}, param: {}, invalid {}'.format(i+1, params_name, params_data_type))
        params_value_dict[params_data_type][params_name] = int(params_value)
      elif params_data_type == 'uint8_t*' or params_data_type == 'const char*':
        params_value = params_value[1:-1]
        try:
          v = tuple(ast.literal_eval(params_value))
          print(v)
        except:
          try:
            v = [ord(c) for c in params_value]
          except:
            err('line: {}, param: {}, invalid {}'.format(i+1, params_name, params_data_type))
        for list_v in v:
          if list_v < 0 or list_v > 0xff:
            err('line: {}, param: {}, invalid {}'.format(i+1, params_name, params_data_type))
        params_value_dict[params_data_type][params_name] = tuple(v)
      elif params_data_type == 'bool':
        try:
          strtobool(params_value)
        except:
          err('line: {}, param: {}, invalid {}'.format(i+1, params_name, params_data_type))
        params_value_dict[params_data_type][params_name] = strtobool(params_value) == True
      else:
        print('unkown data type:', params_data_type)
        exit(1)      
  # print(params_value_dict)
  gen_test_code = ''
  for data_type, values in params_value_dict.items():
      if data_type == 'uint8_t':
        for result, expect in values.items():
          gen_test_code += '    Testing_eq_u8("{}", {}, data.{});\n'.format(result, expect, result)
      elif data_type == 'uint16_t':
        for result, expect in values.items():
          gen_test_code += '    Testing_eq_u16("{}", {}, data.{});\n'.format(result, expect, result)
      elif data_type == 'uint32_t':
        for result, expect in values.items():
          gen_test_code += '    Testing_eq_u32("{}", {}, data.{});\n'.format(result, expect, result)
      elif data_type == 'uint8_t*' or data_type == 'const char*':
        # pass
        for result, expect in values.items():
          gen_test_code += '    Testing_eq_u8_array("{}", "{}", {}, (C_String_t)data.{});\n'.format(result, ''.join(chr(i) for i in expect), len(expect), result)
    
      elif data_type == 'bool':
        for result, expect in values.items():
          gen_test_code += '    Testing_eq_bool("{}", {}, data.{});\n'.format(result, str(expect).lower(), result)
      else:
        print('unkown data type:', params_data_type)
        exit(1)  
  # print(gen_test_code)
  template_c = \
"""
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <string.h>
#include <limits.h>

#include "Main.h"

static unsigned int total = 0;
static unsigned int pass = 0;

void Testing_test_start(C_String_t title) {{
  printf("  \\x1b[36m[%s]\\x1b[0m\\n", title);
}}

void Testing_test_end() {{
  if (total != pass) {{
    printf("  \\x1b[35mSOME TESTS FAILED (%u/%u) (PASS/TOTAL)\\x1b[0m\\n", pass, total);
  }} else {{
    puts("  \\x1b[32mALL TESTS PASSED\\x1b[0m\\n");
  }}
}}

void test_static(bool is_pass) {{
  total++;
  if (total == UINT_MAX) {{
    puts("test-code has so many tests.");
    exit(1);
  }}

  if (is_pass == true) {{
    pass++;
  }}
}}

#define MK_CHECK(n)\\
  void Testing_eq_i##n(C_String_t title, int##n##_t expect, int##n##_t result) {{\\
    bool is_pass = (expect == result);\\
    test_static(is_pass);\\
    if (is_pass) {{\\
    }} else {{\\
          printf("\\x1b[31m✘\\x1b[0m %s\\n\\t expected is %" PRId##n " but result is %" PRId##n "\\n", title, expect, result);\\
    }}\\
  }}
MK_CHECK(8)
MK_CHECK(16)
MK_CHECK(32)
MK_CHECK(64)

#define MK_UCHECK(n)\\
  void Testing_eq_u##n(C_String_t title, uint##n##_t expect, uint##n##_t result) {{\\
    bool is_pass = (expect == result);\\
    test_static(is_pass);\\
    if (is_pass) {{\\
    }} else {{\\
          printf("\\x1b[31m✘\\x1b[0m %s\\n\\t expected is %" PRIu##n " but result is %" PRIu##n "\\n", title, expect, result);\\
    }}\\
  }}
MK_UCHECK(8)
MK_UCHECK(16)
MK_UCHECK(32)
MK_UCHECK(64)

void Testing_eq_bool(C_String_t title, bool expect, bool result) {{
  bool is_pass = (expect == result);
  test_static(is_pass);
  if (is_pass) {{
  }} else {{
    printf("\\x1b[31m✘\\x1b[0m %s\\n\\t expected is true but result is false\\n", title);
  }}
}}

void Testing_eq_str(C_String_t title, C_String_t expect, C_String_t result) {{
  bool is_pass = (strcmp(expect, result) == 0);
  test_static(is_pass);
  if (is_pass) {{
  }} else {{
    printf("\\x1b[31m✘\\x1b[0m %s\\n\\t expected is \\'%s\\' but result is \\'%s\\'\\n", title, expect, result);
  }}
}}

void Testing_eq_u8_array(C_String_t title, C_String_t expect, uint32_t expect_length, C_String_t result) {{
  for(uint32_t i = 0; i <= expect_length; i++) {{
      if(expect[i] != result[i]) {{
          printf("\\x1b[31m✘\\x1b[0m %s\\n\\t expected is \\'%s\\' but result is '", title, expect);
          for(uint32_t i = 0; i <= expect_length; i++) {{
            printf("%c",result[i] & 0x000000FF);
          }}
          puts("'");
          test_static(false);
          return;
      }}
  }}

  test_static(true);
  return;
}}

long long int getFileSize(const char* fileName)
{{
    FILE* fp = fopen(fileName, "rb");
    if (fp == NULL) {{
        return -1LL;
    }}

    long long int count = 0LL;
    for (;;) {{
        if (fgetc(fp) == EOF) {{
            if (feof(fp)) {{
                break;
            }}
            else if (ferror(fp)) {{
                fclose(fp);
                return -1LL;
            }}
            else {{
                // EOF と同じ値をもつ有効な文字
            }}
        }}
        ++count;
    }}

    fclose(fp);
    return count;
}}

int main(int argc, char *argv[]) {{
    FILE *fp;
    char *file_name = "{}";
    uint8_t *request;

    fp = fopen(file_name, "rb");

    if (fp == NULL) {{
        fprintf(stderr, "%s open error.\\n", file_name);
        exit(EXIT_FAILURE);
    }}

    long long int packet_size = getFileSize(file_name);

    request = (uint8_t*)malloc(sizeof(uint8_t) * (packet_size));
    if(request == NULL) {{
        fprintf(stderr, "malloc error.\\n");
        exit(EXIT_FAILURE);
    }}

    size_t read_count = fread(request, sizeof(uint8_t), packet_size, fp);
    if (fclose(fp) == EOF) {{
        fprintf(stderr, "fclose error.\\n");
        exit(EXIT_FAILURE);
    }}

    kremlinit_globals();
    struct_fixed_header data = mqtt_packet_parse(request, packet_size);
    free(request);
    Testing_test_start("{}");
{}
    Testing_test_end();

    return 0;
}}
"""
  write_c = template_c.format('/root/verimqtt/src/mqtt-packet-parser/bin/publish/normal_publish/normal_publish.bin', 'SAMPLE TEST', gen_test_code)
  print(write_c)