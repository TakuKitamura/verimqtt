from gron import gron
import flated_master
import sys
from distutils.util import strtobool
import ast
import os
import sys

def err(message):
  print(message, file=sys.stderr)
  exit(1)

argv = sys.argv

typedef_struct_json = flated_master.get_typedef_struct_json('../out/Const.h')
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
elif (len(argv) == 3 and argv[1] == 'generate'):
  params_value_dict = {'uint8_t': {}, 'uint16_t': {}, 'uint32_t': {}, 'uint8_t*': {}, 'const char*': {}, 'bool': {}}
  file_path = os.path.abspath(argv[2])
  with open(file_path.replace('.bin', '.template')) as f:
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
        err('unkown data type:' + params_data_type)
        exit(1)      
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
        err('unkown data type:' + params_data_type)
        exit(1)  
  with open('test/gen_test/test_c.template') as f:
    template_c = f.read()
    write_c = template_c.format(file_path, '{} TEST'.format(file_path), gen_test_code)
    print(write_c)
else:
  err("python3 main.py (template, generate) ...")