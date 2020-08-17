import json
import copy
import pprint
def err(message):
  print(message)
  exit(1)

file_path = '../../out/Const.h'

parsed_typedef_structs = {}
with open(file_path) as f:
  find_typedef = False
  find_left_brace = False
  find_right_brace = False
  struct_end = False
  data_contents = [] # {}のデータ名とデータタイプ

  for line in f:
    stripped_line = line.strip()
    if (stripped_line.startswith('typedef struct ')):
      if (find_typedef == False and
          find_left_brace == False and
          find_right_brace == False and
          struct_end == False):
        find_typedef = True
      else:
        err('parse err')
    elif (stripped_line.startswith('{')):
      if (find_typedef == True and
          find_left_brace == False and
          find_right_brace == False and
          struct_end == False):
        find_left_brace = True
      else:
        err('parse err')
    elif (stripped_line.startswith('}')):
      if (find_typedef == True and
          find_left_brace == True and
          find_right_brace == False and
          struct_end == False):
          find_right_brace = True
      else:
        err('parse err')
    else:
      if (find_typedef == True and # {}内のテキスト
          find_left_brace == True and
          find_right_brace == False and 
          struct_end == False):
        stripped_line = stripped_line.replace(';', '') # ; 削除
        data_contents.append(stripped_line)
      elif (find_typedef == True and # typedef struct の別名の場合
          find_left_brace == True and
          find_right_brace == True and
          struct_end == False):
        typedef_struct_name = stripped_line.replace(';', '')
        struct_end = True 
        parsed_typedef_structs[typedef_struct_name] = {}
        for data in data_contents:
          asterisk_count = data.count('*')
          splitted_line = data.split(' ')
          data_type = (splitted_line[0] + ('*' * asterisk_count)).replace('C_String_t', 'const char*')
          data_name = splitted_line[1].replace('*', '')
          if data_name in ['utf8_next_start_index', 'binary_next_start_index', 'payload_start_index', 'user_name_or_password_next_start_index', '']:
            continue
          parsed_typedef_structs[typedef_struct_name][data_name] = data_type
        data_contents = []

    if (find_typedef == True and
        find_left_brace == True and
        find_right_brace == True and
        struct_end == True):
      find_typedef = False
      find_left_brace = False
      find_right_brace = False 
      struct_end = False

def explore_parsed_typedef_structs (explore_target, origin_structs):
  explored = {} # return が 空のままの場合探索するものはない
  for data_name in explore_target:
    data_type = explore_target[data_name]
    if (data_type in origin_structs.keys()):
      explored[data_name] = explore_parsed_typedef_structs(origin_structs[data_type], origin_structs)
    else:
      explored[data_name] = explore_target[data_name]
  return explored

# pprint.pprint(parsed_typedef_structs)
origin_structs = copy.deepcopy(parsed_typedef_structs)
extentioned_structs = {}
for struct_name in origin_structs:
  explore_target = origin_structs[struct_name]
  explored = explore_parsed_typedef_structs(explore_target, origin_structs)
  extentioned_structs[struct_name] = explored
  
structs_data_map_json = json.dumps(extentioned_structs)
print(structs_data_map_json)

