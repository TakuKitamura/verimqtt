#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
args = sys.argv

if (len(args) != 4):
    print('ex. python3 {} file_path test_title func_name'.format(args[0]))
    exit(1)

file_path = args[1]
test_title = args[2]
func_name = args[3]

file_size = 0
hex_list_str = ''
with open(file_path, "r+b") as f:
    while True:
        one_byte = f.read(1)
        if len(one_byte) == 0:
            # hex_list_str += ']'
            break
        hex_str = format(ord(one_byte), '02X')
        hex_list_str += '        request.({}ul) <- 0x{}uy;\n'.format(
            file_size, hex_str)
        file_size += 1
# request.(1ul) <- 0x02uy;
file_size_str = str(file_size) + 'ul'

out = \
    """
val {}: u:unit -> St unit
let {} u =
    let request: B.buffer U8.t = B.malloc HyperStack.root 0uy {} in
{}
    let s : parse_result = parse request {} in
        T.eq_str !$"TEST_TITLE message_name check" !$"???" s.message_name;
        T.eq_u8 !$"TEST_TITLE message_type check" ???uy s.message_type;
        T.eq_u8 !$"TEST_TITLE flag check" ???uy s.flags.flag;
        T.eq_u8 !$"TEST_TITLE dup_flag check" ???uy s.flags.dup_flag;
        T.eq_u8 !$"TEST_TITLE qos_flag check" ???uy s.flags.qos_flag;
        T.eq_u8 !$"TEST_TITLE retain_flag check" ???uy s.flags.retain_flag;
        T.eq_u32 !$"TEST_TITLE remaining_length check" ???ul s.remaining_length;
        T.eq_str !$"TEST_TITLE error_message check" !$"???" s.error_message;
B.free request
""".format(func_name, func_name, file_size_str, hex_list_str, file_size_str).replace('TEST_TITLE', test_title)

print(out)
