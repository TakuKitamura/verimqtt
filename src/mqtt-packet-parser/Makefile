SHELL=/bin/bash
krml_link = time krml -verbose -warn-error +9 -drop WasmSupport -drop C_Endianness -drop C -tmpdir ../out -fsopt --cache_dir -fsopt ../out -no-prefix Main -no-prefix Utils -no-prefix Const -no-prefix Common -no-prefix Publish -no-prefix Connect -no-prefix Disconnect -no-prefix FFI -no-prefix Debug -no-prefix Debug_FFI -o ../mqttPacketParser.out main.fst common.fst const.fst publish.fst connect.fst disconnect.fst ffi.fst debug.fst debug_ffi.fst ffi.c debug_ffi.c 

exec_test_c = $(krml_link) /tmp/gen_test.c && ../mqttPacketParser.out && rm ../mqttPacketParser.out

all:
	cd src && $(krml_link) callMain.c

verify:
	cd src && $(krml_link) callMain.c -verify

test_connect_all:
	cd src && python3 test/gen_test/main.py generate ../bin/connect/connect_all/connect_all.bin > /tmp/gen_test.c && $(exec_test_c)

test_connect_password:
	cd src && python3 test/gen_test/main.py generate ../bin/connect/connect_password/connect_password.bin > /tmp/gen_test.c && $(exec_test_c)

test_connect_user:
	cd src && python3 test/gen_test/main.py generate ../bin/connect/connect_user/connect_user.bin > /tmp/gen_test.c && $(exec_test_c)

test_connect_will:
	cd src && python3 test/gen_test/main.py generate ../bin/connect/connect_will/connect_will.bin > /tmp/gen_test.c && $(exec_test_c)

test_normal_connect:
	cd src && python3 test/gen_test/main.py generate ../bin/connect/normal_connect/normal_connect.bin > /tmp/gen_test.c && $(exec_test_c)

test_disconnect_reason:
	cd src && python3 test/gen_test/main.py generate ../bin/disconnect/disconnect_reason/disconnect_reason.bin > /tmp/gen_test.c && $(exec_test_c)

test_normal_disconnect:
	cd src && python3 test/gen_test/main.py generate ../bin/disconnect/normal_disconnect/normal_disconnect.bin > /tmp/gen_test.c && $(exec_test_c)

test_property_binary_data:
	cd src && python3 test/gen_test/main.py generate ../bin/property/property_binary_data/property_binary_data.bin > /tmp/gen_test.c && $(exec_test_c)

test_property_four_byte:
	cd src && python3 test/gen_test/main.py generate ../bin/property/property_four_byte/property_four_byte.bin > /tmp/gen_test.c && $(exec_test_c)

test_property_one_byte:
	cd src && python3 test/gen_test/main.py generate ../bin/property/property_one_byte/property_one_byte.bin > /tmp/gen_test.c && $(exec_test_c)

test_property_two_byte:
	cd src && python3 test/gen_test/main.py generate ../bin/property/property_two_byte/property_two_byte.bin > /tmp/gen_test.c && $(exec_test_c)

test_property_utf8_pair_string:
	cd src && python3 test/gen_test/main.py generate ../bin/property/property_utf8_pair_string/property_utf8_pair_string.bin > /tmp/gen_test.c && $(exec_test_c)

test_property_utf8_string:
	cd src && python3 test/gen_test/main.py generate ../bin/property/property_utf8_string/property_utf8_string.bin > /tmp/gen_test.c && $(exec_test_c)

test_property_variable_byte:
	cd src && python3 test/gen_test/main.py generate ../bin/property/property_variable_byte_integer/property_variable_byte.bin > /tmp/gen_test.c && $(exec_test_c)

test_normal_publish:
	cd src && python3 test/gen_test/main.py generate ../bin/publish/normal_publish/normal_publish.bin > /tmp/gen_test.c && $(exec_test_c)

test_publish_packet_identifier:
	cd src && python3 test/gen_test/main.py generate ../bin/publish/publish_packet_identifier/publish_packet_identifier.bin > /tmp/gen_test.c && $(exec_test_c)

test:
	make && \
	make test_connect_all && \
	make test_connect_password && \
	make test_connect_user && \
	make test_connect_will && \
	make test_normal_connect && \
	make test_disconnect_reason && \
	make test_normal_disconnect && \
	make test_property_binary_data && \
	make test_property_four_byte && \
	make test_property_one_byte && \
	make test_property_two_byte && \
	make test_property_utf8_pair_string && \
	make test_property_utf8_string && \
	make test_property_variable_byte && \
	make test_normal_publish && \
	make test_publish_packet_identifier

verify_and_test:
	make verify && make test