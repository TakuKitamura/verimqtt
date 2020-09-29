# Verimqtt

検証済みのセキュアな MQTT 実装

### dependency

- F\* (https://github.com/FStarLang/FStar)
- Kremlin (https://github.com/FStarLang/kremlin)

### work

MQTT の PUBLISH, CONNECT, DISCONNECT パケットのセキュアなパースに対応.

セキュア・・・ここでは C 言語プログラムのメモリ安全性が保証されており, かつ, MQTT が満たすべき制約(仕様)を F\*言語により記述しておりその仕様を少なくても満たす

```sh
$ git clone https://github.com/TakuKitamura/verimqtt.git
$ cd verimqtt/src/mqtt-packet-parser
$ make
$ ./mqttPacketParser.out bin/connect/connect_all/connect_all.bin # CONNECT パケットのパース例
data.message_type = 0x01
data.message_name = CONNECT
data.flags.flag = 0x00
data.flags.dup_flag = 0xff
data.flags.qos_flag = 0xff
data.flags.retain_flag = 0xff
data.remaining_length = 114

data.connect.protocol_name = MQTT
data.connect.protocol_version = 5
data.connect.flags.connect_flag = 0xc6
data.connect.flags.user_name = 0x01
data.connect.flags.password = 0x01
data.connect.flags.will_retain = 0x00
data.connect.flags.will_qos = 0x00
data.connect.flags.will_flag = 0x01
data.connect.flags.clean_start = 0x01
data.connect.keep_alive = 0x3c
data.connect.connect_id.utf8_string_length = 10
data.connect.connect_id.utf8_string_value =
 [0x63, 0x6F, 0x6E, 0x6E, 0x65, 0x63, 0x74, 0x5F, 0x69, 0x64]
data.property.payload_start_index = 74
data.connect.will.connect_will_property.property_id = 3
data.connect.will.connect_will_property.property_type_id = 4
data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_length = 17
data.connect.will.connect_will_property.property_type_struct.utf8_encoded_string_struct.utf8_string_value =
 [0x77, 0x69, 0x6C, 0x6C, 0x5F, 0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x5F, 0x74, 0x79, 0x70, 0x65]

data.connect.will.connect_will_topic_name.utf8_string_length = 10
data.connect.will.connect_will_topic_name.utf8_string_value =
 [0x77, 0x69, 0x6C, 0x6C, 0x5F, 0x74, 0x6F, 0x70, 0x69, 0x63]
data.connect.will.connect_will_payload.binary_length = 12
data.connect.will.connect_will_payload.binary_value =
 [0x77, 0x69, 0x6C, 0x6C, 0x5F, 0x70, 0x61, 0x79, 0x6C, 0x6F, 0x61, 0x64]


data.connect.user_name.utf8_string_length = 4
data.connect.user_name.utf8_string_value =
 [0x75, 0x73, 0x65, 0x72]
data.connect.password.binary_length = 8
data.connect.password.binary_value =
 [0x70, 0x61, 0x73, 0x73, 0x77, 0x6F, 0x72, 0x64]


data.property.payload_start_index = 41
data.property.property_id = 38
data.property.property_type_id = 7
data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_length = 7
data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_key.utf8_string_value =
 [0x63, 0x6F, 0x6E, 0x6E, 0x65, 0x63, 0x74]
data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_length = 13
data.property.property_type_struct.utf8_string_pair_struct.utf8_string_pair_value.utf8_string_value =
 [0x75, 0x73, 0x65, 0x72, 0x5F, 0x70, 0x72, 0x6F, 0x70, 0x65, 0x72, 0x74, 0x79]

data.error.code=0
data.error.message=
```
