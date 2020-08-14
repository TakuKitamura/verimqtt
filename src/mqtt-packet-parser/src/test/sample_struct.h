typedef struct struct_flags_s
{
  uint8_t flag;
  uint8_t dup_flag;
  uint8_t qos_flag;
  uint8_t retain_flag;
}
struct_flags;

typedef struct struct_connect_s
{
  C_String_t protocol_name;
  uint8_t protocol_version;
  struct_connect_flags flags;
  uint16_t keep_alive;
  struct_utf8_string connect_id;
  struct_connect_will will;
  struct_utf8_string user_name;
  struct_binary_data password;
}
struct_connect;

typedef struct struct_fixed_header_s
{
  uint8_t message_type;
  C_String_t message_name;
  struct_flags flags;
  uint32_t remaining_length;
  struct_connect connect;
  struct_variable_header_publish publish;
  struct_disconnect_reason disconnect;
  struct_property property;
  struct_error_struct error;
}
struct_fixed_header;