module Const

module U8 = FStar.UInt8
module U32 = FStar.UInt32

open C.String

val max_u8: U8.t
let max_u8 = 255uy

val max_u32: U32.t
let max_u32 = 4294967295ul

val min_packet_size: U32.t
let min_packet_size = 2ul

val max_packet_size: U32.t
let max_packet_size = 268435460ul

val max_request_size: U32.t
let max_request_size = 268435461ul

val min_request_size: U32.t
let min_request_size = 0ul

val max_payload_size: U32.t
let max_payload_size = 268435455ul

type type_packet_size =
  packet_size:
    U32.t{U32.v packet_size >= U32.v min_packet_size && U32.v packet_size <= U32.v max_packet_size}

type type_mqtt_control_packets = U8.t
let define_mqtt_control_packet_CONNECT : type_mqtt_control_packets = 1uy
let define_mqtt_control_packet_CONNACK : type_mqtt_control_packets = 2uy
let define_mqtt_control_packet_PUBLISH : type_mqtt_control_packets = 3uy
let define_mqtt_control_packet_PUBACK : type_mqtt_control_packets = 4uy
let define_mqtt_control_packet_PUBREC : type_mqtt_control_packets = 5uy
let define_mqtt_control_packet_PUBREL : type_mqtt_control_packets = 6uy
let define_mqtt_control_packet_PUBCOMP : type_mqtt_control_packets = 7uy
let define_mqtt_control_packet_SUBSCRIBE : type_mqtt_control_packets = 8uy
let define_mqtt_control_packet_SUBACK : type_mqtt_control_packets = 9uy
let define_mqtt_control_packet_UNSUBSCRIBE : type_mqtt_control_packets = 10uy
let define_mqtt_control_packet_UNSUBACK : type_mqtt_control_packets = 11uy
let define_mqtt_control_packet_PINGREQ : type_mqtt_control_packets = 12uy
let define_mqtt_control_packet_PINGRESP : type_mqtt_control_packets = 13uy
let define_mqtt_control_packet_DISCONNECT : type_mqtt_control_packets = 14uy
let define_mqtt_control_packet_AUTH : type_mqtt_control_packets = 15uy

type type_mqtt_control_packet_label = C.String.t
let define_mqtt_control_packet_CONNECT_label : type_mqtt_control_packet_label = !$"CONNECT"
let define_mqtt_control_packet_CONNACK_label : type_mqtt_control_packet_label = !$"CONNACK"
let define_mqtt_control_packet_PUBLISH_label : type_mqtt_control_packet_label = !$"PUBLISH"
let define_mqtt_control_packet_PUBACK_label : type_mqtt_control_packet_label = !$"PUBACK"
let define_mqtt_control_packet_PUBREC_label : type_mqtt_control_packet_label = !$"PUBREC"
let define_mqtt_control_packet_PUBREL_label : type_mqtt_control_packet_label = !$"PUBREL"
let define_mqtt_control_packet_PUBCOMP_label : type_mqtt_control_packet_label = !$"PUBCOMP"
let define_mqtt_control_packet_SUBSCRIBE_label : type_mqtt_control_packet_label = !$"SUBSCRIBE"
let define_mqtt_control_packet_SUBACK_label : type_mqtt_control_packet_label = !$"SUBACK"
let define_mqtt_control_packet_UNSUBSCRIBE_label : type_mqtt_control_packet_label = !$"UNSUBSCRIBE"
let define_mqtt_control_packet_UNSUBACK_label : type_mqtt_control_packet_label = !$"UNSUBACK"
let define_mqtt_control_packet_PINGREQ_label : type_mqtt_control_packet_label = !$"PINGREQ"
let define_mqtt_control_packet_PINGRESP_label : type_mqtt_control_packet_label = !$"PINGRESP"
let define_mqtt_control_packet_DISCONNECT_label : type_mqtt_control_packet_label = !$"DISCONNECT"
let define_mqtt_control_packet_AUTH_label : type_mqtt_control_packet_label = !$"AUTH"
type type_message_name_restrict =
  v:type_mqtt_control_packet_label{
    v = define_mqtt_control_packet_CONNECT_label ||
    v = define_mqtt_control_packet_CONNACK_label ||
    v = define_mqtt_control_packet_PUBLISH_label ||
    v = define_mqtt_control_packet_PUBACK_label ||
    v = define_mqtt_control_packet_PUBREC_label ||
    v = define_mqtt_control_packet_PUBREL_label ||
    v = define_mqtt_control_packet_PUBCOMP_label ||
    v = define_mqtt_control_packet_SUBSCRIBE_label ||
    v = define_mqtt_control_packet_SUBACK_label ||
    v = define_mqtt_control_packet_UNSUBSCRIBE_label ||
    v = define_mqtt_control_packet_UNSUBACK_label ||
    v = define_mqtt_control_packet_PINGREQ_label ||
    v = define_mqtt_control_packet_PINGRESP_label ||
    v = define_mqtt_control_packet_DISCONNECT_label ||
    v = define_mqtt_control_packet_AUTH_label ||
    v = !$""
  }


type type_mqtt_control_packets_restrict =
  v:type_mqtt_control_packets{U8.v v >= 1 && U8.v v <= 15 || U8.eq v max_u8}

type type_remaining_length =
  (remaining_length: U32.t{U32.v remaining_length <= U32.v (U32.sub max_packet_size 5ul) || U32.eq remaining_length max_u32})

type type_flag_restrict =
  flag: U8.t{
    U8.eq flag 0b0000uy ||
    U8.eq flag 0b0010uy ||
    U8.eq flag max_u8
}

type type_dup_flags = U8.t
let define_dup_flag_first_delivery : type_dup_flags = 0uy
let define_dup_flag_re_delivery : type_dup_flags = 1uy

type type_qos_flags = U8.t
let define_qos_flag_at_most_once_delivery : type_qos_flags = 0b00uy
let define_qos_flag_at_least_once_delivery : type_qos_flags = 0b01uy
let define_qos_flag_exactly_once_delivery : type_qos_flags = 0b10uy

type type_retain_flags = U8.t
let define_retain_flag_must_not_store_application_message : type_retain_flags = 0uy
let define_retain_flag_must_store_application_message : type_retain_flags = 1uy

type type_dup_flags_restrict =
  dup_flag: type_dup_flags{U8.v dup_flag <= 1 || U8.eq dup_flag max_u8}

type type_qos_flags_restrict =
  qos_flag: type_qos_flags{U8.v qos_flag <= 2 || U8.eq qos_flag max_u8}

type type_retain_flags_restrict =
  retain_flag: type_retain_flags{U8.v retain_flag <= 1 || U8.eq retain_flag max_u8}

type type_flags = U8.t

let define_flag_CONNECT : type_flags = 0b0000uy
let define_flag_CONNACK : type_flags = 0b0000uy

let define_flag_PUBACK : type_flags = 0b0000uy
let define_flag_PUBREC : type_flags = 0b0000uy
let define_flag_PUBREL : type_flags = 0b0010uy
let define_flag_PUBCOMP : type_flags = 0b0000uy
let define_flag_SUBSCRIBE : type_flags = 0b0010uy
let define_flag_SUBACK : type_flags = 0b0000uy
let define_flag_UNSUBSCRIBE : type_flags = 0b0010uy
let define_flag_UNSUBACK : type_flags = 0b0000uy
let define_flag_PINGREQ : type_flags = 0b0000uy
let define_flag_PINGRESP : type_flags = 0b0000uy
let define_flag_DISCONNECT : type_flags = 0b0000uy
let define_flag_AUTH : type_flags = 0b0000uy

type struct_flags = {
  flag: type_flag_restrict;
  dup_flag: type_dup_flags_restrict;
  qos_flag: type_qos_flags_restrict;
  retain_flag: type_retain_flags_restrict;
}

type struct_fixed_header_constant = {
  message_type_constant: type_mqtt_control_packets_restrict;
  message_name_constant: type_message_name_restrict;
  flags_constant: struct_flags;
}

type struct_connect_flags = {
      connect_flag: U8.t;
      user_name: U8.t;
      password: U8.t;
      will_retain: U8.t;
      will_qos: U8.t;
      will_flag: U8.t;
      clean_start: U8.t;
  }

type struct_connect_property = {
    connect_property_id: U8.t;
    connect_property_name: C.String.t;
}

let define_connect_property_session_expiry_interval_id: U8.t = 0x11uy
let define_connect_property_receive_maximum_id: U8.t = 0x21uy
let define_connect_property_maximum_packet_size_id: U8.t = 0x27uy
let define_connect_property_topic_alias_maximum_id: U8.t = 0x22uy
let define_connect_property_request_response_information_id: U8.t = 0x19uy
let define_connect_property_request_problem_information_id: U8.t = 0x17uy
let define_connect_property_user_property_id: U8.t = 0x26uy
let define_connect_property_authentication_method_id: U8.t = 0x15uy
let define_connect_property_authentication_data_id: U8.t = 0x16uy

let define_struct_connect_property_session_expiry_interval: struct_connect_property =
  {
    connect_property_id = define_connect_property_session_expiry_interval_id;
    connect_property_name = !$"Session Expiry Interval";
  }

let define_struct_connect_property_receive_maximum: struct_connect_property =
  {
    connect_property_id = define_connect_property_receive_maximum_id;
    connect_property_name = !$"Receive Maximum";
  }

let define_struct_connect_property_maximum_packet_size: struct_connect_property =
  {
    connect_property_id = define_connect_property_maximum_packet_size_id;
    connect_property_name = !$"Maximum Packet Size";
  }

let define_struct_connect_property_topic_alias_maximum: struct_connect_property =
  {
    connect_property_id = define_connect_property_topic_alias_maximum_id;
    connect_property_name = !$"Topic Alias Maximum";
  }

let define_struct_connect_property_request_response_information: struct_connect_property =
  {
    connect_property_id = define_connect_property_request_response_information_id;
    connect_property_name = !$"Request Response Information";
  }

let define_struct_connect_property_request_problem_information: struct_connect_property =
  {
    connect_property_id = define_connect_property_request_problem_information_id;
    connect_property_name = !$"Request Problem Information";
  }

let define_struct_connect_property_user_property: struct_connect_property =
  {
    connect_property_id = define_connect_property_user_property_id;
    connect_property_name = !$"User Property";
  }

let define_struct_connect_property_authentication_method: struct_connect_property =
  {
    connect_property_id = define_connect_property_authentication_method_id;
    connect_property_name = !$"Authentication Method";
  }

let define_struct_connect_property_authentication_data: struct_connect_property =
  {
    connect_property_id = define_connect_property_authentication_data_id;
    connect_property_name = !$"Authentication Data";
  }

// 3.1.2.3 Connect Flags
type struct_connect = {
  protocol_name: C.String.t;
  protocol_version: U8.t;
  flags: struct_connect_flags;
  keep_alive: U32.t;
  connect_topic_length: U32.t;
  connect_property: struct_connect_property;
}  

type type_topic_name_restrict =
  (
    topic_name: C.String.t{U32.v (strlen topic_name) <= 65535}
  )

type type_topic_length_restrict =
  (topic_length_restrict: U32.t{U32.v topic_length_restrict <= 65535 || U32.eq topic_length_restrict max_u32})

type type_property_length = type_remaining_length

type type_payload_restrict =
  (
    payload: C.String.t{U32.v (strlen payload) <= U32.v max_packet_size}
  )

type type_payload_offset = payload_offset: U32.t{U32.v payload_offset < U32.v max_packet_size}

type struct_variable_header_publish = {
  topic_length: type_topic_length_restrict;
  topic_name: type_topic_name_restrict;
  property_length: type_property_length;
  payload: type_payload_restrict;
}

type type_disconnect_reason_code = U8.t
let define_disconnect_reason_code_normal_disconnection: type_disconnect_reason_code = 0uy
let define_disconnect_reason_code_disconnect_with_will_message: type_disconnect_reason_code = 4uy
let define_disconnect_reason_code_unspecified_error: type_disconnect_reason_code = 128uy
let define_disconnect_reason_code_malformed_packet: type_disconnect_reason_code = 129uy
let define_disconnect_reason_code_protocol_error: type_disconnect_reason_code = 130uy
let define_disconnect_reason_code_implementation_specific_error: type_disconnect_reason_code = 131uy
let define_disconnect_reason_code_not_authorized: type_disconnect_reason_code = 135uy
let define_disconnect_reason_code_server_busy: type_disconnect_reason_code = 137uy
let define_disconnect_reason_code_server_shutting_down: type_disconnect_reason_code = 139uy
let define_disconnect_reason_code_keep_alive_timeout: type_disconnect_reason_code = 141uy
let define_disconnect_reason_code_session_taken_over: type_disconnect_reason_code = 142uy
let define_disconnect_reason_code_topic_filter_invalid: type_disconnect_reason_code = 143uy
let define_disconnect_reason_code_topic_name_invalid: type_disconnect_reason_code = 144uy
let define_disconnect_reason_receive_maximum_exceeded: type_disconnect_reason_code = 147uy
let define_disconnect_reason_topic_alias_invalid: type_disconnect_reason_code = 148uy
let define_disconnect_reason_packet_too_large: type_disconnect_reason_code = 149uy
let define_disconnect_reason_message_rate_too_high: type_disconnect_reason_code = 150uy
let define_disconnect_reason_quota_exceeded: type_disconnect_reason_code = 151uy
let define_disconnect_reason_administrative_action: type_disconnect_reason_code = 152uy
let define_disconnect_reason_payload_format_invalid: type_disconnect_reason_code = 153uy
let define_disconnect_reason_retain_not_supported: type_disconnect_reason_code = 154uy
let define_disconnect_reason_qos_not_supported: type_disconnect_reason_code = 155uy
let define_disconnect_reason_use_another_server: type_disconnect_reason_code = 156uy
let define_disconnect_reason_server_moved: type_disconnect_reason_code = 157uy
let define_disconnect_reason_shared_subscriptions_not_supported: type_disconnect_reason_code = 158uy
let define_disconnect_reason_connection_rate_exceeded: type_disconnect_reason_code = 159uy
let define_disconnect_reason_maximum_connect_time: type_disconnect_reason_code = 160uy
let define_disconnect_reason_subscription_identifiers_not_supported: type_disconnect_reason_code = 161uy
let define_disconnect_reason_wildcard_subscriptions_not_supported: type_disconnect_reason_code = 162uy

type type_disconnect_reason_code_name = C.String.t
let define_disconnect_reason_code_normal_disconnection_name: type_disconnect_reason_code_name = !$"Normal disconnection" 
let define_disconnect_reason_code_disconnect_with_will_message_name: type_disconnect_reason_code_name = !$"Disconnect with Will Message"
let define_disconnect_reason_code_unspecified_error_name: type_disconnect_reason_code_name = !$"Unspecified error"
let define_disconnect_reason_code_malformed_packet_name: type_disconnect_reason_code_name = !$"Malformed Packet"
let define_disconnect_reason_code_protocol_error_name: type_disconnect_reason_code_name = !$"Protocol Error"
let define_disconnect_reason_code_implementation_specific_error_name: type_disconnect_reason_code_name = !$"Implementation specific error"
let define_disconnect_reason_code_not_authorized_name: type_disconnect_reason_code_name = !$"Not authorized"
let define_disconnect_reason_code_server_busy_name: type_disconnect_reason_code_name = !$"Server busy"
let define_disconnect_reason_code_server_shutting_down_name: type_disconnect_reason_code_name = !$"Server shutting down"
let define_disconnect_reason_code_keep_alive_timeout_name: type_disconnect_reason_code_name = !$"Keep Alive timeout"
let define_disconnect_reason_code_session_taken_over_name: type_disconnect_reason_code_name = !$"Session taken over"
let define_disconnect_reason_code_topic_filter_invalid_name: type_disconnect_reason_code_name = !$"Topic Filter invalid"
let define_disconnect_reason_code_topic_name_invalid_name: type_disconnect_reason_code_name = !$"Topic Name invalid"
let define_disconnect_reason_receive_maximum_exceeded_name: type_disconnect_reason_code_name = !$"Receive Maximum exceeded"
let define_disconnect_reason_topic_alias_invalid_name: type_disconnect_reason_code_name = !$"Topic Alias invalid"
let define_disconnect_reason_packet_too_large_name: type_disconnect_reason_code_name = !$"Packet too large"
let define_disconnect_reason_message_rate_too_high_name: type_disconnect_reason_code_name = !$"Message rate too high"
let define_disconnect_reason_quota_exceeded_name: type_disconnect_reason_code_name = !$"Quota exceeded"
let define_disconnect_reason_administrative_action_name: type_disconnect_reason_code_name = !$"Administrative action"
let define_disconnect_reason_payload_format_invalid_name: type_disconnect_reason_code_name = !$"Payload format invalid"
let define_disconnect_reason_retain_not_supported_name: type_disconnect_reason_code_name = !$"Retain not supported"
let define_disconnect_reason_qos_not_supported_name: type_disconnect_reason_code_name = !$"QoS not supported"
let define_disconnect_reason_use_another_server_name: type_disconnect_reason_code_name = !$"Use another server"
let define_disconnect_reason_server_moved_name: type_disconnect_reason_code_name = !$"Server moved"
let define_disconnect_reason_shared_subscriptions_not_supported_name: type_disconnect_reason_code_name = !$"Shared Subscriptions not supported"
let define_disconnect_reason_connection_rate_exceeded_name: type_disconnect_reason_code_name = !$"Connection rate exceeded"
let define_disconnect_reason_maximum_connect_time_name: type_disconnect_reason_code_name = !$"Maximum connect time"
let define_disconnect_reason_subscription_identifiers_not_supported_name: type_disconnect_reason_code_name = !$"Subscription Identifiers not supported"
let define_disconnect_reason_wildcard_subscriptions_not_supported_name: type_disconnect_reason_code_name = !$"Wildcard Subscriptions not supported"

type struct_disconnect_reason = {
  disconnect_reason_code: type_disconnect_reason_code;
  disconnect_reason_code_name: type_disconnect_reason_code_name;
}

let define_struct_disconnect_normal_disconnection: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_normal_disconnection;
    disconnect_reason_code_name = define_disconnect_reason_code_normal_disconnection_name;
  }

let define_struct_disconnect_disconnect_with_will_message: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_disconnect_with_will_message;
    disconnect_reason_code_name = define_disconnect_reason_code_disconnect_with_will_message_name;
  }

let define_struct_disconnect_unspecified_error: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_unspecified_error;
    disconnect_reason_code_name = define_disconnect_reason_code_unspecified_error_name;
  }

let define_struct_disconnect_malformed_packet: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_malformed_packet;
    disconnect_reason_code_name = define_disconnect_reason_code_malformed_packet_name;
  }

let define_struct_disconnect_protocol_error: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_protocol_error;
    disconnect_reason_code_name = define_disconnect_reason_code_protocol_error_name;
  }

let define_struct_disconnect_implementation_specific_error: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_implementation_specific_error;
    disconnect_reason_code_name = define_disconnect_reason_code_implementation_specific_error_name;
  }

let define_struct_disconnect_not_authorized: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_not_authorized;
    disconnect_reason_code_name = define_disconnect_reason_code_not_authorized_name;
  }

let define_struct_disconnect_server_busy: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_server_busy;
    disconnect_reason_code_name = define_disconnect_reason_code_server_busy_name;
  }

let define_struct_disconnect_server_shutting_down: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_server_shutting_down;
    disconnect_reason_code_name = define_disconnect_reason_code_server_shutting_down_name;
  }

let define_struct_disconnect_keep_alive_timeout: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_keep_alive_timeout;
    disconnect_reason_code_name = define_disconnect_reason_code_keep_alive_timeout_name;
  }  

let define_struct_disconnect_session_taken_over: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_session_taken_over;
    disconnect_reason_code_name = define_disconnect_reason_code_session_taken_over_name;
  } 

let define_struct_disconnect_topic_filter_invalid: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_topic_filter_invalid;
    disconnect_reason_code_name = define_disconnect_reason_code_topic_filter_invalid_name;
  } 

let define_struct_disconnect_topic_name_invalid: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_code_topic_name_invalid;
    disconnect_reason_code_name = define_disconnect_reason_code_topic_name_invalid_name;
  } 

let define_struct_disconnect_receive_maximum_exceeded: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_receive_maximum_exceeded;
    disconnect_reason_code_name = define_disconnect_reason_receive_maximum_exceeded_name;
  } 

let define_struct_disconnect_topic_alias_invalid: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_topic_alias_invalid;
    disconnect_reason_code_name = define_disconnect_reason_topic_alias_invalid_name;
  } 

let define_struct_disconnect_packet_too_large: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_packet_too_large;
    disconnect_reason_code_name = define_disconnect_reason_packet_too_large_name;
  }   

let define_struct_disconnect_message_rate_too_high: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_message_rate_too_high;
    disconnect_reason_code_name = define_disconnect_reason_message_rate_too_high_name;
  }   

let define_struct_disconnect_quota_exceeded: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_quota_exceeded;
    disconnect_reason_code_name = define_disconnect_reason_quota_exceeded_name;
  }   

let define_struct_disconnect_administrative_action: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_administrative_action;
    disconnect_reason_code_name = define_disconnect_reason_administrative_action_name;
  }   

let define_struct_disconnect_payload_format_invalid: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_payload_format_invalid;
    disconnect_reason_code_name = define_disconnect_reason_payload_format_invalid_name;
  }   

let define_struct_disconnect_retain_not_supported: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_retain_not_supported;
    disconnect_reason_code_name = define_disconnect_reason_retain_not_supported_name;
  }   

let define_struct_disconnect_qos_not_supported: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_qos_not_supported;
    disconnect_reason_code_name = define_disconnect_reason_qos_not_supported_name;
  }   

let define_struct_disconnect_use_another_server: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_use_another_server;
    disconnect_reason_code_name = define_disconnect_reason_use_another_server_name;
  }   

let define_struct_disconnect_server_moved: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_server_moved;
    disconnect_reason_code_name = define_disconnect_reason_server_moved_name;
  }   

let define_struct_disconnect_shared_subscriptions_not_supported: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_shared_subscriptions_not_supported;
    disconnect_reason_code_name = define_disconnect_reason_shared_subscriptions_not_supported_name;
  }   

let define_struct_disconnect_connection_rate_exceeded: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_connection_rate_exceeded;
    disconnect_reason_code_name = define_disconnect_reason_connection_rate_exceeded_name;
  } 

let define_struct_disconnect_maximum_connect_time: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_maximum_connect_time;
    disconnect_reason_code_name = define_disconnect_reason_maximum_connect_time_name;
  } 

let define_struct_disconnect_subscription_identifiers_not_supported: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_subscription_identifiers_not_supported;
    disconnect_reason_code_name = define_disconnect_reason_subscription_identifiers_not_supported_name;
  } 

let define_struct_disconnect_wildcard_subscriptions_not_supported: struct_disconnect_reason =
  {
    disconnect_reason_code = define_disconnect_reason_wildcard_subscriptions_not_supported;
    disconnect_reason_code_name = define_disconnect_reason_wildcard_subscriptions_not_supported_name;
  } 

let define_struct_disconnect_error: struct_disconnect_reason =
  {
    disconnect_reason_code = max_u8;
    disconnect_reason_code_name = !$"";
  }


type type_error_code = U8.t
let define_no_error_code: type_error_code = 0uy
let define_error_remaining_length_invalid_code: type_error_code = 1uy
let define_error_message_type_invalid_code: type_error_code = 2uy
let define_error_flag_invalid_code: type_error_code = 3uy
let define_error_dup_flag_invalid_code: type_error_code = 4uy
let define_error_qos_flag_invalid_code: type_error_code = 5uy
let define_error_retain_flag_invalid_code: type_error_code = 6uy
let define_error_topic_length_invalid_code: type_error_code = 7uy
let define_error_topic_name_dont_zero_terminated_code: type_error_code = 8uy
let define_error_property_length_invalid_code: type_error_code = 9uy
let define_error_payload_invalid_code: type_error_code = 10uy
let define_error_topic_name_have_inavlid_character_code: type_error_code = 11uy
let define_error_protocol_name_invalid_code: type_error_code = 12uy
let define_error_protocol_version_invalid_code: type_error_code = 13uy
let define_error_connect_flag_invalid_code: type_error_code = 14uy

type type_error_code_restrict =
  (v:
    type_error_code{
      v = define_no_error_code ||
      v = define_error_remaining_length_invalid_code ||
      v = define_error_message_type_invalid_code ||
      v = define_error_flag_invalid_code ||
      v = define_error_dup_flag_invalid_code ||
      v = define_error_qos_flag_invalid_code ||
      v = define_error_retain_flag_invalid_code ||
      v = define_error_topic_length_invalid_code ||
      v = define_error_topic_name_dont_zero_terminated_code ||
      v = define_error_topic_name_have_inavlid_character_code ||
      v = define_error_property_length_invalid_code ||
      v = define_error_payload_invalid_code ||
      v = define_error_protocol_name_invalid_code ||
      v = define_error_protocol_version_invalid_code ||
      v = define_error_connect_flag_invalid_code
    }
  )

type type_error_message = C.String.t
let define_error_remaining_length_invalid: type_error_message = !$"remaining_length is invalid."
let define_error_message_type_invalid: type_error_message = !$"message_type is invalid."
let define_error_flag_invalid: type_error_message = !$"flag is invalid."
let define_error_dup_flag_invalid: type_error_message = !$"dup_flag is invalid."
let define_error_qos_flag_invalid: type_error_message = !$"qos_flag is invalid."
let define_error_retain_flag_invalid: type_error_message = !$"retain_flag is invalid."
let define_error_topic_length_invalid: type_error_message = !$"topic_length is invalid."
let define_error_topic_name_dont_zero_terminated: type_error_message = !$"topic_name is not zero-terminated."
let define_error_topic_name_have_inavlid_character: type_error_message = !$"topic_name have invalid character."
let define_error_property_length_invalid: type_error_message = !$"property_length is invalid."
let define_error_payload_invalid: type_error_message = !$"payload is invalid."
let define_error_protocol_name_invalid: type_error_message = !$"protocol name is invalid."
let define_error_protocol_version_invalid: type_error_message = !$"protocol version is invalid."
let define_error_connect_flag_invalid: type_error_message = !$"connect flag is invalid."
let define_no_error: type_error_message = !$""

type type_error_message_restrict =
  (v:
    type_error_message{
      v = define_no_error ||
      v = define_error_remaining_length_invalid ||
      v = define_error_message_type_invalid ||
      v = define_error_flag_invalid ||
      v = define_error_dup_flag_invalid ||
      v = define_error_qos_flag_invalid ||
      v = define_error_retain_flag_invalid ||
      v = define_error_topic_length_invalid ||
      v = define_error_topic_name_dont_zero_terminated ||
      v = define_error_topic_name_have_inavlid_character ||
      v = define_error_property_length_invalid ||
      v = define_error_payload_invalid ||
      v = define_error_protocol_name_invalid ||
      v = define_error_protocol_version_invalid ||
      v = define_error_connect_flag_invalid
    }
  )

type struct_error_struct = {
  code: type_error_code_restrict;
  message: type_error_message_restrict;
}

type struct_fixed_header = {
  message_type: type_mqtt_control_packets_restrict;
  message_name: type_message_name_restrict;
  flags: struct_flags;
  remaining_length: type_remaining_length;
  connect: struct_connect;
  publish: struct_variable_header_publish;
  disconnect: struct_disconnect_reason;
  error: struct_error_struct;
}

type struct_publish_parts = {
  publish_remaining_length: type_remaining_length;
  publish_fixed_header_first_one_byte: U8.t;
  publish_topic_name: type_topic_name_restrict;
  publish_topic_length: type_topic_length_restrict;
  publish_property_length: type_property_length;
  publish_payload: type_payload_restrict;
}

type struct_connect_parts = {
  connect_remaining_length: type_remaining_length;
  connect_connect_constant: struct_fixed_header_constant;
  connect_connect_flag: U8.t;
  connect_keep_alive: U32.t;
  connect_connect_topic_length: U32.t;
  connect_connect_property_id: U8.t;
}

type struct_disconnect_parts = {
  disconnect_remaining_length: type_remaining_length;
  disconnect_disconnect_constant: struct_fixed_header_constant;
}