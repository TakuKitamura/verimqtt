#[repr(C)]
struct Struct_variable_header_publish {
  topic_length: u32,
  topic_name: *const std::os::raw::c_char,
  property_length: u32,
  payload: *const std::os::raw::c_char
}

#[repr(C)]
struct Struct_flags {
  flag: u8,
  dup_flag: u8,
  qos_flag: u8,
  retain_flag: u8
}

#[repr(C)]
struct Struct_error_struct {
  code: u8,
  message: *const std::os::raw::c_char
}

#[repr(C)]
struct Struct_fixed_header {
  message_type: u8,
  message_name: *const std::os::raw::c_char,
  flags: Struct_flags,
  remaining_length: u32,
  publish: Struct_variable_header_publish,
  error: Struct_error_struct
}

#[link(name = "mqtt")]
extern "C" {
    fn mqtt_packet_parse(request: *const u8, packet_size: u32) -> Struct_fixed_header;
}

unsafe fn cstring_to_str<'a>(c_string: *const std::os::raw::c_char) -> &'a str {
  return std::ffi::CStr::from_ptr(c_string).to_str().unwrap();
}

/*
RUST 
パケットデータ(同一)
30 30 00 0D 65 78 61 6D 70 6C 65 2F 74 6F 70 69 63 00 68 65 6C 6C 6F 20 6D 71 74 74 21 20 E3 81 93 E3 82 93 E3 81 AB E3 81 A1 E3 81 AF 4D 51 54 54 21
*/
fn main() {
  println!("---call mqtt_packet_parse from rust---");
  let read_bytes = std::fs::read("/Users/kitamurataku/work/verimqtt/src/packet_example.bin");

  let mut read_bytes = match read_bytes {
    Ok(file) => file,
    Err(error) => {
        panic!("There was a problem opening the file: {:?}", error)
    },
  };

  read_bytes.push(0);

  let request_length = (read_bytes.len() as u32) - 1 ;

  let reauest = Box::into_raw(read_bytes.into_boxed_slice()) as *const u8;

  unsafe {
    let data = mqtt_packet_parse(reauest, request_length);
    println!("message_type=0x{:02x?}", data.message_type);
    println!("message_name={}", cstring_to_str(data.message_name));
    println!("flag=0x{:02x?}", data.flags.flag);
    println!("dup_flag=0x{:02x?}", data.flags.dup_flag);
    println!("qos_flag=0x{:02x?}", data.flags.qos_flag);
    println!("retain_flag=0x{:02x?}", data.flags.retain_flag);
    println!("remaining_length={}", data.remaining_length);
    println!("topic_length={}", data.publish.topic_length);
    println!("topic_name={}", cstring_to_str(data.publish.topic_name));
    println!("property_length={}", data.publish.property_length);
    println!("payload={}", cstring_to_str(data.publish.payload));
    println!("error_code={}", data.error.code);
    println!("error_message={}", cstring_to_str(data.error.message));
  }
}