import socket

def get_topic_length(topic_name_length):
    hex_str = '{0:04x}'.format(topic_name_length)
    return hex_str[0:2] + ' ' + hex_str[2:4]

def encode_remaining_length(remaining_length):
    remaining_length_hex_str = ''
    while True:
        d = remaining_length % 128
        remaining_length //= 128
        if remaining_length > 0:
            d |= 128
        remaining_length_hex_str += '{0:02x} '.format(d & 255)
        if remaining_length == 0:
            break
    return remaining_length_hex_str

target_ip = "localhost"
target_port = 1883
buffer_size = 4096

tcp_client = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

tcp_client.connect((target_ip,target_port))

tcp_client.send(b"\x10\x10\x00\x04\x4d\x51\x54\x54\x05\x02\x00\x3c\x03\x21\x00\x14\x00\x00")

_ = tcp_client.recv(buffer_size)

i = 0
total_packet_size = 0
total_time = 0.0

n = 50

max_interval = 268435460

interval = 268435460 // (n - 1)

j = 0

x = []
y = []

while True:
  # 1,65535
  # topic_name_length = random.randint(1, 65535)
  topic_name_length = 1
  # 0, 268435455
  # payload_length = random.randint(0, 268435455)
  payload_length = j

  # print(encode_remaining_length(topic_name_length + payload_length + 3))
  data = '30{}{}{}00{}'.format(
      encode_remaining_length(topic_name_length + payload_length + 3),
      get_topic_length(topic_name_length),
      '61' * topic_name_length,
      '61' * payload_length
  )

  mqtt_packet_data = bytearray.fromhex(data)

  if len(mqtt_packet_data) <= max_interval:
      pass
  else:
      print('done')
      break

  tcp_client.send(mqtt_packet_data)

  total_packet_size += len(mqtt_packet_data)
  i += 1
  j += interval

  totol_packet_count = i
  print('計測パケット合計数:', totol_packet_count, '個')
  average_packet_size_b = total_packet_size / totol_packet_count
  print('平均パケットサイズ: {:.15f}'.format(average_packet_size_b), 'byte')

  x.append(payload_length/1000/1000) # mb

# tcp_client.send(b"\x30\x30\x00\x0D\x65\x78\x61\x6D\x70\x6C\x65\x2F\x74\x6F\x70\x69\x63\x00\x68\x65\x6C\x6C\x6F\x20\x6D\x71\x74\x74\x21\x20\xE3\x81\x93\xE3\x82\x93\xE3\x81\xAB\xE3\x81\xA1\xE3\x81\xAF\x4D\x51\x54\x54\x21")
print(x)
tcp_client.send(b"\xe0\x00")
