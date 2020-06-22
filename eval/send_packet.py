import socket

def get_topic_length(topic_name_length):
    hex_str = '{0:04x}'.format(topic_name_length)
    return hex_str[0:2] + hex_str[2:4]

def encode_remaining_length(remaining_length):
    remaining_length_hex_str = ''
    while True:
        d = remaining_length % 128
        remaining_length //= 128
        if remaining_length > 0:
            d |= 128
        remaining_length_hex_str += '{0:02x}'.format(d & 255)
        if remaining_length == 0:
            break
    return remaining_length_hex_str

target_ip = "localhost"
target_port = 1883
buffer_size = 4096

tcp_client = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

tcp_client.connect((target_ip,target_port))

tcp_client.send(b"\x10\x10\x00\x04\x4d\x51\x54\x54\x05\x02\x00\x3c\x03\x21\x00\x14\x00\x00")

res = tcp_client.recv(buffer_size)
# print('Connect ACK:', res)

topic_name = 'example/topic'
topic_name_length = len(topic_name)

payload = 'Hello MQTT!'
payload_length = len(payload)

data = '30{}{}{}00{}'.format(
    encode_remaining_length(topic_name_length + payload_length + 3),
    get_topic_length(topic_name_length),
    topic_name.encode('utf-8', 'replace').hex(),
    payload.encode('utf-8', 'replace').hex()
)

tcp_client.send(bytearray.fromhex(data))

tcp_client.send(b"\xe0\x00")
