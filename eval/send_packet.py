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

res = tcp_client.recv(buffer_size)
print('Connect ACK:', res)

topic_name = 'example/topic'
topic_name_length = len(topic_name)

payload = 'Hello MQTT!'
payload_length = len(payload)

# print(encode_remaining_length(topic_name_length + payload_length + 3))
data = '30{}{}{}00{}'.format(
    encode_remaining_length(topic_name_length + payload_length + 3),
    get_topic_length(topic_name_length),
    topic_name,
    payload
)
tcp_client.send(b"\x30\x30\x00\x0D\x65\x78\x61\x6D\x70\x6C\x65\x2F\x74\x6F\x70\x69\x63\x00\x68\x65\x6C\x6C\x6F\x20\x6D\x71\x74\x74\x21\x20\xE3\x81\x93\xE3\x82\x93\xE3\x81\xAB\xE3\x81\xA1\xE3\x81\xAF\x4D\x51\x54\x54\x21")

tcp_client.send(b"\xe0\x00")
