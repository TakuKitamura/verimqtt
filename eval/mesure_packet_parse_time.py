import subprocess
import time
import random
import matplotlib.pyplot as plt
import japanize_matplotlib

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

# make_file_path = '../src/out/mqttPacketParser.out'
# command = ['make', '-C', '../src', 'measure_time']
command = ['make', '-C', '../src', 'measure_time_optimize']
subprocess.check_output(command, stderr=subprocess.STDOUT)

i = 0
total_packet_size = 0
total_time = 0.0

n = 50

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

    file_data = '30{}{}{}00{}'.format(
        encode_remaining_length(topic_name_length + payload_length + 3),
        get_topic_length(topic_name_length),
        '61' * topic_name_length,
        '61' * payload_length
    )

    packet_file_path = '../src/packet_example.bin'
    mqtt_packet_data = bytearray.fromhex(file_data)
    if len(mqtt_packet_data) <= 268435460:
        with open(packet_file_path, 'wb') as f:
                f.write(mqtt_packet_data)
    else:
        print('done')
        break

    executed_file_path = '../src/out/mqttPacketParser.out'
    command = [executed_file_path, packet_file_path]

    res = subprocess.check_output(command).decode('utf-8', 'ignore').strip().split(', ')
    packet_size = int(res[0].split('=', 1)[1])
    total_packet_size += packet_size
    time = float(res[1].split('=', 1)[1][:8])
    total_time += time

    i += 1
    j += interval

    totol_packet_count = i
    print('計測パケット合計数:', totol_packet_count, '個')

    average_packet_size_b = total_packet_size / totol_packet_count
    print('平均パケットサイズ: {:.15f}'.format(average_packet_size_b), 'byte')

    one_packet_parse_time = total_time / totol_packet_count
    print('1パケットあたりのパース時間: {:.15f}'.format(one_packet_parse_time), 's')

    x.append(payload_length/1000/1000) # mb
    y.append(one_packet_parse_time*1000) # ms

fig = plt.figure()

ax = fig.add_subplot()
ax.plot(x, y, marker='o', label='計測パケット(合計個数: {}個)'.format(totol_packet_count))

plt.title('パケットサイズとパケットパース時間の関係 (最適化レベルは高め)')
plt.xlabel('パケットサイズ [mb]')
plt.ylabel('1パケットあたりのパース時間 [ms]')

plt.legend()

plt.show()