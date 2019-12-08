with open('time.txt', mode='rt', encoding='utf-8') as f:
    read_data = list(f)
    i = 0
    total_packet_size = 0
    total_time = 0.0
    for v in read_data:
        line = str(v).strip().split(', ')
        # print(line)
        packet_size = int(line[0].split('=', 1)[1])
        total_packet_size += packet_size
        # print(packet_size)
        time = float(line[1].split('=', 1)[1][:8])
        total_time += time
        # print(time)
        i += 1
    print('packet_number:', i, "個")
    print('ave_packet_size:', total_packet_size / i, "bytes")
    print( "ave_parse_time: {:.15f}".format(total_time / i), "秒")