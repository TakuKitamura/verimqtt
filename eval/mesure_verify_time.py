# (time make -C src ) 2>&1 | grep real | cut -b 5- | tr -d '\011'

import subprocess
total_verify_time_sec = 0
mesure_count = 0
stop_count = 3
while True:
    p = subprocess.Popen('./mesure_verify_time.sh', shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p.wait()
    stdout_data = p.stdout.read().decode('utf-8').strip()
    verify_time_sec = int(stdout_data.split('m')[0]) + float(stdout_data.split('m')[1][:-1])
    mesure_count += 1
    total_verify_time_sec += verify_time_sec
    average_verify_time_sec = total_verify_time_sec / mesure_count
    print('平均 {}秒'.format(average_verify_time_sec))
    if (stop_count == mesure_count):
        break