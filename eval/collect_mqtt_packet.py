import subprocess
import sys
import os
import string
import random
# mosquitto_pub -t 'example/topic' -m 'hello world' -V mqttv5

def randomname(n):
   randlst = [random.choice(string.ascii_letters + string.digits) for i in range(n)]
   return ''.join(randlst)

while True:
    topic_name = randomname(random.randint(1,1000))
    payload = randomname(random.randint(1,1000))
    res = subprocess.run(
        ['mosquitto_pub', '-t', topic_name, '-m', payload, '-V', 'mqttv5'],
        stdout=subprocess.PIPE
    )
    sys.stdout.buffer.write(res.stdout)
    # print(123)