from statistics import mean
import numpy as np

original_parser_times = []
with open('/tmp/original_parser_time.txt') as f:
  data = f.read()
  original_parser_times = data.split(',')
  original_parser_times.pop()

my_parser_time_times = []
with open('/tmp/my_parser_time.txt') as f:
  data = f.read()
  my_parser_time_times = data.split(',')
  my_parser_time_times.pop()

if len(my_parser_time_times) != len(original_parser_times):
  print('failed mesure time.')
  exit(0)

for i in range(0, len(original_parser_times)):
  original_parser_times[i] = float(original_parser_times[i])
  my_parser_time_times[i] = float(my_parser_time_times[i])



original_parser_times_split = np.array_split(original_parser_times, 10)
my_parser_time_times_split = np.array_split(my_parser_time_times, 10)

print(original_parser_times_split)

print(list(np.mean(original_parser_times_split, axis=0)))
print(list(np.mean(my_parser_time_times_split, axis=0)))

# print(original_parser_times_split)
# for i in range(0, len(original_parser_times_split)):
#   print(original_parser_times_split[i], my_parser_time_times_split[i])
#   print()