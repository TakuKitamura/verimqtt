import matplotlib.pyplot as plt
from matplotlib import lines
import japanize_matplotlib
import pandas as pd
from sklearn import linear_model

# ['file_name:0', 'packet_count:1', 'packet_byte:2', 'emqtt5_ave_time[μs]:3', 'verimqtt_ave_time[μs]:4']

X_MAX = 120
Y_MAX = 16

def plot_data(file_path, o_level):
  fig = plt.figure()

  ax = fig.add_subplot()

  df = pd.read_csv(file_path, index_col=0)

  packet_byte_x = df['packet_byte']
  emqtt5_ave_time_y1 = df['emqtt5_ave_time[μs]']
  verimqtt_ave_time_y2 = df['verimqtt_ave_time[μs]']

  color_map = {'emqtt5': 'blue', 'verimqtt': 'red'} if o_level == 0 else {'emqtt5': 'blue', 'verimqtt': 'red'}

  for _ in range(0, 2):
    for i, x in enumerate(packet_byte_x):
      ax.plot(x, emqtt5_ave_time_y1[i], marker='.', color=color_map['emqtt5'])
      ax.plot(x, verimqtt_ave_time_y2[i], marker='.', color=color_map['verimqtt'])


  target_x = [[x] for x in packet_byte_x ]

  # line_color = {emqtt5: 'blue', verimqtt: 'red'} if o_level == 0 else {emqtt5: 'cyan', verimqtt: 'magenta'}

  lr = linear_model.LinearRegression()

  lr.fit(target_x, emqtt5_ave_time_y1)
  slope = lr.coef_[0] # 傾き
  intercept = lr.intercept_ # 切片
  print('y={:+,f}x{:+,f} // emqtt5'.format(slope, intercept))

  emqtt5_line = lines.Line2D([0, X_MAX], [intercept, X_MAX * slope + intercept], color=color_map['emqtt5'], alpha=0.3, label='emqtt5の回帰直線')

  ax.add_line(emqtt5_line)

  lr.fit(target_x, verimqtt_ave_time_y2)
  slope = lr.coef_[0] # 傾き
  intercept = lr.intercept_ # 切片
  print('y={:+,f}x{:+,f} // verimqtt'.format(slope, intercept))

  verimqtt_line = lines.Line2D([0, X_MAX], [intercept, X_MAX * slope + intercept], color=color_map['verimqtt'], alpha=0.3, label='verimqttの回帰直線')
  ax.add_line(verimqtt_line)

  
  # ax.plot(packet_byte_x, lr.predict(target_x), color=color_map['verimqtt'], alpha=0.3, label='verimqttの回帰直線')



# plot_data('./O0.csv', 0)
plot_data('./O2.csv', 2)


plt.title('パケットサイズと平均パース時間の関係(最適化レベルデフォルト値)')
plt.xlabel('パケットサイズ [byte]')
plt.ylabel('1パケットあたりの平均パース時間 [μs]')
plt.xlim(0, X_MAX)
plt.ylim(0, Y_MAX)

plt.legend()

plt.show()


# with open('./O2.csv') as f:
#     read_csv = csv.reader(f)