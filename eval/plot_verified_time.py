import matplotlib.pyplot as plt
import japanize_matplotlib

fig = plt.figure()

ax = fig.add_subplot()

x = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
y = [240+22.188, 240+32.542, 240+28.652, 240+29.426, 240+18.897, 240+18.786, 240+16.401, 240+14.427, 240+26.244, 240+26.244]
print(sum(y)/len(y))

ax.plot(x, y, marker='o', label='検証時間')
plt.plot([0, 11],[sum(y)/len(y), sum(y)/len(y)], "red", linestyle='dashed', label='平均検証時間')

plt.title('同一ソースコードの検証時間の測定')
plt.xlabel('検証回数 [回]')
plt.ylabel('同一ソースコードの検証時間 [s]')
plt.xlim(0, 11)
plt.ylim(0, 280)

plt.legend()

plt.show()