import matplotlib.pyplot as plt
import japanize_matplotlib

fig = plt.figure()

ax = fig.add_subplot()

x = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
y = [144.306,144.014,144.242,144.257,143.252,141.454,141.875,141.771,139.630,139.204]
print(sum(y)/len(y))

ax.plot(x, y, marker='o', label='検証時間')
plt.plot([0, 10], [sum(y)/len(y), sum(y)/len(y)],
         "red", linestyle='dashed', label='平均検証時間')

plt.title('プログラム検証時間の測定')
plt.xlabel('検証回数 [回]')
plt.ylabel('プログラム検証時間 [s]')
plt.xlim(0, 10)
plt.ylim(0, 150)

plt.legend()

plt.show()
