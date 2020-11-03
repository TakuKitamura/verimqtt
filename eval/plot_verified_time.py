import matplotlib.pyplot as plt
import japanize_matplotlib

fig = plt.figure()

ax = fig.add_subplot()

x = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
y = [126.343, 127.172, 120.440, 115.896, 115.205,
     109.733, 112.092, 103.419, 117.148, 106.160]
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
