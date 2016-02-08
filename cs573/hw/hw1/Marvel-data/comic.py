input = open("marvel.txt")
output = open("result.txt", 'w')
lastToken = ''
count = 0
numOfCh = 0
countDict = {}
countList = []
for line in input.readlines():
    line = line.split(' ')
    token = line[0]
    if (token == lastToken):
        count+=1
    else:
        output.write("%d%s"%(count,"\n"))
        if (count in countDict):
            countDict[count] += 1
        else:
            countDict[count] = 1
            countList.append(count)
        count = 1
        lastToken = token
        numOfCh += 1
        
print numOfCh
if (count in countDict):
    countDict[count] += 1
else:
    countDict[count] = 1

countList.sort()
countList.reverse()
cumulativeCountDict = {}  #ECCDF P[X > x]
bte = 0
bt = 0
for count in countList:
    bte += countDict[count]
    bt = bte - countDict[count]
    cumulativeCountDict[count] = bt * 1.0 / numOfCh

#print cumulativeCountDict
input.close()
output.close()

import numpy as np
import matplotlib.pyplot as plt
import math
x = cumulativeCountDict.keys()
y = cumulativeCountDict.values()

plt.xlim([min(x),max(x)])
#plt.plot(x,y,'ro')
plt.loglog(x,y,'ro')
plt.show()
