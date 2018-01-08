#!/usr/bin/env python

# Solution for "West of Loathing" elevator

import sys

a = 411
b = 295
c = 161

class LoopExit( Exception ):
    pass

i = 0
j = 0
k = 0
s = 0
tries = 0
try: 
    while s <= 3200:
        while s <= 3200:
            while s <= 3200:
                if s == 3200:
                    print("solution: i=%s j=%s k=%s in %s tries" % (i,j,k,tries))
                    raise LoopExit
                tries += 1
                k += 1
                s = i * a + j * b + k * c
            k = 0
            j += 1
            s = i * a + j * b + k * c        
        j = 0
        i += 1
        s = i * a + j * b + k * c    
except LoopExit as e:
    pass


tries=0
try: 
    for i in range(0,100):
        for j in range(0,100):
            for k in range(0,100):
                if i * a + j * b + k * c == 3200:
                    print("Solution: i=%s j=%s k=%s in %s tries" % (i,j,k,tries))
                    raise LoopExit
                tries +=1
except LoopExit as e:
    pass
            
