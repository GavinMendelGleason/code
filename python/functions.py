#!/usr/bin/env python


def fact(n):
    if (n == 0):
        return 1
    else:
        return n * (fact(n-1))

def factFor(n):
    res = 1
    for i in range(1,n+1):
        res = i * res

    return res
        
