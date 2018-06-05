#!/usr/bin/env python

def f(n):
    if n == 0:
        return 1
    else:
        return 3 * 2 ** (n-1) * f(n-1)
