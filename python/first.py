#!/usr/bin/env python

# print("hello how r u")
msg = "hello how r u"
blahblah = "hello how r u"

# print(msg)

def test(msg):
    
    for i in range(0,10):
        msg = msg + blahblah
        print(msg)





def name_dialog():
    print("Hello, what is your name!")
    name = input()
    print("Your name is %s" % name)

name_dialog()


def whiletest():

    var=0
    
    while var < 10:
        print("asdf")
        var = var + 1


whiletest()
