#!/usr/bin/env python

def waddle():
    print "Waddle waddle"

def quack():
   print "Quack! Quack!"

def paddle():
    print "Splish, splosh"

def breath():
    print "sigh"
    
duck = { 'walk' : waddle,
         'talk' : quack,
         'breath_air' : breath,
         'swim' : paddle }


def fishy_swim():
    print "silently undulating"

def use_gills():
    print "silently filtering"

fish = { 'swim' : fishy_swim, 
         'breath_water' : use_gills }

def hopitty():
    print "Hippity, hop"

rabbit = { 'hop' : hopitty,
           'breath_air' : breath }

def swim_ye_swimmers(swimmers):
    for swimmer in swimmers:
        swimmer['swim']()

def do_action(collection,key):
    for obj in collection:
        obj[key]()
        
if __name__ == "__main__":
    swimmers = [fish, duck]
    swim_ye_swimmers(swimmers)

    do_action(swimmers,'swim')

    walkers = [duck] 
    
    do_action(walkers,'walk')


