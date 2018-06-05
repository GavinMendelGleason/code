#!/usr/bin/env python3

from assignment2 import *

if __name__ == "__main__":
    """
    Fill in your server communication code here...

    example: 
    """

    coordinates = server('get_coordinates')
    print(coordinates)
    coordinates = server('go_east',location=coordinates)
    print(coordinates)
    sword = server('pick_up',location=coordinates)
    print(sword)
    coordinates = server('go_west',location=coordinates)
    print(coordinates)
    coordinates = server('go_north',location=coordinates)
    print(coordinates)
    coordinates = server('go_north',location=coordinates)
    print(coordinates)
    coordinates = server('go_east',location=coordinates)
    print(coordinates)
    coordinates = server('go_east',location=coordinates)
    print(coordinates)
    knot = server('pick_up',location=coordinates)
    print(knot)
    success = server('slice',items=[sword,knot])
    print(success)
