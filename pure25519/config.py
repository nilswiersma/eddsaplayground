import sys

def init():
    global verbose
    global spa
    global spa_file
    global swap
    
    verbose = [] #['pk', 'sign', 'scalarmult', 'open']
    spa = False
    spa_file = sys.stdout
    swap = False

