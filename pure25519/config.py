import sys

def init():
    global verbose
    global spa
    global spa_file
    
    verbose = [] #['pk', 'sign', 'scalarmult', 'open']
    spa = False
    spa_file = sys.stdout

