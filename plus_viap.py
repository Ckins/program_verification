# February 24, 2017

import re
import random
# add by Pritom Rajkhowa
import wolframalpha
import sys
import plyj.parser
import plyj.model as m
import subprocess
from sympy import *
import regex
import os
import copy
import time
import datetime
import ConfigParser
from pyparsing import *
from sympy.core.relational import Relational
ParserElement.enablePackrat()

''' Configrations'''

config = ConfigParser.RawConfigParser()
config.read('config.properties')
timeout = config.get('ConfigurationSection', 'timeout')
app_id = config.get('ConfigurationSection', 'app_id')

TIMEOUT = 60000
Mathematica_id = None

_base = ['=', '==', '!=', '<', '<=', '>', '>=', '*', '**', '!', '+', '-', '/', '%', 'ite', 'and', 'or', 'not',\
         'implies', 'all', 'some', 'null']
_infix_op = ['=', '==', '!=', '<', '<=', '>', '>=', '*', '**', '+', '-', '/', '%', 'implies']

current_milli_time = lambda: int(round(time.time() * 1000))
p = plyj.parser.Parser()

'''Classes'''

''' Functions'''
def is_number(s):
    try:
        float(s)  # for int, long and float
    except ValueError:
        try:
            complex(s)  # for complex
        except ValueError:
            return False
    return True

def initConfig():
    # Time Out
    if timeout.strip() != '' and timeout.strip() != 'None' and is_number(timeout.strip()) != False:
        global TIMEOUT
        TIMEOUT = timeout.strip()

    if app_id.strip() != '' and app_id.strip() != 'None':
        global Mathematica_id
        Mathematica_id = app_id.strip()

def getParser():
    global p
    return p

def translate(file_name):
    if not (os.path.exists(file_name)):
        print "File not exits"
        return

    start_time = current_milli_time()
    p = getParser()
    tree = p.parse_file(file_name)
    print tree

if __name__ == "__main__":
    initConfig()
    file_name = 'benchmark/fact.java'
    axiom = translate(file_name)
