# March 13, 2017
# A translator from C to FOL in python

import re
import sys
TEMP = ''
LABEL = '_'
TC = 0  # for generating temporary functions to yield xt1,xt2,...
LC = 0  # for generating smallest macro constants in a loop _N1, _N2,... as well as
               # natural number variables _n1,_n2,...

#     [label,'assign',left-side,right-side]
def assign_type(program, variables):
    axioms = []
    names = program[2]
    for [x,k,_] in variables:
        if (x==names[0]): # variable matches!
            if (k != names[1]):
                print(names[0]+ ' has arity mismatch in '+program+' with ')
                print([x,k,_])
                print(' in the variable list.')
                sys.exit()
            else:
                print 1
    return axioms

def seq_type(program, vars):
    axioms = []
    print "ok"
    return axioms

def one_if_type(program, vars):
    axioms = []
    print "ok"
    return axioms

def if_else_type(program, vars):
    axioms = []
    print "ok"
    return axioms

def while_type(program, vars):
    axioms = []
    print "ok"
    return axioms

def cons_type(program, vars):
    axioms = []
    print "ok"
    return axioms

def right_address_type(program, vars):
    axioms = []
    print "ok"
    return axioms

def left_address_type(program, vars):
    axioms = []
    print "ok"
    return axioms

def dispose_type(program, vars):
    axioms = []
    print "ok"
    return axioms

# A program is represented by a list
#     [label,type,...]
#   where label is a string representing the label of the
#   statement or '-1' if it has no label, type is 'while' (while-loop),
#   'if1' (if-then), 'if2' (if-then-else), 'seq' (sequence), or '='
#   (assignment):
#     [label,'seq',statement1,program]
#     [label,'if1',condition,program]
#     [label,'if2',condition,program1,program2]
#     [label,'while',condition,body]
#     [label,'assign',left-side,right-side]
#     [label,'cons',left-side,right-side]
def trans_to_first_order(program, variables):
    method = program[1]
    if (method == "="):
        return assign_type(program, variables)
    elif (method == "seq"):
        return seq_type(program, variables)
    elif (method == "one_if"):
        return one_if_type(program, variables)
    elif (method == "if_else"):
        return if_else_type(program, variables)
    elif (method == "while"):
        return while_type(program, variables)
    elif (method == "cons"):
        return cons_type(program, variables)
    elif (method == "right_address"):
        return right_address_type(program, variables)
    elif (method == "left_address"):
        return left_address_type(program, variables)
    elif (method == "dispose"):
        return dispose_type(program, variables)
    else:
        print "Unknown type"
        sys.exit()


def trans_start(program, variables):
    global TC
    global LC
    TC = 0
    LC = 0
    ax = trans_to_first_order(program, variables)
    for x in ax: print(x)

#the main function
if __name__ == '__main__':
    ex1 = ['-1', 'assign', 'x', '1']  # x=1
    ex2 = ['-1', 'assign', 'x', 'y+1']  # x=y+1
    ex3 = ['-1', 'seq', ex1, ex2]  # x=1; x=y+1
    v1 = [['x', 0, ['int']], ['y', 0, ['int']]]
    trans_start(ex1, v1)