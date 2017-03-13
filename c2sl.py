# March 13, 2017
# A translator from C to FOL in python

import re
import sys
TEMP = '_T_'
LABEL = '_L_'
TC = 0  # for generating temporary functions to yield xt1,xt2,...
LC = 0  # for generating smallest macro constants in a loop _N1, _N2,... as well as
               # natural number variables _n1,_n2,...

#   [label,'assign',left-side,right-side]
#   V' = E
#   X' = X
#   for all x. heap'(x) = heap(x)
def assign_type(program, variables):
    axioms = []
    label_num = program[0]
    left_side = program[2]
    right_side = program[3]
    for [name, arity, types] in variables:
        if (left_side == name): # variable matches!
            temp_1 = name + '\'' if label_num == '-1' else name + LABEL + label_num # t1 is left-side
            axioms.append(temp_1 + ' = ' + right_side)
        else: # other variables
            temp_1 = name+'\'' if label_num =='-1' else name + LABEL + label_num
            axioms.append(temp_1 + ' = ' +  name)

    # heap x
    if (label_num == '-1'):
        axioms.append("for all x. heap'(x) = heap(x)")
    else:
        axioms.append("for all x. heap" + LABEL + label_num + "(x) = heap(x)")
    return axioms

# get the final label recursively
def last_label(p):
    if p[1]=='seq':
        return last_label(p[3])
    else:
        return p[0]

# replace_vars_in_axiom(lstring,os,ns,v): for each x in v, replace x+os by x+ns
def replace_vars_in_axiom(lstring, origin_s, new_s, variables):
    for i in range(len(lstring)):
        for [name, arity, type] in variables:
            lstring[i] = lstring[i].replace(name+origin_s, name+new_s)

#     [label,'seq',statement1,program]
def seq_type(program, variables):
    global TC
    statement1 = program[2]
    rest_program = program[3]
    axioms1 = trans_to_first_order(statement1, variables) #axioms for the first atomic statement
    axioms2 = trans_to_first_order(rest_program, variables) #axioms for the second program
    label = last_label(statement1)
    if label=='-1': #the first statement has no label
        TC += 1
        replace_vars_in_axiom(axioms1, '\'', TEMP+str(TC), variables)
        replace_vars_in_axiom(axioms2, '', TEMP+str(TC), variables)

        # replace heap
        #replaceHeapInSeq(axioms1, axioms2)

    else: #the first statement has a label
        replace_vars_in_axiom(axioms2, '', LABEL+label, variables)
    return axioms1+axioms2

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
#     [label,'if1',condition,program]
#     [label,'if2',condition,program1,program2]
#     [label,'while',condition,body]
#     [label,'assign',left-side,right-side]
#     [label,'cons',left-side,right-side]
def trans_to_first_order(program, variables):
    method = program[1]
    if (method == "assign"):
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