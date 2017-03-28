#!/usr/bin/python
# -*- coding: utf-8 -*-

# March 13, 2017
# A translator from C to FOL in python

import re
import sys

TEMP = ''  # one char to identify temp num
LABEL = '' # one char to identify label
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
def replace_vars_in_first_axiom(lstring, origin_s, new_s, variables):
    for i in range(len(lstring)):
        if (lstring[i].find("heap") == -1):
            for [name, arity, type] in variables:
                lstring[i] = lstring[i].replace(name+origin_s, name+new_s)
        else:
            lstring[i] = lstring[i].replace("heap'", "heap" + new_s)

# replace_vars_in_axiom(lstring,os,ns,v): for each x in v, replace x+os by x+ns
def replace_vars_in_second_axiom(lstring, label, variables):
    for i in range(len(lstring)):
        if (lstring[i].find("heap") != -1):
            lstring[i] = lstring[i].replace("heap(", "heap" + label + "(")
        for [name, arity, type] in variables:
            extStr = ' ' + lstring[i] + ' '
            indexList = re.finditer(name, extStr)
            tmp_str = ""
            prev = 0
            for index in indexList:
                if (not extStr[index.end()].isalnum()) and (extStr[index.end()] != "'"):
                    tmp_str += extStr[prev:index.start()] + name + label
                    prev = index.end()
            tmp_str += extStr[prev:]
            lstring[i] = tmp_str[1:-1]

#     [label,'seq',P1,P2]
#   if no label:
#   (heap'(x)/heap*(x)) for x in P1;
#   (heap(x)/heap*(x))  for x in P2;

#   if has label:
#   (heap(x)/heap_L_(x)) for x in P2;
def seq_type(program, variables):
    global TC
    statement1 = program[2]
    rest_program = program[3]
    axioms1 = trans_to_first_order(statement1, variables) #axioms for the first atomic statement
    axioms2 = trans_to_first_order(rest_program, variables) #axioms for the second program
    label_num = last_label(statement1)
    if label_num=='-1': #the first statement has no label
        TC += 1
        replace_vars_in_first_axiom(axioms1, '\'', TEMP+str(TC), variables)
        replace_vars_in_second_axiom(axioms2, TEMP+str(TC), variables)


    else: #the first statement has a label
        replace_vars_in_second_axiom(axioms2, LABEL+label_num, variables)

    return axioms1+axioms2

#   [label,'if1',condition,program]
def one_if_type(program, variables):
    condition = program[2]
    cur_label_num = program[0]
    rest_program = program[3]
    second_label = last_label(rest_program)

    axioms = trans_to_first_order(rest_program, variables)

    if (cur_label_num == "-1"):
        if (second_label == "-1"):
            for i in range(len(axioms)):
                axioms[i] = condition + " -> " + axioms[i]
            for [name, arity, type] in variables:
                axioms.append("not (" + condition + ") -> " + name + '\'' + ' = ' + name)
        else: # a final label in body
            for [name, arity, type] in variables:
                axioms.append(condition + ' -> ' + name + ' = ' + name + LABEL + second_label)
                axioms.append('not (' + condition + ') -> ' + name + ' = ' + name)
    else: # if-then has a label
        if (second_label == '-1'): # body has no final label
            replace_vars_in_first_axiom(axioms, '\'', LABEL+cur_label_num, variables)
            for i in range(len(axioms)):
                axioms[i] = condition + ' -> ' + axioms[i]
            for [name, arity, type] in variables:
                axioms.append('not (' + condition + ') -> ' +name + LABEL + cur_label_num + ' = ' + name)
        else: # body has a final label
            for [name, arity, type] in variables:
                axioms.append(condition + ' -> ' + name + LABEL + cur_label_num + ' = ' + name + LABEL + second_label)
                axioms.append('not (' + condition + ') -> ' + name + LABEL + cur_label_num + ' = ' + name)
    return axioms

#     [label,'if2',condition,program1,program2]

def if_else_type(program, variables):
    axioms1 = trans_to_first_order(program[3], variables)
    axioms2 = trans_to_first_order(program[4], variables)
    label1 = last_label(program[3])
    label2 = last_label(program[4])
    condition = program[2]
    cur_num = program[0]

    if (cur_num == "-1"): # no label, so ignore it
        if (label1 == "-1"):
            for i in range(len(axioms1)):
                axioms1[i] = condition + " -> " + axioms1[i]
        else:
            for [name, arity, type] in variables:
                axioms1.append(condition + " -> " + name + "' = " + name + LABEL + label1)

        if (label2 == "-1"):
            for i in range(len(axioms2)):
                axioms2[i] = 'not (' + condition + ') -> ' + axioms2[i]
        else:  # if case has no label
            for [name, arity, type] in variables:
                axioms2.append('not (' + condition + ') -> ' + name + '\' = ' + name + LABEL + label2)
    else:
        if (label1 == "-1"):
            replace_vars_in_first_axiom(axioms1, '\'', LABEL + cur_num, variables)
            for i in range(len(axioms1)):
                axioms1[i] = condition + ' -> ' + axioms1[i]
        else:
            for [name, arity, type] in variables:
                axioms1.append(condition + ' -> ' + name + LABEL + cur_num + ' = ' + name + LABEL + label1)
        if (label2 == '-1'):  # else case has no final label
            replace_vars_in_first_axiom(axioms2, '\'', LABEL + cur_num)
            for i in range(len(axioms2)):
                axioms2[i] = 'not (' + condition + ') -> ' + axioms2[i]
        else:  # if case has label
            for [name, arity, type] in variables:
                axioms2.append('not (' + condition + ') -> ' + name + LABEL + cur_num + ' = ' + name + LABEL + label2)

    return axioms1+axioms2

# used in while tyep method
# return s[n], using variable list v, new temp count string tc, and body label bl

def extend_arg(s,n,v,tc,bl):
    r=re.compile('\w+[\']?')
    s=s+' '
    m=r.finditer(s)
    l=[]
    for mi in m:
        l.append([mi.start(),mi.end(),mi.group()])
    l.sort(reverse=True)
    for i in l:
        if i[2].startswith('_N'):
            if s[i[1]]=='(':
                s=s[:i[1]+1]+n+','+s[i[1]+1:]
            else:
                s=s[:i[1]]+'('+n+')'+s[i[1]:]
        else:
            for [x,k,_] in v:
                if i[2].startswith(x):
                    if i[2]==x:
                        if bl=='-1':  #body has no label, use temp
                            if s[i[1]]=='(':
                                s=s[:i[1]]+tc+'('+n+','+s[i[1]+1:]
                            else:
                                s=s[:i[1]]+tc+'('+n+')'+s[i[1]:]
                        else: #body has label, use it
                            if s[i[1]]=='(':
                                s=s[:i[1]]+LABEL+bl+'('+n+')'+s[i[1]+1:]
                            else:
                                s=s[:i[1]]+LABEL+bl+'('+n+')'+s[i[1]:]
                    elif i[2]==x+'\'': #implies body has no label
                            if s[i[1]]=='(':
                                s=s[:i[1]-1]+tc+'('+n+'+1,'+s[i[1]+1:]
                            else:
                                s=s[:i[1]-1]+tc+'('+n+'+1)'+s[i[1]:]
                    elif i[2]==x+LABEL+bl: #implies body has label
                            if s[i[1]]=='(':
                                s=s[:i[1]]+'('+n+'+1,'+s[i[1]+1:]
                            else:
                                s=s[:i[1]]+'('+n+'+1)'+s[i[1]:]
                    elif (i[2].startswith(x+LABEL)) or (i[2].startswith(x+TEMP)):
                        if s[i[1]]=='(':
                            s=s[:i[1]+1]+n+','+s[i[1]+1:]
                        else:
                            s=s[:i[1]]+'('+n+')'+s[i[1]:]
    return s[:-1]

#     [label,'while',condition,body]
def while_type(program, variables):
    global LC
    global TC
    body = program[3]
    condition = program[2]
    cur_num = program[0]
    axioms = trans_to_first_order(body, variables)  # axioms for the body of the loop
    llabel = last_label(body)  # label of the last statement in the body
    TC += 1
    LC += 1

    # first step
    for i in range(len(axioms)):
        axioms[i] = extend_arg(axioms[i], '_n' + str(LC), variables, TEMP+str(TC), llabel)


    if (condition[0] == '(') and (condition[2][-1] == ')'):
        sml='not ' + condition
    else:
        sml='not (' + condition +')'
    sml=extend_arg(sml, '_n'+str(LC), variables, TEMP+str(TC), llabel)
    axioms.append('smallest(_N' + str(LC) + ',_n' + str(LC) + ',' + sml + ')') #construct smallest macro


    init = TEMP+str(TC) if (llabel=='-1') else LABEL+llabel
    succ = '\'' if (cur_num == '-1') else LABEL + cur_num

    for [name, arity, type] in variables: #initial value and output value axioms
        axioms.append(name + init + '(0) = ' + name)
        axioms.append(name + succ + ' = ' + name + init + '(_N' + str(LC) + ')')

    axioms.append("for all x. heap(x) = heap(x, 0)")
    axioms.append("for all x. heap'(x) = heap(x, _N" + str(LC) + ")")
    return axioms

def cons_type(label_num, left_val, right_list, variables):
    axioms = []
    origin = left_val
    if (label_num != '-1'):
        left_val = left_val + LABEL + label_num
        heap = "heap" + LABEL + label_num
    else:
        left_val = left_val + "'"
        heap = "heap'"
    for [name, arity, types] in variables:
        if (name != origin):
            if (label_num == '-1'):
                axioms.append(name + "' = " + name)
            else:
                axioms.append(name + LABEL + label_num + " = " + name)
        else:
            first_step = "not(" + left_val + " = nil) and not(" + left_val + ") = ill)"
            second_step = " and " + heap + "(" + left_val + ") = nil"
            if_part = "for all x. not(x = " + left_val + ") "
            axioms.append(heap + "(" + left_val + ") = " + str(right_list[0]))

            i = 1
            while (i < (len(right_list))):
                axioms.append(heap + "(" + left_val + " + " + str(i) + ") = " + str(right_list[i]))
                second_step += " and " + heap + "(" + left_val + " + " + str(i) + ") = nil"
                if_part += "and not(x = " + left_val + " + " + str(i) + ") "
                i += 1

            if_part += "implies " + heap + "(x) = heap(x)"
            axioms.append(first_step + second_step)
            axioms.append(if_part)
    return axioms

def right_address_type(label_num, left_val, right_val, variables):
    axioms = []
    origin = left_val  # in order to indentify the original var name
    if (label_num != '-1'):
        left_val = left_val + LABEL + label_num
        heap = "heap" + LABEL + label_num
    else:
        left_val = left_val + "'"
        heap = "heap'"
    for [name, arity, types] in variables:
        if (name != origin):
            if (label_num == '-1'):
                axioms.append(name + "' = " + name)
            else:
                axioms.append(name + LABEL + label_num + " = " + name)
        else:
            axioms.append("heap(" + right_val + ") = nil or heap(" + right_val +") = ill implies "
                          + left_val + " = ill")
            axioms.append("not (heap(" + right_val + ") = nil) and not (heap(" + right_val
                          +") = ill) implies " + left_val + " = heap(" + right_val + ")")
    axioms.append("for all x. " + heap + "(x) = heap(x)")
    return axioms

def left_address_type(label_num, left_val, right_val, variables):
    axioms = []
    for [name, arity, types] in variables:
        if (label_num == '-1'):
            axioms.append(name + "' = " + name)
        else:
            axioms.append(name + LABEL + label_num + " = " + name)
    axioms.append("heap(" + left_val + ") = nil or heap(" + left_val + ") = ill implies heap'(" +
                  left_val + ") = ill")
    axioms.append("not (heap(" + left_val + ") = nil) and not (heap(" + left_val + ") = ill) implies heap'("
                  + left_val + ") = " + right_val)
    axioms.append("for all x. not (x = " + left_val + ") implies heap'(x) = heap(x)")
    return axioms

def dispose_type(label_num, right_val, variables):
    axioms = []
    for [name, arity, types] in variables:
        if (label_num == '-1'):
            axioms.append(name + "' = " + name)
        else:
            axioms.append(name + LABEL + label_num + " = " + name)
    axioms.append("heap'(" + right_val + ") = nil or heap(" + right_val + ") = ill impiles heap'("
                  + right_val + ") = ill")
    axioms.append("not (heap(" + right_val + ") = nil) and not (heap(" + right_val + ") = ill impiles " +
                    "heap'(" + right_val +") = nil")
    axioms.append("for all x. not(x = " + right_val + ") impiles heap'(x) = heap(x)")
    return axioms

# A program is represented by a list
#     [label,type,...]
#   where label is a string representing the label of the
#   statement or '-1' if it has no label, type is 'while' (while-loop),
#   'if1' (if-then), 'if2' (if-then-else), 'seq' (sequence), or '='
#   (assignment):
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
        return cons_type(program[0], program[2], program[3], variables)
    elif (method == "right_address"):
        return right_address_type(program[0], program[2], program[3], variables)
    elif (method == "left_address"):
        return left_address_type(program[0], program[2], program[3], variables)
    elif (method == "dispose"):
        return dispose_type(program[0], program[2], variables)
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

def simple_test():
    # 不用行号的例子
    ex3 = ['-1', '=', 'x', 'y+2'] # x = y + 2
    ex2 = ['-1', 'seq', ['-1', '=', 'x', '1'], ex3] # x = 1
    ex1 = ['-1', 'seq', ['-1', '=', 'y', '5'], ex2]  # y=5; x=1; x=y+1
    v1 = [['x', 0, ['int']], ['y', 0, ['int']]]
    trans_start(ex1, v1)

def simple_label_test():
    # 使用行号的例子

    # y=5; x=1; x=y+1

    ex3 = ['3', '=', 'x', 'y+2'] # x = y + 2
    ex2 = ['-1', 'seq', ['2', '=', 'x', '1'], ex3] # x = 1
    ex1 = ['-1', 'seq', ['1', '=', 'y', '5'], ex2]
    v1 = [['x', 0, ['int']], ['y', 0, ['int']]]
    trans_start(ex1, v1)

def simple_while_test():
    fact0 = ['-1', 'seq', ['-1', '=', 'i', '1'], ['-1', '=', 'F', '1']]
    fact1 = ['-1', 'seq', ['-1', '=', 'F', 'F*i'], ['-1', '=', 'i', 'i+1']]
    fact2 = ['-1', 'while', 'i<=X', fact1]
    fact = ['-1', 'seq', fact0, fact2]
    vfact = [['i', 0, ['int']], ['X', 0, ['int']], ['F', 0, ['int']]]
    trans_start(fact, vfact)

def hard_test():

    # X := cons(1, 2, 3)
    # Y ：= 【X]
    # [X+1] := 4
    # dispose(X+1)
    ex_2 = ['3', 'left_address', 'X+1', '4']
    ex_1 = ['2', 'right_address', 'Y', 'X']
    ex_0 = ['1', 'cons', 'X', ['1', '2', '3']]

    ex4 = ['-1', 'dispose', 'X+1']
    ex3 = ['-1', 'seq', ex_2, ex4]
    ex2 = ['-1', 'seq', ex_1, ex3]
    ex1 = ['-1', 'seq', ex_0, ex2]

    v1 = [['X', 0, ['int*']], ['Y', 0, ['int*']]]
    trans_start(ex1, v1)

def hard_while_test():
    """
    C1: I := cons(1, 2, 3)
    C2: S := 0
    C3: E := 3
    C4: while S < E do
    C5:     K := [I+S]
    C6:     T := [I+E]
    C7:     [I+S] := T
    C8:     [I+E] := K
    C9:     S := S+1
    C10:    E := E-1
    """
    ex_10 = ['-1', '=', 'E', 'E-1']
    ex_9 = ['-1', '=', 'S', 'S+1']
    ex_8 = ['-1', 'left_address', 'I+E', 'K']
    ex_7 = ['-1', 'left_address', 'I+S', 'T']
    ex_6 = ['-1', 'right_address', 'T', 'I+E']
    ex_5 = ['-1', 'right_address', 'K', 'I+S']
    ex_3 = ['-1', '=', 'E', '3']
    ex_2 = ['-1', '=', 'S', '0']
    ex_1 = ['-1', 'cons', 'I', ['1', '2', '3']]

    ex9 = ['-1', 'seq', ex_9, ex_10]
    ex8 = ['-1', 'seq', ex_8, ex9]
    ex7 = ['-1', 'seq', ex_7, ex8]
    ex6 = ['-1', 'seq', ex_6, ex7]
    ex5 = ['-1', 'seq', ex_5, ex6]
    ex4 = ['-1', 'while', 'S < E', ex5]
    ex3 = ['-1', 'seq', ex_3, ex4]
    ex2 = ['-1', 'seq', ex_2, ex3]
    ex1 = ['-1', 'seq', ex_1, ex2]

    v1 = [['I', 0, ['int*']], ['S', 0, ['int']], ['E', 0, ['int']], ['K', 0, ['int*']], ['T', 0, ['int*']]]
    trans_start(ex1, v1)

def hard_while_test_with_label():
    ex_10 = ['10', '=', 'E', 'E-1']
    ex_9 = ['9', '=', 'S', 'S+1']
    ex_8 = ['8', 'left_address', 'I+E', 'K']
    ex_7 = ['7', 'left_address', 'I+S', 'T']
    ex_6 = ['6', 'right_address', 'T', 'I+E']
    ex_5 = ['5', 'right_address', 'K', 'I+S']
    ex_3 = ['3', '=', 'E', '3']
    ex_2 = ['2', '=', 'S', '0']
    ex_1 = ['1', 'cons', 'I', ['1', '2', '3']]

    ex9 = ['-1', 'seq', ex_9, ex_10]
    ex8 = ['-1', 'seq', ex_8, ex9]
    ex7 = ['-1', 'seq', ex_7, ex8]
    ex6 = ['-1', 'seq', ex_6, ex7]
    ex5 = ['-1', 'seq', ex_5, ex6]
    ex4 = ['4', 'while', 'S < E', ex5]
    ex3 = ['-1', 'seq', ex_3, ex4]
    ex2 = ['-1', 'seq', ex_2, ex3]
    ex1 = ['-1', 'seq', ex_1, ex2]

    v1 = [['I', 0, ['int*']], ['S', 0, ['int']], ['E', 0, ['int']], ['K', 0, ['int*']], ['T', 0, ['int*']]]
    trans_start(ex1, v1)

#the main function
if __name__ == '__main__':
    hard_while_test_with_label()