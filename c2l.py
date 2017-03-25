# March 20, 2016 
# A translator from C to FOL in python 

"""
Assumptions:
1. Program variables:
  - "heap" is not allowed in any part of the name
  - except for "heap", can be any word \w+,
  - cannot be _x\d*, _n\d*, _N\d* (these are reserved for general variables,
    natural number variables, and smallest macro constants in our axioms)
  - for a variable, its temporary variants are constructed by adding to it TEMP+number
    and its output values after a labeled statement are constructed by adding to it LABEL+number.
    (Currently, TEMP is empty and LABEL is '_'.) This menas that if V is a variable, then
    V+TEMP+\d+ and V+LABEL+\d+ are not allowed to be variables (right now it means that
    V1,V2,... and V_1,V_2,... cannot be variables).
  - smallest is a reserved word so cannot be a variable
2. Program variable lists:
  They are lists of lists of the form 
    [variable-name, arity, type], where type is a list of the form
    [return-type, type-of-parameter-1, ...]
  Any example is: [['x',0,['int']],['y',1,['int','char']]], so x is a constant of
  type int, and y a unary function from char to int.
3. Programs:
  A program is represented by a list
    [label,type,...]
  where label is a string representing the label of the 
  statement or '-1' if it has no label, type is 'while' (while-loop),
  'if1' (if-then), 'if2' (if-then-else), 'seq' (sequence), or '=' 
  (assignment):
    [label,'seq',statement1,program]
    [label,'if1',condition,program]
    [label,'if2',condition,program1,program2]
    [label,'while',condition,body]
    [label,'=',left-side,right-side]

For example, the prgram
1: while x<y(1) { 2: x=y(1); if x<y(1) then y(1)=x; x=y(2) }
will be represented as
['1', 'while', 'x<y(1)',
 ['-1', 'seq', ['2', '=', 'x','y(1)'],
  ['-1', 'seq', ['-1', 'if1', 'x<y(1)', ['-1','=','y(1)','x']],
   ['-1','=','x','y(2)']]]]
and its list of variables is [['x',0,['int']],['y',1,['int','int']]].
"""

import re

# base language (not used for now)

_base = ['=','==','<','<=','>','>=','*','+','-','/']

#Temporary function names are constructed as: variable-name + TEMP + TC
#Output function names are: variable-name + LABEL + LC
# TC: TempCount, a global counter for naming temporary variables
# LC: LoopCount, a global counter for naming loop constants and variables

TEMP = ''
LABEL = '_'
TC = 0  # for generating temporary functions to yield xt1,xt2,...
LC = 0  # for generating smallest macro constants in a loop _N1, _N2,... as well as
               # natural number variables _n1,_n2,...

# for testing
def translate1(p,v):
    global TC
    global LC
    TC=0
    LC=0
    ax = translate0(p,v)
    for x in ax: print(x)
    return ax

# translate0(program,variables) returns a sequence of equations representing \Pi_P^X

def translate0(p,v):
    if p[1]=='while':
        return translateWhile(p,v)
    if p[1]=='seq':
        return translateSeq(p,v)
    if p[1]=='if1':
        return translateIf1(p,v)
    if p[1]=='if2':
        return translateIf2(p,v)
    if p[1]=='=':
        return translateAssign(p,v)

    # to be extended

def translateWhile(p,v):
    global LC
    global TC
    axioms = translate0(p[3],v) # axioms for the body of the loop
    llabel = last_label(p[3])   # label of the last statement in the body
    TC +=1
    LC += 1
    for i in range(len(axioms)):
        axioms[i]=extend_arg(axioms[i],'_n'+str(LC),v,TEMP+str(TC),llabel)
    if (p[2][0]=='(') and (p[2][-1]==')'): #add (not B) (B is the condition of
        #the loop) to the axioms in preparation for constructing smallest macro
        sml='not '+p[2]
    else:
        sml='not ('+p[2]+')'
    sml=extend_arg(sml,'_n'+str(LC),v,TEMP+str(TC),llabel)
    axioms.append('smallest(_N'+str(LC)+',_n'+str(LC)+','+sml+')') #construct smallest macro
    if llabel=='-1': #body has no label
        init=TEMP+str(TC)
    else:
        init=LABEL+llabel
    if p[0]=='-1': #while has no label
        succ='\''
    else:
        succ=LABEL+p[0]
    for [x,k,type] in v: #initial value and output value axioms
        if k==0:
            axioms.append(x+init+'(0) = '+x)
            axioms.append(x+succ+' = '+x+init+'(_N'+str(LC)+')')
        else:
            xtuple = get_var_tuple(k)
            axioms.append(x+init+'(0,'+xtuple[1:]+' = '+x+xtuple)
            axioms.append(x+succ+xtuple+' = '+x+init+'(_N'+str(LC)+','+xtuple[1:])
    return axioms


def translateIf1(p,v):
    axioms = translate0(p[3],v)
    llabel = last_label(p[3])
    if p[0]=='-1': # if-then has no label
        if (llabel=='-1'): # body has no final label
            for i in range(len(axioms)):
                axioms[i] = p[2] + ' -> ' + axioms[i]
            for [x,k,_] in v:
                axioms.append('not ('+p[2]+') -> ' + x+'\''+get_var_tuple(k)+ 
                              ' = '+x+get_var_tuple(k))
        else: # body has a final label
            for [x,k,_] in v:
                axioms.append(p[2]+' -> ' + x+get_var_tuple(k)+' = '+x+LABEL+llabel+get_var_tuple(k))
                axioms.append('not ('+p[2]+') -> ' + x+get_var_tuple(k)+ 
                              ' = '+x+get_var_tuple(k))
    else: # if-then has a label
        if llabel=='-1': # body has no final label
            axiom_list_sub(axioms,'\'',LABEL+p[0],v)
            for i in range(len(axioms)):
                axioms[i] = p[2] + ' -> ' + axioms[i]
            for [x,k,_] in v:
                axioms.append('not ('+p[2]+') -> ' + x+LABEL+p[0]+get_var_tuple(k)+ ' = '+x+get_var_tuple(k))
        else: # body has a final label
            for [x,k,_] in v:
                axioms.append(p[2]+' -> ' + x+LABEL+p[0]+get_var_tuple(k)+' = '+
                              x+LABEL+llabel+get_var_tuple(k))
                axioms.append('not ('+p[2]+') -> ' + x+LABEL+p[0]+
                              get_var_tuple(k)+ ' = '+x+get_var_tuple(k))
    return axioms
            
def translateIf2(p,v):
    axioms1 = translate0(p[3],v)
    axioms2 = translate0(p[4],v)
    llabel1 = last_label(p[3])
    llabel2 = last_label(p[4])
    if p[0]=='-1': # if-then-else has no label
        if (llabel1=='-1'): # if case has no label
            for i in range(len(axioms1)):
                axioms1[i] = p[2] + ' -> ' + axioms1[i]
        else: # if case has label
            for [x,k,_] in v:
                axioms1.append(p[2]+' -> ' + x+'\''+get_var_tuple(k)+' = '+
                              x+LABEL+llabel1+get_var_tuple(k))
        if (llabel2=='-1'): # else case has no label
            for i in range(len(axioms2)):
                axioms2[i] = 'not ('+p[2] + ') -> ' + axioms2[i]
        else: # if case has no label
            for [x,k,_] in v:
                axioms2.append('not ('+p[2]+') -> ' + x+'\''+get_var_tuple(k)+' = '+
                              x+LABEL+llabel2+get_var_tuple(k))
    else: # if-then-else has a label
        if llabel1=='-1': # if case has no final label
            axiom_list_sub(axioms1,'\'',LABEL+p[0],v)
            for i in range(len(axioms1)):
                axioms1[i] = p[2] + ' -> ' + axioms1[i]
        else: #if case has label
            for [x,k,_] in v:
                axioms1.append(p[2]+' -> ' + x+LABEL+p[0]+get_var_tuple(k)+' = '+
                               x+LABEL+llabel1+get_var_tuple(k))
        if llabel2=='-1': # else case has no final label
            axiom_list_sub(axioms2,'\'',LABEL+p[0])
            for i in range(len(axioms2)):
                axioms2[i] = 'not ('+p[2] + ') -> ' + axioms2[i]
        else: #if case has label
            for [x,k,_] in v:
                axioms2.append('not ('+p[2]+') -> ' + x+LABEL+p[0]+get_var_tuple(k)+' = '+
                               x+LABEL+llabel2+get_var_tuple(k))
    return axioms1+axioms2

def replaceHeapInSeq(ax1, ax2):
    for i in range(len(ax1)):
        ax1[i] = ax1[i].replace("heap'", "heap*")

    for i in range(len(ax2)):
        ax2[i] = ax2[i].replace("heap(", "heap*(")

def translateSeq(p,v):
    global TC
    axioms1 = translate0(p[2],v) #axioms for the first atomic statement
    axioms2 = translate0(p[3],v) #axioms for the second program
    ll=last_label(p[2])
    if ll=='-1': #the first statement has no label
        TC += 1
        axiom_list_sub(axioms1,'\'',TEMP+str(TC),v)
        axiom_list_sub(axioms2,'',TEMP+str(TC),v)

        # replace heap
        #replaceHeapInSeq(axioms1, axioms2)

    else: #the first statement has a label
        axiom_list_sub(axioms2,'',LABEL+ll,v)
    return axioms1+axioms2


def translateAssign(p,v):
    axioms = []
    name = term2list(p[2])
    for [x,k,_] in v:
        if (x==name[0]):
            if (k != name[1]):
                print(name[0]+ ' has arity mismatch in '+p+' with ')
                print([x,k,_])
                print(' in the variable list.')
                sys.exit()
            else:
                t1 = x+'\''+get_var_tuple(k) if p[0]=='-1' else x+LABEL+p[0]+get_var_tuple(k) #t1 is x'(_x1,...,_xk) or xllabel(_x1,..,_xk)
                t2 = p[3] if k==0 else 'if (_x1=' + name[2]+')'
                for i in range(k-1):
                    t2 += '& (_x'+str(i+2) + ' = ' + name[i+3]+')'
                t2 = t2 if k==0 else t2+ ' then '+p[3]+' else ' + x+get_var_tuple(k)
                axioms.append(t1 + ' = ' + t2)
        else:
            t1 = x+'\''+get_var_tuple(k) if p[0]=='-1' else x+LABEL+p[0]+get_var_tuple(k)
            axioms.append(t1 + ' = ' +  x+get_var_tuple(k))

    #adding axiom about heap
    #axioms.append("heap'(X) = heap(X)")
    return axioms

# convert a term like x(t1,t2) to ['x',2,t1,t2] where 2 is the arity of x 
# for simple terms in the right side of assignment only, not for terms with nested function terms like x(y(1,2),2)

def term2list(p):
    m=re.search('\(.*\)',p)
    if m==None:
        return [p,0]
    elif re.search('\(.*\)',m.group()[1:-1]) != None:
        print("A nested term in the left side of the assignment: "+p)
        sys.exit()
    else:
        o=[p[:m.start()]]
        t=m.group()[1:-1].split(',')
        o.append(len(t))
        return o+t
#axiom_list_sub(lstring,os,ns,v): for each x in v, replace x+os by x+ns in 
#every string in lstring
def axiom_list_sub(lstring,os,ns,v): 
    for i in range(len(lstring)):
        s=' '+lstring[i]+' '
        for [x,k,_] in v:
            m=re.finditer(x+os,s)
            l=[]
            for mi in m:
                l.append([mi.start(),mi.end()])
            l.sort(reverse=True)
            for j in l:
                if re.match('\W',s[j[0]-1]) and re.match('\W',s[j[1]]) and s[j[1]]!='\'':
                    s=s[:j[0]]+x+ns+s[j[1]:]
        lstring[i]=s[1:-1]

# get a tuple of variables

def get_var_tuple(k):
    t = '(_x1'
    for i in range(k-1):
        t = t+ ',_x'+str(i+2)
    t = '' if k==0 else t+')'
    return t

# get the label of the last statement of a program

def last_label(p):
    if p[1]=='seq':
        return last_label(p[3])
    else:
        return p[0]

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


# testing examples. 

ex1 = ['-1','=','x', 'y+1'] #x=y+1
ex2 = ['-1','=','y', 'y+1'] #y=y+1
ex3 = ['-1','seq',ex1,ex2]  #x=y+1; y=y+1
v1 = [['x',0,['int']], ['y',0,['int']]]
ex4 = ['-1', '=', 't(x)', 'z(x,t(x))+1+x']
v2 = [['x',0,['int']], ['y',0,['int']], ['t',1,['int','int']],['z',2,['int','int','int']]]
ex5 = ['-1','if2','x=t(1) and y<z(x,y)', ex1, ex4]
#translate1(ex1,v1)
#translate1(ex4,v2)
#translate1(ex5,v2)
#translate1(['-1','while','x<y',ex4],v2)


# factorial function
"""
i=1;
F=1;
while(i <= X) {
 F=F*i;
 i=i+1;
}
"""


fact0 = ['-1','seq',['-1','=','i','1'],['-1','=','F','1']]
fact1 = ['-1','seq',['-1','=','F','F*i'],['-1','=','i','i+1']]
fact2 = ['-1','while', 'i<=X', fact1]
fact = ['-1','seq',fact0,fact2]
vfact = [['i',0,['int']], ['X',0,['int']], ['F',0,['int']]]
#ax=translate1(fact,vfact)
#print ax
# in-place list reversing - see Lin and Yang 2015
"""
J = null;
while I != null do {
    K = next(I);
    next(I) = J;
    J=I;
    I=K;
}
I=J;
"""

lr6 = ['-1','=','I','K']
lr5 = ['-1','seq',['-1','=','J','I'], lr6]
lr4 = ['-1','seq',['-1','=','next(I)','J'], lr5]
lr3 = ['-1','seq',['-1','=','K','next(I)'], lr4]
lr2 = ['-1','while','I != null', lr3]
lr1 = ['-1','seq',lr2,['-1','=','I','J']]
lr = ['-1','seq',['-1','=','J','null'], lr1]
vlr = [['J',0,['list']],['I',0,['list']],['K',0,['list']],['next',1,['list','list']]]

#the main function
if __name__ == '__main__':
    ex3 = ['-1', '=', 'x', 'y+2'] # x = y + 2
    ex2 = ['-1', 'seq', ['-1', '=', 'x', '1'], ex3] # x = 1
    ex1 = ['-1', 'seq', ['-1', '=', 'y', '5'], ex2]  # y=5; x=1; x=y+1
    v1 = [['x', 0, ['int']], ['y', 0, ['int']]]
    translate1(ex1, v1)

    # fact0 = ['-1', 'seq', ['-1', '=', 'i', '1'], ['-1', '=', 'F', '1']]
    # fact1 = ['-1', 'seq', ['-1', '=', 'F', 'F*i'], ['-1', '=', 'i', 'i+1']]
    # fact2 = ['-1', 'while', 'i<=X', fact1]
    # fact = ['-1', 'seq', fact0, fact2]
    # vfact = [['i', 0, ['int']], ['X', 0, ['int']], ['F', 0, ['int']]]
    # translate1(fact, vfact)

    # lr6 = ['-1', '=', 'I', 'K']
    # lr5 = ['-1', 'seq', ['-1', '=', 'J', 'I'], lr6]
    # lr4 = ['-1', 'seq', ['-1', '=', 'next(I)', 'J'], lr5]
    # lr3 = ['-1', 'seq', ['-1', '=', 'K', 'next(I)'], lr4]
    # lr2 = ['-1', 'while', 'I != null', lr3]
    # lr1 = ['-1', 'seq', lr2, ['-1', '=', 'I', 'J']]
    # lr = ['-1', 'seq', ['-1', '=', 'J', 'null'], lr1]
    # vlr = [['J', 0, ['list']], ['I', 0, ['list']], ['K', 0, ['list']], ['next', 1, ['list', 'list']]]
    # translate1(lr, vlr)