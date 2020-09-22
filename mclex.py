print('')
print('+------------------------------------------------------------------+')
print('|  MCLex Ver 4 (September 2020). Python implementation.            |')
print('|  Classificator of matrix classes of lex categories.              |')
print('+------------------------------------------------------------------+')

# Note: to get started, read input.mclex
# Packages
#---------
import sys
import math
import time
import datetime
# The following packages are needed for creating images of matrices
import PIL
from PIL import Image, ImageDraw
import os
# The following is needed to give windows command prompt functionality of erasing lines 
from sys import platform
if platform == "win32":
    import ctypes
    kernel32 = ctypes.windll.kernel32
    kernel32.SetConsoleMode(kernel32.GetStdHandle(-11), 7)

# Global variables
#---------
# This stores text written in output.mclex upon conclusion of execution
Output=[]
# This stores instructions read from input.mclex
Tasks=[]

# Operations on individual matrices
#----------------------------------
# Method for deciding whether M1 implies M2 
def sharper(M1,M2,h,v,transform):
    loop = True
    while loop:
        loop=False
        for i in range(0,h**h):
            for j in range(0,v**(v*h)):
                newcol=transform[0][i][j]
                if newcol not in M2:
                    extend=True
                    for colM1 in M1:
                        newcolM1=transform[colM1][i][j]
                        if newcolM1 not in M2:
                            extend=False
                            break
                    if extend==True:
                        if newcol==0:
                            return True
                        M2.append(newcol)
                        loop=True
    return False
# The function for computing proof of matrix implication
def matrixProof(M1,M2,h,v,transform):
    proof = ''
    loop = True
    while loop:
        loop=False
        for i in range(0,h**h):
            for j in range(0,v**(v*h)):
                newcol=transform[0][i][j]
                if newcol not in M2:
                    extend=True
                    M1transformed=[]
                    for colM1 in M1:
                        newcolM1=transform[colM1][i][j]
                        M1transformed.append(newcolM1)
                        if newcolM1 not in M2:
                            extend=False
                            break
                    if extend==True:
                        proof=proof+str(newcol)+' added thanks to reduction '+str(M1transformed)+'.'
                        if newcol==0:
                            return proof
                        M2.append(newcol)
                        loop=True
    return proof
# Method for deciding whether conjunction of matrices implies a matrix
def consharper(M1list,M2,h,v,transform):
    loop = True
    print('')
    print('Atempting to make derivation '+str(M1list)+'=>'+str(M2)+':')
    while loop:
        loop = False
        oldM2=M2.copy()
        for M1 in M1list:
            if sharper(M1,M2,h,v,transform):
                print(matrixProof(M1,oldM2.copy(),h,v,transform))
                return True
        if oldM2!=M2:
            print(matrixProof(M1,oldM2.copy(),h,v,transform))
            loop = True
    return False
# Creates a matrix from given parameters
def matrixFor(i,h,v):
    M=[]
    binary=toColumn(2**((v**h)-1)-i,v**h,2)
    for j in range(0,len(binary)):
            if binary[j]==1:
                M.append(j)
    return M
    
# Operations on columns
#-----------------------
# Generates the data of all possible transformations of columns
def initialize(col,h,v):
    transform=[[[]]]
    col.insert(0,0)
    no=len(col)
    print('')
    print('Initializing column transform for h='+str(h)+' and v='+str(v)+'.')
    sys.stdout.write('\033[F')
    print('\r')
    start = time.time()
    transform=[[[0 for _ in range(0,v**(v*h))] for _ in range(0,h**h)] for _ in range(0,v**h)]
    for a in col:
        for i in range(0,h**h):
            arr=toColumn(i,h,h)
            for j in range(0,v**(v*h)):
                sub=toColumn(j,v*h,v)
                deccol=toColumn(a,h,v)
                newcol=[0 for _ in range(0,h)]
                for k in range(0,h):
                    newcol[k]=sub[k*v+deccol[arr[k]]]
                transform[a][i][j]=toNumber(newcol,h,v)
        sys.stdout.write('\033[K')        
        print('Initialization progress: '+str(round(100*a/no,2))+'% complete.')
        sys.stdout.write('\033[F')
    end = time.time()
    sys.stdout.write('\033[K')
    print('Initialization successful. Time taken: '+str(int((end-start)))+' seconds.')
    return transform 
# Returns the numerical encoding of a column
def toNumber(col, h, v):
    num=0
    for i in range(0,h):
        num=num+col[i]*(v**(h-1-i))
    return num
# Returns the column encoded by a number
def toColumn(num, h, v):
    col=[]
    while num:
        col.insert(0,int(num % v))
        num = int(num / v)
    while h-len(col):
        col.insert(0,0)
    return col
# Returns column of zeros
def zeroColumn(h):
    col=[]
    for i in range(h):
        col.append(0)
    return col
# Turns columns into rows
def rows(col, h, v):
    rowsfromcol=[]
    for i in range(0,h):
        rowsfromcol.append([])
        for j in range(0,len(col)):
            rowsfromcol[i].append(toColumn(col[j], h, v)[i])
    return rowsfromcol 
# Turns rows into columns
def columns(rows, h, v):
    columnsfromrows=[]
    for i in range(0,len(rows[0])):
        col=[]
        for j in range(0,h):
            col.append(rows[j][i])
        columnsfromrows.append(toNumber(col, h, v))
    return columnsfromrows 

# Operations on matrix lists
#----------------------------
# Returns implication table for a given list of matrices. 
# The last column and row indicate unique representative of each equivalence class
def implicationTable(matrices,h,v,c):
    start=time.time()
    matrices.sort(key=len)
    transform=initialize([i for i in range(1,v**h)],h,v)
    discardedMatrices=[]
    noMatrices=len(matrices)
    table = [[2 for _ in range(0,noMatrices+1)] for _ in range(0,noMatrices+1)]
    entrycounter=0
    addedentries=noMatrices
    print('')
    print('Generating implication table for a total of '+str(noMatrices)+' matrices.')
    for i in range(0,noMatrices):
        table[i][i]=1
    print('')
    for k in range(0,noMatrices):
        M1=matrices[k]
        if M1 not in discardedMatrices:
            table[k][noMatrices]=k
            table[noMatrices][k]=k
            sys.stdout.write('\033[F')
            sys.stdout.write('\033[K')
            print('At most '+str(min(noMatrices-len(discardedMatrices),noMatrices-k))+' matrices remaining to work on.')
            equivalent=''
            implies=''
            M2count=0
            for l in range(k+1,noMatrices):
                M2=matrices[l]
                if M2!=M1 and (M2 not in discardedMatrices):
                    M2count=M2count+1
                    if table[k][l]==2:
                        M2extend=M2.copy()
                        imp=sharper(M1,M2extend,h,v,transform)
                        if imp==True:
                            for a in range(0,noMatrices):
                                if table[k][a]==2 and set(matrices[a])>=set(M2) and set(M2extend)>=set(matrices[a]):
                                    table[k][a]=1
                                    addedentries=addedentries+1
                            implies=implies+decode([M2])
                            if table[l][k]==2:
                                M1extend=M1.copy()
                                revimp=sharper(M2,M1extend,h,v,transform)
                                if revimp==True:
                                    for a in range(0,noMatrices):
                                        if table[l][a]==2 and set(matrices[a])>=set(M1) and set(M1extend)>=set(matrices[a]):
                                            table[l][a]=1 
                                            addedentries=addedentries+1
                                    table[l][noMatrices]=k
                                    table[noMatrices][l]=k
                                    discardedMatrices.append(M2)
                                    equivalent=equivalent+decode([M2])
                                else:
                                    for a in range(0,noMatrices):
                                        if table[l][a]==2 and set(matrices[a])>=set(M1) and set(M1extend)>=set(matrices[a]):
                                            table[l][a]=0
                                            addedentries=addedentries+1
                            elif table[l][k]==1:
                                    table[l][noMatrices]=k
                                    table[noMatrices][l]=k
                                    discardedMatrices.append(M2)
                                    equivalent=equivalent+decode([M2])
                        else:
                            for a in range(0,noMatrices):
                                if table[k][a]==2 and set(matrices[a])>=set(M2) and set(M2extend)>=set(matrices[a]):
                                    table[k][a]=0
                                    addedentries=addedentries+1
                            if table[l][k]==2:
                                M1extend=M1.copy()
                                revimp=sharper(M2,M1extend,h,v,transform)
                                if revimp==True:
                                    for a in range(0,noMatrices):
                                        if table[l][a]==2 and set(matrices[a])>=set(M1) and set(M1extend)>=set(matrices[a]):
                                            table[l][a]=1
                                            addedentries=addedentries+1
                                else:
                                    for a in range(0,noMatrices):
                                        if table[l][a]==2 and set(matrices[a])>=set(M1) and set(M1extend)>=set(matrices[a]):
                                            table[l][a]=0
                                            addedentries=addedentries+1
                    elif table[k][l]==1:
                        implies=implies+decode([M2])
                        if table[l][k]==2:
                            M1extend=M1.copy()
                            revimp=sharper(M2,M1extend,h,v,transform)
                            if revimp==True:
                                for a in range(0,noMatrices):
                                    if table[l][a]==2 and set(matrices[a])>=set(M1) and set(M1extend)>=set(matrices[a]):
                                        table[l][a]=1
                                        addedentries=addedentries+1
                                table[l][noMatrices]=k
                                table[noMatrices][l]=k
                                discardedMatrices.append(M2)
                                equivalent=equivalent+decode([M2])
                            else:
                                for a in range(0,noMatrices):
                                    if table[l][a]==2 and set(matrices[a])>=set(M1) and set(M1extend)>=set(matrices[a]):
                                        table[l][a]=0
                                        addedentries=addedentries+1
                        elif table[l][k]==1:
                                table[l][noMatrices]=k
                                table[noMatrices][l]=k
                                discardedMatrices.append(M2)
                                equivalent=equivalent+decode([M2])
                entrycounter=entrycounter+addedentries
                sys.stdout.write('\033[K')
                sys.stdout.write('\033[K')
                sys.stdout.write('\033[K')
                print(str(M2count-1)+' checked for equivalence with the matrix '+str(M1)+'.')
                print(str(len(discardedMatrices))+' matrices eliminated.')
                print(str(entrycounter)+' implications worked out (not counting implications duplicate by equivalence).')
                sys.stdout.write('\033[F')
                sys.stdout.write('\033[F')
                sys.stdout.write('\033[F')
                addedentries=0
    end = time.time()
    sys.stdout.write('\033[F')
    sys.stdout.write('\033[K')
    sys.stdout.write('\033[K')
    sys.stdout.write('\033[K')
    sys.stdout.write('\033[K')
    print(str(len(discardedMatrices))+' matrices eliminated.')
    print(str(entrycounter)+' implications worked out (not counting implications duplicate by equivalence).')
    sys.stdout.write('\033[K')
    print('Implication table succefully generated. Time taken: '+str(int((end-start)))+' seconds.')
    sys.stdout.write('\033[K')
    return table
# Returns proper matrices in the list
def proper(matrices,h,v,c):
    transform=initialize([i for i in range(1,v*v)],2,v)
    proper=[]
    eliminated=0
    print('')
    print('Extracting certain proper matrices from a list of '+str(len(matrices))+' matrices.')
    start=time.time()
    if c==0:
        c=v**h-1
    for M1 in matrices:
        M1length=len(M1)
        sys.stdout.write('\033[K')
        print(str(len(proper))+' matrices extracted. '+str(eliminated)+' matrices discarded.')
        sys.stdout.write('\033[F')
        if c+1>M1length and M1length>2:
            keep=True
            for i in range(0,M1length-1):
                if M1[i+1]==M1[i] or M1[i+1]<M1[i]:
                    keep=False
                    eliminated=eliminated+1
            M1rows=rows(M1,h,v)
            for row1 in range(0,h):
                if keep==False:
                    break
                for row2 in range(row1+1,h):
                    col=columns([M1rows[row1],M1rows[row2]],2,v)
                    if toNumber(M1rows[row2],M1length,v)<toNumber(M1rows[row1],M1length,v):
                        keep=False
                        eliminated=eliminated+1
                        break
                    if 0 not in col:
                        if sharper(col,[1,2],2,v,transform):
                            keep=False
                            eliminated=eliminated+1
                            break
                if keep==False:
                    break
            if keep==True:
                proper.append(M1)
        else:
            eliminated=eliminated+1
    end=time.time()
    sys.stdout.write('\033[K')
    print(str(len(proper))+' matrices kept. '+str(eliminated)+' matrices discarded.')
    print('Extraction successfully completed. Time taken: '+str(int((end-start)))+' seconds.')
    return proper
# Returns proper matrices in the list of given dimensions       
def properd(h,v,c):
    transform=initialize([i for i in range(1,v*v)],2,v)
    proper=[]
    eliminated=0
    print('')
    print('Extracting certain proper matrices from a list of '+str(2**((v**h)-1))+' matrices.')
    start=time.time()
    if c==0:
        c=v**h-1
    for i in range(1,2**((v**h)-1)):
        M1=matrixFor(i,h,v)
        M1length=len(M1)
        sys.stdout.write('\033[K')
        print(str(len(proper))+' matrices extracted. '+str(eliminated)+' matrices discarded.')
        sys.stdout.write('\033[F')
        if c+1>M1length and M1length>2:
            keep=True
            for i in range(0,M1length-1):
                if M1[i+1]==M1[i] or M1[i+1]<M1[i]:
                    keep=False
                    eliminated=eliminated+1
            M1rows=rows(M1,h,v)
            for row1 in range(0,h):
                if keep==False:
                    break
                for row2 in range(row1+1,h):
                    col=columns([M1rows[row1],M1rows[row2]],2,v)
                    rownum2=toNumber(M1rows[row2],M1length,v)
                    rownum1=toNumber(M1rows[row1],M1length,v)
                    if rownum2<rownum1:
                        keep=False
                        eliminated=eliminated+1
                        break
                    if rownum2==rownum1 and rownum1!=0 and rownum2!=0:
                        keep=False
                        eliminated=eliminated+1
                        break
                    if 0 not in col:
                        if sharper(col,[1,v],2,v,transform):
                            keep=False
                            eliminated=eliminated+1
                            break
                if keep==False:
                    break
            if keep==True:
                proper.append(M1)
        else:
            eliminated=eliminated+1
    end=time.time()
    sys.stdout.write('\033[K')
    print(str(len(proper))+' matrices kept. '+str(eliminated)+' matrices discarded.')
    print('Extraction successfully completed. Time taken: '+str(int((end-start)))+' seconds.')
    return proper
# The same as before but only selects matrices implying a given matrix
def properimplying(matrix,h,v,c):
    matrices=[matrixFor(i,h,v) for i in range(1,2**((v**h)-1))]
    transform=initialize([i for i in range(1,v*v)],2,v)
    transform2=initialize([i for i in range(1,v**h)],h,v)
    proper=[]
    eliminated=0
    print('')
    print('Extracting certain proper matrices from a list of '+str(len(matrices))+' matrices.')
    start=time.time()
    if c==0:
        c=v**h-1
    for M1 in matrices:
        M1length=len(M1)
        sys.stdout.write('\033[K')
        print(str(len(proper))+' matrices extracted. '+str(eliminated)+' matrices discarded.')
        sys.stdout.write('\033[F')
        if c+1>M1length and M1length>2:
            keep=True
            M1rows=rows(M1,h,v)
            for row1 in range(0,h):
                for row2 in range(row1+1,h):
                    col=columns([M1rows[row1],M1rows[row2]],2,v)
                    if toNumber(M1rows[row2],M1length,v)<toNumber(M1rows[row1],M1length,v):
                        keep=False
                        eliminated=eliminated+1
                        break
                    if 0 not in col:
                        if sharper(col,[1,2],2,v,transform):
                            keep=False
                            eliminated=eliminated+1
                            break
                if keep==False:
                    break
            if keep==True:
                if sharper(M1,matrix.copy(),h,v,transform2)==True:
                    proper.append(M1)
                else:
                    eliminated=eliminated+1
    end=time.time()
    sys.stdout.write('\033[K')
    print(str(len(proper))+' matrices kept. '+str(eliminated)+' matrices discarded.')
    print('Extraction successfully completed. Time taken: '+str(int((end-start)))+' seconds.')
    return proper
# The same as before but only selects matrices implied by a given matrix
def properimplied(matrix,matrices,h,v,c):
    transform=initialize([i for i in range(1,v*v)],2,v)
    transform2=initialize([i for i in range(1,v**h)],h,v)
    proper=[]
    eliminated=0
    print('')
    print('Extracting certain proper matrices from a list of '+str(len(matrices))+' matrices.')
    start=time.time()
    if c==0:
        c=v**h-1
    for M1 in matrices:
        M1length=len(M1)
        sys.stdout.write('\033[K')
        print(str(len(proper))+' matrices extracted. '+str(eliminated)+' matrices discarded.')
        sys.stdout.write('\033[F')
        if c+1>M1length and M1length>2:
            keep=True
            M1rows=rows(M1,h,v)
            for row1 in range(0,h):
                for row2 in range(row1+1,h):
                    col=columns([M1rows[row1],M1rows[row2]],2,v)
                    if toNumber(M1rows[row2],M1length,v)<toNumber(M1rows[row1],M1length,v):
                        keep=False
                        eliminated=eliminated+1
                        break
                    if 0 not in col:
                        if sharper(col,[1,2],2,v,transform):
                            keep=False
                            eliminated=eliminated+1
                            break
                if keep==False:
                    break
            if keep==True:
                if sharper(matrix,M1.copy(),h,v,transform2)==True:
                    proper.append(M1)
                else:
                    eliminated=eliminated+1
    end=time.time()
    sys.stdout.write('\033[K')
    print(str(len(proper))+' matrices kept. '+str(eliminated)+' matrices discarded.')
    print('Extraction successfully completed. Time taken: '+str(int((end-start)))+' seconds.')
    return proper

# Operations on poset tables
#----------------------------
# Creates transitive reduction of the poset
def trimPoset(table):
    length=len(table[0])-1
    newtable=[[2 for j in range(0,length+1)] for i in range(0,length+1)] 
    for i in range(0,length):
        newtable[i][length]=table[i][length]
        newtable[length][i]=table[length][i]
        for j in range(0,length):
            if table[table[i][length]][table[j][length]]==1 and table[i][length]!=table[j][length] and newtable[table[i][length]][table[j][length]]==2:
                newtable[table[i][length]][table[j][length]]=1
                for k in range(0,length):
                    if table[k][length]!=table[i][length] and table[k][length]!=table[j][length] and table[table[i][length]][table[k][length]]==1 and table[table[k][length]][table[j][length]]==1:
                        newtable[table[i][length]][table[j][length]]=0
                        break
    print('')
    return newtable   
# Creates transitive closure of the relation of matrix implication
def transitiveClosure(table):
    print('Computing transitive closure.')
    length=len(table[0])
    newtable=[[0 for j in range(0,length)] for i in range(0,length)] 
    loop=True
    while loop:
        loop=False
        for i in range(0,length):
            for j in range(0,length):
                    for k in range(0,length):
                        if table[i][k]==1 and table[k][j]==1 and newtable[i][j]!=1:
                            newtable[i][j]=1
                            loop=True
                            break
    return newtable
# Returns non-duplicating row numbers for matrices
def rowNumbers(matrices,h,v):
    length=len(matrices)
    num=[0 for i in range(0,length)]
    for i in range(0,length):
        uniquerows=[]
        for j in range(0,h):
            row=rows(matrices[i],h,v)[j]
            if rows(matrices[i],h,v)[j] not in uniquerows:
                uniquerows.append(row)
        num[i]=len(uniquerows)
    return num    
def nonzerodistinctrowNumber(matrix,h,v):
    zerorowpresent=False
    uniquerows=[]
    zerorowpresent=False
    for j in range(0,h):
        row=rows(matrix,h,v)[j]
        if rows(matrix,h,v)[j] not in uniquerows:
            uniquerows.append(row)
            if toNumber(row,len(row),v)==0:
                zerorowpresent=True
    num=len(uniquerows)
    if zerorowpresent==False:
        return num
    elif zerorowpresent==True:
        return num-1      
# Chooses a canonical member each equivalence class of matrices
def canonicalRepresentation(table,matrices,h,v):
    length=len(matrices)
    rowno=rowNumbers(matrices,h,v)
    for i in range(0,length):
        for j in range(i+1,length):
            if table[i][length]==table[j][length]: 
                if rowno[table[length][i]]>rowno[j]: 
                    table[length][i]=j
                elif rowno[table[length][i]]==rowno[j]:
                    if len(matrices[table[length][i]])>len(matrices[j]):
                        table[length][i]=j

# Operations of transformation between lists and strings
#--------------------------------------------------------
# Turns sentence string into a list of lists 
def encode(sentence):
    data=[]
    words=sentence.split(',')
    for w in words:
        letters=w.split(' ') 
        column=[]
        for l in letters:
            if l.isdigit():
                column.append(int(l))
        data.append(column)
    return data
# String representation of a list of lists
def decode(data):
    sentence=''
    for i in range(0,len(data)):
        for l in data[i]:
            sentence=sentence+' '+str(l)
        sentence=sentence+','
    return sentence

# Output operations
#--------------------------------------------------------
# See description of codes in input.mclex    
def code1(h,v,c):
    start = time.time()
    matrices=properd(h,v,c)
    matrices.sort(key=len)
    end = time.time()
    Output.append('List of all proper matrices for h='+str(h)+', v='+str(v)+', c='+str(c)+':')
    Output.append(decode(matrices)+'\n')
    print('')
    print('Task (code 1) completed in '+str(int((end-start)))+' seconds.')
def code2(M1,h,v,c):
    start = time.time()
    transform=initialize([i for i in range(1,v**h)],h,v)
    matrices=properd(h,v,c)
    matrices.sort(key=len)
    impliedmatrices=[]
    print('')
    print('Restricting to matrices implied by '+str(M1)+'.')
    for M2index in range(0,len(matrices)):
        if sharper(M1,matrices[M2index].copy(),h,v,transform):
            impliedmatrices.append(M2index)
    end = time.time()
    print('Restriction completed. '+str(len(impliedmatrices))+' matrices kept.\n')
    Output.append('List of all proper matrices implying '+str(M1)+', for h='+str(h)+', v='+str(v)+', c='+str(c)+':')
    Output.append(decode([matrices[impliedmatrices[i]] for i in range(0,len(impliedmatrices))])+'\n')
    print('Task (code 2) completed in '+str(int((end-start)))+' seconds.')
def code3(M1,h,v,c):
    start = time.time()
    transform=initialize([i for i in range(1,v**h)],h,v)
    matrices=properd(h,v,c)
    matrices.sort(key=len)
    impliedmatrices=[]
    print('')
    print('Restricting to matrices implied by '+str(M1)+'.')
    for M2index in range(0,len(matrices)):
        if sharper(M1,matrices[M2index].copy(),h,v,transform) and sharper(matrices[M2index].copy(),M1,h,v,transform):
            impliedmatrices.append(M2index)
    end = time.time()
    print('Restriction completed. '+str(len(impliedmatrices))+' matrices found.\n')
    Output.append('List of all proper matrices implied by '+str(M1)+', for h='+str(h)+', v='+str(v)+', c='+str(c)+':')
    Output.append(decode([matrices[impliedmatrices[i]] for i in range(0,len(impliedmatrices))])+'\n')
    print('Task (code 3) completed in '+str(int((end-start)))+' seconds.')
def code6(P,Q,h,v):
    start = time.time()
    R=P + list(set(Q) - set(P))
    R.sort()
    transform=initialize(R,h,v)
    Pcopy=P.copy()
    Qcopy=Q.copy()    
    PQ=sharper(P,Qcopy,h,v,transform)
    QP=sharper(Q,Pcopy,h,v,transform)
    end = time.time()
    Output.append('For h='+str(h)+', v='+str(v)+', '+str(P)+'=>'+str(Q)+' is '+str(PQ)+' and '+str(Q)+'=>'+str(P)+' is '+str(QP)+'.\n')
    print('')
    print('Task (code 6) completed in '+str(int((end-start)))+' seconds.')
    return
def code13(codeline,h,v,c):
    start = time.time()
    Output.append('With h='+str(h)+', v='+str(v)+', c='+str(c)+', among the matrices'+decode([codeline[i] for i in range(1,len(codeline)-1)]))
    Output.append('the following are proper matrices:')
    Output.append(decode(proper([codeline[i] for i in range(1,len(codeline)-1)],h,v,c))+'\n')
    end = time.time()
    print('')
    print('Task (code 13) completed in '+str(int((end-start)))+' seconds.')
def code15(h,v,c):
    start = time.time()
    matrices=properd(h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    newtable=trimPoset(table)
    writeTable(newtable,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 15) completed in '+str(int((end-start)))+' seconds.')
def code16(P1,P2,Q,h,v):
    start = time.time()
    R=P1 + P2
    R.sort()
    transform=initialize(R,h,v)
    Qcopy=Q.copy()
    PQ=consharper([P1,P2],Qcopy,h,v,transform)
    end = time.time()
    Output.append('For h='+str(h)+', v='+str(v)+', ['+str(P1)+'/\\'+str(P2)+']=>'+str(Q)+' is '+str(PQ)+'.\n')
    print('')
    print('Task (code 16) completed in '+str(int((end-start)))+' seconds.')
def code17(matrix,h,v,c):
    start = time.time()
    matrices=properimplying(matrix,h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    newtable=trimPoset(table)
    writeTable(newtable,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 17) completed in '+str(int((end-start)))+' seconds.')
def code18(matrix,h,v,c):
    start = time.time()
    matrices=properimplied(matrix,[matrixFor(i,h,v) for i in range(1,2**((v**h)-1))],h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    newtable=trimPoset(table)
    writeTable(newtable,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 18) completed in '+str(int((end-start)))+' seconds.')
def code19(matrix,h,v,c):
    start = time.time()
    matrices=properd(h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    writeClassesFOLDERS(table,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 19) completed in '+str(int((end-start)))+' seconds.')
def code20(matrix,h,v,c):
    start = time.time()
    matrices=properd(h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    writeClassesGIFS(table,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 20) completed in '+str(int((end-start)))+' seconds.')
def code21(P,Q,h,v):
    R=P + list(set(Q) - set(P))
    R.sort()
    transform=initialize(R,h,v)
    start = time.time()
    Output.append('Proof of '+str(P)+'=>'+str(Q)+' with h='+str(h)+', v='+str(v)+':')
    Output.append(matrixProof(P,Q,h,v,transform)+'\n')
    end = time.time()
    print('')
    print('Task (code 21) completed in '+str(int((end-start)))+' seconds.')
def code22(h,v,c):
    start = time.time()
    matrices=properd(h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    newtable=trimPoset(table)
    writeTableNew(newtable,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 22) completed in '+str(int((end-start)))+' seconds.')
def code23(h,v,c):
    start = time.time()
    matrices=properd(h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    newtable=trimPoset(table)
    writeSite(newtable,table,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 23) completed in '+str(int((end-start)))+' seconds.')
def code24(matrix,h,v,c):
    start = time.time()
    matrices=properimplying(matrix,h,v,c)
    table=implicationTable(matrices,h,v,c)
    canonicalRepresentation(table,matrices,h,v)
    newtable=trimPoset(table)
    writeTableNew(newtable,matrices,h,v,c)
    end = time.time()
    print('')
    print('Task (code 24) completed in '+str(int((end-start)))+' seconds.')
def writeTable(table,matrices,h,v,c):
    path = 'Matrices['+str(h)+','+str(v)+','+str(c)+']/'
    try:
        os.mkdir(path)
    except OSError:
        print ("Using the existing folder /%s. Matrices will be saved as image files in this folder." % path)
    else:
        print ("Foler /%s successfully created. Matrices will be saved as image files in this folder." % path)
    Output.append('digraph G{')
    Output.append('graph[imagepath="'+os.getcwd()+'/'+path+'",splines="line",rankdir="LR",dpi = 300];')
    Output.append('node[imagescale=false,fixedsize="false",width="0",height="0",color="gray"];')
    Output.append('edge[arrowhead=vee, arrowsize=0.5];')
    length=len(matrices)
    rowno=rowNumbers(matrices,h,v)
    for i in range(0,length):
        if table[i][length]==i:
            dim1=len(matrices[table[length][i]])
            dim2=rowno[table[length][i]]
            im= Image.new('RGB', (dim1*2,dim2*2))
            rowsofmatrix=[]
            repeat=0
            for j in range(0,h):
                row=rows(matrices[table[length][i]],h,v)[j]
                if row not in rowsofmatrix:
                    for k in range(0,dim1):
                        rowsofmatrix.append(row)
                        im.putpixel((k,j-repeat),(255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1))))
                        im.putpixel((2*dim1-k-1,j-repeat),(255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1))))
                        im.putpixel((k,2*dim2-j+repeat-1),(255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1))))
                        im.putpixel((2*dim1-k-1,2*dim2-j+repeat-1),(255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1))))
                else:
                    repeat=repeat+1
            newim=im.resize((dim1*40,dim2*40), resample=Image.BOX)
            newim.save(path+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.png')
            Output.append(str(i)+' [image="['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.png", label=""];')   

    written=[[0 for j in range(0,length)] for i in range(0,length)]
    for i in range(0,length):
        for j in range(0,length):
                if table[table[i][length]][table[j][length]]==1 and written[table[i][length]][table[j][length]]==0:
                        Output.append(str(i)+' -> '+str(j))
                        written[i][j]=1
    Output.append('}\n')

def writeMatrix(path,matrix,h,v,zoom):
    dim1=len(matrix)
    dim2=nonzerodistinctrowNumber(matrix,h,v)
    im= Image.new('RGB', (dim1*8+1,dim2*8+1))
    rowsofmatrix=[]
    repeat=0
    im.putpixel((dim1*8,0),(150,150,150))
    for j in range(0,h):
        row=rows(matrix,h,v)[j]
        if row not in rowsofmatrix and toNumber(row,dim1,v)!=0:
            im.putpixel((0,j-repeat),(150,150,150))
            for k in range(0,dim1):
                rowsofmatrix.append(row)
                for r in range(0,9):
                    for s in range(0,9):
                        if r==0:
                            im.putpixel((k*8+s,(j-repeat)*8+r),(150,150,150)) 
                        else:
                            if s==0:
                                im.putpixel((k*8,(j-repeat)*8+r),(150,150,150))
                            elif s==8:
                                im.putpixel((k*8+s,(j-repeat)*8+r),(150,150,150))
                            else:
                                im.putpixel((k*8+s,(j-repeat)*8+r),(255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1)),255-(row[k])*int(255/(v-1))))
        else:
            repeat=repeat+1
    for k in range(0,dim1*8+1):
        im.putpixel((k,dim2*8),(150,150,150))
    newim=im.resize(((dim1*8+1)*zoom,(dim2*8+1)*zoom), resample=Image.BOX)
    newim.save(path+'['+str(h)+','+str(v)+']'+str(matrix)+'.png')

def writeTableNew(table,matrices,h,v,c):
    path = 'Matrices['+str(h)+','+str(v)+','+str(c)+']/'
    try:
        os.mkdir(path)
    except OSError:
        print ("Using the existing folder /%s. Matrices will be saved as image files in this folder." % path)
    else:
        print ("Foler /%s successfully created. Matrices will be saved as image files in this folder." % path)
    Output.append('digraph G{')
    Output.append('graph[imagepath="'+os.getcwd()+'/'+path+'",splines="ortho",rankdir="LR",dpi = 300,ranksep="1"];')
    Output.append('node[imagescale=false,fixedsize="false",width="0",height="0",color="gray",shape="plaintext"];')
    Output.append('edge[arrowhead=vee, arrowsize=0.5];')
    length=len(matrices)
    for i in range(0,length):
        if table[i][length]==i:
            writeMatrix(path,matrices[table[length][i]],h,v,7)
            Output.append(str(i)+' [image="['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.png", label=""];')   
    written=[[0 for j in range(0,length)] for i in range(0,length)]
    for i in range(0,length):
        for j in range(0,length):
                if table[table[i][length]][table[j][length]]==1 and written[table[i][length]][table[j][length]]==0:
                        Output.append(str(i)+' -> '+str(j))
                        written[i][j]=1
    Output.append('}\n')
def writeSite(table,untrimmed,matrices,h,v,c):
    path = 'Matrices['+str(h)+','+str(v)+','+str(c)+']/'
    try:
        os.mkdir(path)
    except OSError:
        print ("Using the existing folder /%s. Matrices will be saved as image files in this folder." % path)
    else:
        print ("Foler /%s successfully created. Matrices will be saved as image files in this folder." % path)
    #Output.append('digraph G{')
    #Output.append('graph[imagepath="'+os.getcwd()+'/'+path+'",splines="line",rankdir="LR",dpi = 300];')
    #Output.append('node[imagescale=false,fixedsize="false",width="0",height="0",color="gray"];')
    #Output.append('edge[arrowhead=vee, arrowsize=0.5];')
    length=len(matrices)
    for i in range(0,length):
        if table[i][length]==i:
            #if not os.path.isfile(path+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.mclex'):
            file = open(path+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.mclex','w+')
            file.write('#'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'\n')
            file.write('\n')
            file.write('It seems like this matrix class has not been studied yet.') 
            file = open(path+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.html','w+')
            file.write('<!DOCTYPE html>'+'\n')
            file.write('<html>'+'\n')
            file.write('<body>'+'\n')
            file.write('<center><h1>Matrix class #'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'</h1></center>'+'\n')
            file.write('<center><p><img src="'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.png'+'"></p></center>'+'\n')
            file.write('<center><p><iframe src="'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][i]])+'.mclex'+'" width="90%" height="200"></iframe></p></center>'+'\n')
            file.write('<hr>')
            file.write('<center><h2>'+'immediate ['+str(h)+','+str(v)+','+str(c)+']'+' superclasses</h2></center>'+'\n')
            file.write('<center>'+'\n')
            written=[[0 for j in range(0,length)] for i in range(0,length)]
            for j in range(0,length):
                    if table[table[i][length]][table[j][length]]==1 and written[table[i][length]][table[j][length]]==0:
                        file.write('<a href="['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.html"><img border="1" src="'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.png'+'"></a> ')
                        written[i][j]=1
            file.write('</center>'+'\n')
            file.write('<hr>')
            file.write('<center><h2>'+'immediate ['+str(h)+','+str(v)+','+str(c)+']'+' subclasses</h2></center>'+'\n')
            file.write('<center>'+'\n')
            written=[[0 for j in range(0,length)] for i in range(0,length)]
            for j in range(0,length):
                    if table[table[j][length]][table[i][length]]==1 and written[table[j][length]][table[i][length]]==0:
                        file.write('<a href="['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.html"><img border="1" src="'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.png'+'"></a> ')
                        written[j][i]=1
            file.write('</center>'+'\n')
            file.write('<hr>')
            file.write('<center><h2>'+'equivalent ['+str(h)+','+str(v)+','+str(c)+']'+' presentations</h2></center>'+'\n')
            file.write('<center>'+'\n')
            #written=[[0 for j in range(0,length)] for i in range(0,length)]
            for j in range(0,length):
                    if untrimmed[i][j]==1 and untrimmed[j][i]==1:  #and written[table[j][length]][table[i][length]]==0:
                        file.write('<img alt="'+'['+str(h)+','+str(v)+']'+str(matrices[j])+'" border="1" src="'+'['+str(h)+','+str(v)+']'+str(matrices[j])+'.png'+'">      ')
                        #written[j][i]=1
            file.write('</center>'+'\n')
            file.write('<hr>')
            file.write('<center><h2>'+'all ['+str(h)+','+str(v)+','+str(c)+']'+' superclasses</h2></center>'+'\n')
            file.write('<center>'+'\n')
            written=[[0 for j in range(0,length)] for i in range(0,length)]
            for j in range(0,length):
                    if untrimmed[table[i][length]][table[j][length]]==1 and written[table[i][length]][table[j][length]]==0:
                        file.write('<a href="['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.html"><img border="1" src="'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.png'+'"></a> ')
                        written[i][j]=1
            file.write('</center>'+'\n')
            file.write('<hr>')
            file.write('<center><h2>'+'all ['+str(h)+','+str(v)+','+str(c)+']'+' subclasses</h2></center>'+'\n')
            file.write('<center>'+'\n')
            written=[[0 for j in range(0,length)] for i in range(0,length)]
            for j in range(0,length):
                    if untrimmed[table[j][length]][table[i][length]]==1 and written[table[j][length]][table[i][length]]==0:
                        file.write('<a href="['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.html"><img border="1" src="'+'['+str(h)+','+str(v)+']'+str(matrices[table[length][j]])+'.png'+'"></a> ')
                        written[j][i]=1
            file.write('</center>'+'\n')
            file.write('<hr>')
            file.write('</body>'+'\n')
            file.write('</html>'+'\n')
            file.close
        writeMatrix(path,matrices[i],h,v,2)
def writeClassesFOLDERS(table,matrices,h,v,c):
    print('')
    length=len(matrices)
    for i in range(0,length):
        path = 'EC['+str(h)+','+str(v)+','+str(c)+']/'+str(matrices[table[i][length]])+'/'
        try:
            os.makedirs(path)
            print('Folder '+path+' created.')
        except:
            print('Folder '+path+' already exists. Will save images in this folder.') 
        writeMatrix(path,matrices[i],h,v,2)   
def writeClassesGIFS(table,matrices,h,v,c):
    print('')
    length=len(matrices)
    images=[[] for i in range(0,length)]
    path = 'GIF['+str(h)+','+str(v)+','+str(c)+']/'
    for i in range(0,length):
        try:
            os.makedirs(path)
            print('Folder '+path+' created.')
        except:
            print('Folder '+path+' already exists. Will save images in this folder.')
        dim1=len(matrices[i])
        im= Image.new('RGB', ((v**h-1)*2,h*2))
        for j in range(0,h):
            row=rows(matrices[i],h,v)[j]
            for k in range(0,dim1):
                im.putpixel((v**h-1-dim1+k,j),(200-(row[k])*int(200/(v-1))+50,150-(row[k])*int(150/(v-1)),50-(row[k])*int(50/(v-1))))
                im.putpixel((v**h-1+dim1-k-1,j),(200-(row[k])*int(200/(v-1))+50,150-(row[k])*int(150/(v-1))+50,50-(row[k])*int(50/(v-1))+50))
                im.putpixel((v**h-1-dim1+k,2*h-j-1),(200-(row[k])*int(200/(v-1))+50,150-(row[k])*int(150/(v-1))+50,50-(row[k])*int(50/(v-1))+50))
                im.putpixel((v**h-1+dim1-k-1,2*h-j-1),(200-(row[k])*int(200/(v-1))+50,150-(row[k])*int(150/(v-1))+50,50-(row[k])*int(50/(v-1))+50))
        newim=im.resize(((v**h-1)*40,h*40), resample=Image.BOX)
        images[table[i][length]].append(newim)
    for i in range(0,length):
        if images[i]!=[]:
            images[table[i][length]][0].save(path+'['+str(h)+','+str(v)+']'+str(matrices[i])+'.gif', save_all=True, append_images=images[table[i][length]][1:], optimize=False, duration=500, loop=0)

# User-end functions
#-------------------
TASK=''
file = open('input.mclex','r')
Tasks=file.readlines()
file.close
print('')
print('Running MCLex: '+str(datetime.datetime.now()))
for task in Tasks:
    if task[0]=='>':
        taskread=encode(task)
        print('Executing '+str(taskread[0])+'.')
        if taskread[0][0]==0:
            sys.stdout.write('\033[F')
            sys.stdout.write('\033[K')
        elif taskread[0][0]==1: 
            code1(taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==2:
            code2(taskread[1],taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==3:
            code3(taskread[1],taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==6:
            code6(taskread[1],taskread[2],taskread[0][1],taskread[0][2])
        elif taskread[0][0]==13:
            code13(taskread,taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==15:
            code15(taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==16:
            code16(taskread[1],taskread[2],taskread[3],taskread[0][1],taskread[0][2])
        elif taskread[0][0]==17:
            code17(taskread[1],taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==18:
            code18(taskread[1],taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==19:
            code19(taskread[1],taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==20:
            code20(taskread[1],taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==21:
            code21(taskread[1],taskread[2],taskread[0][1],taskread[0][2])
        elif taskread[0][0]==22:
            code22(taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==23:
            code23(taskread[0][1],taskread[0][2],taskread[0][3])
        elif taskread[0][0]==24:
            code24(taskread[1],taskread[0][1],taskread[0][2],taskread[0][3])
        else:
            print('Task code '+str(taskread[0][0])+' is not recognized.')
        print('')
file = open('output.mclex','a+')
for line in Output:
    file.write(line+'\n')
file.close

