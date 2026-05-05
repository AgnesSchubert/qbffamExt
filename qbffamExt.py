# qbffamExt.py — Version mit zusätzlichen Familien GADGETFAM, AESAT, SUBSETSUM, CLIQUECOLOURING, SUCKRAD

#Copyright (c) 2020 Martina Seidl, Johannes Kepler University Linz, Austria 
#Copyright (c) 2026 Agnes Schleitzer, Friedrich Schiller University Jena, Germany

#Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated 
#documentation files (the “Software”), to deal in the Software without restriction, including without 
#limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of 
#the Software, and to permit persons to whom the Software is furnished to do so, subject to the following 
#conditions:

#The above copyright notice and this permission notice shall be included in all copies or substantial 
#portions of the Software.

#THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED 
#TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL 
#THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF 
#CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER 
#DEALINGS IN THE SOFTWARE.

from pyeda.inter import *
from pyeda.boolalg.expr import expr2dimacscnf
from itertools import product, combinations
from typing import Iterable, Dict, Tuple, Set
import math
import argparse
import sys

def error(message):
    print(f"Error:\n  {message}", file=sys.stderr)
    sys.exit(1)

def EQ (n):

    if n < 2:
        error ("EQ expects size >= 2")

    print("p cnf " + str (3*n) + " " + str (2*n+1))

    # print the prefix

    print(("e"), end=' ')

    for i in range (n): 
        print(str (i+1), end=' ')

    print((0))

    print(("a"), end=' ')

    for i in range (n): 
        print(str (i+n+1), end=' ')

    print((0))
 
    print(("e"), end=' ')

    for i in range (n): 
        print(str (i+2*n+1), end=' ')

    print((0))

    # print the matrix

    for i in range (n): 
        print(str (i+1) + " " + str (i+n+1) + " -" + str (i+2*n+1), end=' ')
        print("0")
        print("-" + str (i+1) + " -" + str (i+n+1) + " -" + str (i+2*n+1), end=' ')
        print("0")

    for i in range (n): 
        print((i+2*n+1), end=' ')

    print("0")


# equality square formulas from 
# Olaf Beyersdorff, Joshua Blinkhorn, Meena Mahajan:
# Building Strategies into QBF Proofs. STACS 2019: 14:1-14:18
def EQ2 (n): 

    if n < 2:
        error ("EQ2 expects size >= 2")

    print("p cnf " + str (4*n+n*n) + " " + str (4*n*n+1))

    print("e", end=' ') 

    for i in range (n): 
        print(str (i+1) + " " + str (n+i+1), end=' ')

    print ("0")

    print("a", end=' ') 

    for i in range (n): 
        print(str (2*n+i+1) + " " + str (3*n+i+1), end=' ')
    
    print ("0")

    print("e", end=' ')

    for i in range (n): 
        for j in range (n): 
            print(str (4*n + i*n + j + 1), end=' ')

    print ("0")

    # print the matrix

    for i in range (n): 
        for j in range (n):
            print(str (i+1) + " " + str (n + j + 1), end=' ') 
            print(str (2 * n + i + 1) + " " + str (3 * n + j + 1), end=' ')
            print(str (4 * n + i * n + j + 1), end=' ')
            print ("0")

            print(str (i+1) + " -" + str (n + j + 1), end=' ') 
            print(str (2 * n + i + 1) + " -" + str (3 * n + j + 1), end=' ')
            print(str (4 * n + i * n + j + 1), end=' ')
            print ("0")
            
            print("-" + str (i+1) + " " + str (n + j + 1), end=' ') 
            print("-" + str (2 * n + i + 1) + " " + str (3 * n + j + 1), end=' ')
            print(str (4 * n + i * n + j + 1), end=' ')
            print ("0")

            print("-" + str (i+1) + " -" + str (n + j + 1), end=' ') 
            print("-" + str (2 * n + i + 1) + " -" + str (3 * n + j + 1), end=' ')
            print(str (4 * n + i * n + j + 1), end=' ')
            print ("0")

    for i in range (n): 
        for j in range (n): 
         print("-" + str (4*n + i*n + j + 1), end=' ') 
    print(0)

# CR formulas
# Mikolas Janota:
#On Q-Resolution and CDCL QBF Solving. SAT 2016: 402-418
def CR (n): 
    if n < 2:
        error ("CR expects size >= 2")


    print("p cnf " + str ((n+2) * n + 1) + " " + str (2 * n * n + 2)) 


    print("e", end=' ') 

    z = str ((n+2) * n +1)

    for i in range (n):
        for j in range (n): 
            print(str(i * n + j + 1), end=' ')
    print(0)
        
    print("a " + z + " 0")

    print("e", end=' ')

    for i in range (n): 
        print(str (n*n+i+1) + " " + str((n+1)*n+i+1), end=' ')
    print(0)

    for i in range (n):
        for j in range (n): 
            print(str (i*n+j+1) + " " + z + " " +str (n*n+i+1) + " 0")
            print("-" + str (i*n+j+1) + " -" + z + " " +str ((n+1)*n+j+1) + " 0")

    for i in range (n): 
        print("-" + (str (n*n+i+1)), end=' ')
    print("0")

    for i in range (n): 
        print("-" + (str ((n+1)*n+i+1)), end=' ')
    print("0")

# trapdoor formulas
# Olaf Beyersdorff, Benjamin Boehm:
# Understanding the Relative Strength of QBF CDCL Solvers and QBF Resolution. Electronic Colloquium on Computational Complexity (ECCC) 27: 53 (2020)
def TRAP (n) : 

    print("p cnf " + str ((n+1)*n*2 + 3) + " " + str (n * (n+1) * (n+1)  - (n-1)* (n+1) + 6 * n*(n+1)))

    w = str ((n+1)*n*2+1)
    u = str ((n+1)*n*2+2)
    t = str ((n+1)*n*2+3)

    print("e", end=' ')

    for i in range ((n+1)*n):
        print(str ((n+1)*n+i+1), end=' ')
    print("0")
    print("a " + w + " 0")
    print("e "+ t, end=' ') 
    for i in range ((n+1)*n):
        print(str (i+1), end=' ')
    print("0")
    print("a " + u + " 0")

    # matrix

    # pigeon hole

    for i in range (n+1): 
        for j in range (n): 
            print(str (i*n + j +1), end=' ') 
        print("0")

    for j in range (n): 
        for i1 in range (n+1): 
            for i2 in range (n+1) :
                if i1 != i2: 
                    print("-" + str (i1*n+j+1) + " -" + str (i2*n+j+1) + " 0")

    # rest
    for i in range (n*(n+1)): 
        o = n*(n+1)
        print("-" + str (i+1) + " " + str (o + i + 1) + " " + u + " 0")
        print(str (i+1) + " -" + str (o + i + 1) + " " + u + " 0")

        print(str (o+i+1) + " " + w + " " + t + " 0")
        print("-" + str (o+i+1) + " " + w + " " + t + " 0")
        print(str (o+i+1) + " -" + w + " " + t + " 0")
        print(str (o+i+1) + " " + w + " -" + t + " 0")

# PhD thesis of Florian Lonsing, JKU Linz, 2012 
def LONSING (n): 

    print("p cnf " + str (n * (n+1) + 6) + " " + str (n + 1 + n * (n+1) * (n+1) - (n * (n+1))+5))

    a = str (n * (n+1) + 1)
    b = str (n * (n+1) + 2)
    c = str (n * (n+1) + 3)
    d = str (n * (n+1) + 4)
    x = str (n * (n+1) + 5)
    y = str (n * (n+1) + 6)

    print("e" + " " + a + " " +b, end=' ')

    for i in range ((n+1)*n):
        print(str (i+1), end=' ')

    print("0")

    print("a " + x + " " + y + " 0") 
    print("e " + c + " " + d + " 0") 

    # pigeon hole

    for i in range (n+1): 
        for j in range (n): 
            print(str (i*n + j +1), end=' ') 
        print("0")

    for j in range (n): 
        for i1 in range (n+1): 
            for i2 in range (n+1) :
                if i1 != i2: 
                    print("-" + str (i1*n+j+1) + " -" + str (i2*n+j+1) + " 0")

    print(a + " " + x + " " + c + " 0")

    print(a + " " + b, end=' ') 
    for i in range (n * (n+1)): 
        print(i+1, end=' ')
    print(0)

    print(b + " " + y + " " + d + " 0")


    print(x + " " + c + " 0")
    print(x + " -" + c + " 0")



# Blocked equality formulas
# Joshua Blinkhorn, Olaf Beyersdorff:
# Proof Complexity of QBF Symmetry Recomputation. SAT 2019: 36-52
def blocked_EQ (n):

    if n < 2:
        error ("Blocked-EQ expects size >= 2")

    print("p cnf " + str (6*n+2) + " " + str (2*n+1+3*n+1))

    # print the prefix

    a = str (6*n+1)
    c = str (6*n+2)

    print(("e"), end=' ')


    print(a, end=' ')

    for i in range (3*n): 
        print(str (3*n + i + 1), end=' ')

    for i in range (n): 
        print(str (i+1), end=' ')

    print((0))

    print(("a"), end=' ')

    for i in range (n): 
        print(str (i+n+1), end=' ')

    print((0))
 
    print(("e"), end=' ')

    for i in range (n): 
        print(str (i+2*n+1), end=' ')

    print((0))

    print("a " + c + " 0")

    # print the matrix

    for i in range (n): 
        print(str (i+1) + " " + str (i+n+1) + " -" + str (i+2*n+1), end=' ')
        print("-" + a + " " + c + " 0")
        print("-" + str (i+1) + " -" + str (i+n+1) + " -" + str (i+2*n+1), end=' ')
        print("-" + a + " " + c + " 0")

    for i in range (n): 
        print((i+2*n+1), end=' ')
    print("-" + a + " " + c + " 0")

    print(a + " 0")

    for i in range (3 * n): 
        for j in range (i+1): 
            print((3*n + j +1), end=' ') 
        print((i+1), end=' ')
        print("0")


def printXOR (x, y, z): 

    print("-" + str (x) + " -" + str (y) + " -" + str (z) + " 0")
    print("-" + str (x) + " " + str (y) + " " + str (z) + " 0")
    print(str (x) + " -" + str (y) + " " + str (z) + " 0")
    print(str (x) + " " + str (y) + " -" + str (z) + " 0")



# parity formulas 
# Olaf Beyersdorff, Leroy Chew, Mikolas Janota:
# New Resolution-Based QBF Calculi and Their Proof Complexity. TOCT 11(4): 26:1-26:42 (2019)

def PARITY (n): 

    print("p cnf " + str (n*2) + " " + str (4 * (n-1) + 2))

    print("e", end=' ') 

    for i in range (n):
        print(str (i+1), end=' ') 

    print("0")

    z = str (n+1)

    print("a " + z + " 0")

    print("e", end=' ') 
    for i in range (n-1): 
        print(str (n + i + 2), end=' ')

    print("0")

    printXOR (1, 2, n+2)

    for i in range (n-2): 
        printXOR (n+i+2, i+3, n+i+3)
 
    print(z + " " + str (2 * n) + " 0")
    print("-" + z + " -" + str (2 * n) + " 0")


def PARITYTrue (n):
    print("p cnf " + str (n*2) + " " + str (4 * (n-1) + 2))

    print("a", end=' ') 

    for i in range (n):
        print(str (i+1), end=' ') 

    print("0")

    z = str (n+1)

    print("e " + z + " 0")

    print("e", end=' ') 
    for i in range (n-1): 
        print(str (n + i + 2), end=' ')

    print("0")

    printXOR (1, 2, n+2)

    for i in range (n-2): 
        printXOR (n+i+2, i+3, n+i+3)
 
    print(z + " " + str (2 * n) + " 0")
    print("-" + z + " -" + str (2 * n) + " 0")


def printXORl (x, y, z, a): 

    print("-" + str (x) + " -" + str (y) + " -" + str (z) + " " + str (a) + " 0")
    print("-" + str (x) + " " + str (y) + " " + str (z) + " " + str (a) + " 0")
    print(str (x) + " -" + str (y) + " " + str (z) + " " + str (a) + " 0")
    print(str (x) + " " + str (y) + " -" + str (z) + " " + str (a) + " 0")



# LD-parity formulas 
# Olaf Beyersdorff, Leroy Chew, Mikolas Janota:
# New Resolution-Based QBF Calculi and Their Proof Complexity. TOCT 11(4): 26:1-26:42 (2019)

def LQ_PARITY (n): 

    print("p cnf " + str (n*2) + " " + str (8 * (n-1) + 2))

    print("e", end=' ') 

    for i in range (n):
        print(str (i+1), end=' ') 

    print("0")

    z = (n+1)

    print("a " + str(z) + " 0")

    print("e", end=' ') 
    for i in range (n-1): 
        print(str (n + i + 2), end=' ')

    print("0")

    printXORl (1, 2, n+2, z)
    printXORl (1, 2, n+2, -z)

    for i in range (n-2): 
        printXORl (n+i+2, i+3, n+i+3, z)
        printXORl (n+i+2, i+3, n+i+3, -z)
 
    print(str(z) + " " + str (2 * n) + " 0")
    print("-" + str(z) + " -" + str (2 * n) + " 0")


def printXORu (x, y, z, a, b): 

    print("-" + str (x) + " -" + str (y) + " -" + str (z) + " " + str (a) + " " + str (b) +" 0")
    print("-" + str (x) + " " + str (y) + " " + str (z) + " " + str (a) + " " + str (b) + " 0")
    print(str (x) + " -" + str (y) + " " + str (z) + " " + str (a) + " " + str (b) + " 0")
    print(str (x) + " " + str (y) + " -" + str (z) + " " + str (a) + " " + str (b) + " 0")



# QU-parity formulas 
# Olaf Beyersdorff, Leroy Chew, Mikolas Janota:
# New Resolution-Based QBF Calculi and Their Proof Complexity. TOCT 11(4): 26:1-26:42 (2019)
def QU_PARITY (n): 

    print("p cnf " + str (n*2+1) + " " + str (8 * (n-1) + 2))

    print("e", end=' ') 

    for i in range (n):
        print(str (i+1), end=' ') 

    print("0")

    z1 = (n+1)
    z2 = (2*n+1)

    print("a " + str(z1) + " " + str (z2) + " 0")

    print("e", end=' ') 
    for i in range (n-1): 
        print(str (n + i + 2), end=' ')

    print("0")

    printXORu (1, 2, n+2, z1, z2)
    printXORu (1, 2, n+2, -z1, -z2)

    for i in range (n-2): 
        printXORu (n+i+2, i+3, n+i+3, z1, z2)
        printXORu (n+i+2, i+3, n+i+3, -z1, -z2)
 
    print(str(z1) + " " + str(z2) + " " + str (2 * n) + " 0")
    print("-" + str(z1) + " -" + str (z2) + " -" + str (2 * n) + " 0")





#Valeriy Balabanov, Magdalena Widl, Jie-Hong R. Jiang:
#QBF Resolution Systems and Their Proof Complexities. SAT 2014: 154-169
def KBKF_QU (n): 

    print("p cnf " + str (5 * n) +  " " + str (4*n+1))  

    for i in range (n): 
        print("e " + str (n + i +1) + " " + str (2*n +i +1) + " 0")
        print("a " + str (i+1) + " " + str (4*n+i+1) + " 0")

    print("e", end=' ') 
    for i in range (n): 
        print(str (3*n + i + 1), end=' ') 
    print("0")


    for i in range (n-1):
        print(str (n + i + 1) + " " + str (i+1) + " " + str (4*n+i + 1), end=' ') 
        print("-" + str (n+i+2) + " -" + str (2*n+i+2) + " 0")
 
        print(str (2*n + i + 1) + " -" + str (i+1) + " -" + str (4*n+i+1), end=' ') 
        print("-" + str (n+i+2) + " -" + str (2*n+i+2) + " 0")

    print(str (n + n) + " " + str (n) + " " + str (5*n), end=' ') 

    for i in range (n): 
        print("-" + str (3 * n + i + 1), end=' ') 
    print("0")

    print(str (2*n + n) + " -" + str (n) + " -" + str (5*n), end=' ') 

    for i in range (n): 
        print("-" + str (3 * n + i + 1), end=' ') 
    print("0")

    for i in range (n): 

        print(str (i+1) + " " + str (4*n+i+1) + " " +str (3*n+i+1) + " 0")
        print("-" + str (i+1) +" -" + str (4*n+i+1)+ " " + str (3*n+i+1) + " 0")

    print("-" + str (n + 1) + " -" + str (2*n + 1) + " 0")

#kleine buening et al. Q-Resolution Paper

#------------------------------------------------------------------------
#true KBKF formulas
def KBKFTrue (n):
   
    #counter for variables (first number - variable count)
    counter = 0
    # counter for initial variables
    counter2 = 0
 
    allvariables = 8*n+1
    
    print("p cnf " + str(8*n+1) + " " + str(14*n-1))

    for i in range (n): 
        print("a " + str (n + i +1) + " " + str (2*n +i +1) + " 0")
        print("e " + str (i+1) + " 0")
        counter += 3
        counter2 += 3

    print("a", end=' ')
    for i in range (n): 
        print(str (3*n + i + 1), end=' ') 
        counter += 1
        counter2 += 1
    print("0")

    newlyGvariables = allvariables - counter2

    print("e", end=' ')
    for i in range(newlyGvariables):
        print(str(counter2+i+1), end=' ')
    print("0")

    for i in range (n-1):
        
        print("-" + str(counter+1) + " -" + str (n + i + 1) + " 0")
        print("-" + str(counter+1) + " -" + str (i+1) + " 0")
        print("-" + str(counter+1) + " " + str (n+i+2) + " 0")
        print("-" + str(counter+1) + " " + str (2*n+i+2) + " 0")
        counter += 1

        print("-" + str(counter+1) + " -" + str (2*n + i + 1)+ " 0")
        print("-" + str(counter+1) + " " + str (i+1) + " 0")
        print("-" + str(counter+1) + " " + str (n+i+2) + " 0")
        print("-" + str(counter+1) + " " + str (2*n+i+2) + " 0")
        counter += 1

    print("-" + str(counter+1) + " -" + str (n + n)+ " 0")
    print("-" + str(counter+1) + " -" + str (n)+ " 0")
    
    for i in range (n): 
        print("-" + str(counter+1) + " " + str (3 * n + i + 1) + " 0") 
        
    counter += 1
    print("-" + str(counter+1) + " -" + str (2*n + n) + " 0")
    print("-" + str(counter+1) + " " + str (n) + " 0")

    for i in range (n): 
        print("-" + str(counter+1) + " " + str (3 * n + i + 1) + " 0") 
        
    counter += 1
    
    for i in range (n): 

        print("-" + str(counter+1) + " -" + str (i+1)+ " 0")
        print("-" + str(counter+1) + " -" + str (3*n+i+1)+ " 0")
        counter += 1

        print("-" + str(counter+1) + " " + str (i+1) + " 0")
        print("-" + str(counter+1) + " -" + str (3*n+i+1) + " 0")
        counter += 1

    print("-" + str(counter+1) + " " + str (n + 1) + " 0")
    print("-" + str(counter+1) + " " + str (2*n + 1) + " 0")
    
    for i in range(newlyGvariables):
        print(str(counter2+i+1), end=' ')
    print("0")
   
   
#------------------------------------------------------------------------
#true KBKF formulas with reordered quantifiers
def KBKFQRE (n):
   
    #counter for variables (first number - variable count)
    counter = 0
    # counter for initial variables
    counter2 = 0
 
    allvariables = 8*n+1
    originalVariables = 4*n
    
    
    print("p cnf " + str(8*n+1) + " " + str(14*n-1))

    for i in range (n): 
        print("a " + str (n + i +1) + " " + str (2*n +i +1) + " 0")
        if(i < 1):
            print("e " + str(allvariables) + " 0")
        else:
            print("e "+ str(originalVariables+1) + " " + str(originalVariables+2) + " 0") 
            originalVariables = originalVariables+2
        print("e " + str (i+1) + " 0")
        counter += 3
        counter2 += 3

    

    tempCounter = originalVariables + 3
    lastVar = 0
    for i in range (n-1): 
        print("a " + str (3*n + i + 1) + " 0") 
        lastVar = 3*n + i + 1
        print("e " + str(tempCounter) + " " + str(tempCounter+1) + " 0")
        tempCounter = tempCounter + 2
        counter += 1
        counter2 += 1
    
    counter = counter +1
    counter2 = counter2 +1
    newlyGvariables = allvariables - counter2
    
    print("a " + str(lastVar + 1) + " 0")

    print("e " + str(originalVariables+1) + " " + str(originalVariables+2) + " " + str(tempCounter) + " " + str(tempCounter+1) + " 0")

    for i in range (n-1):
        
        print("-" + str(counter+1) + " -" + str (n + i + 1) + " 0")
        print("-" + str(counter+1) + " -" + str (i+1) + " 0")
        print("-" + str(counter+1) + " " + str (n+i+2) + " 0")
        print("-" + str(counter+1) + " " + str (2*n+i+2) + " 0")
        counter += 1

        print("-" + str(counter+1) + " -" + str (2*n + i + 1)+ " 0")
        print("-" + str(counter+1) + " " + str (i+1) + " 0")
        print("-" + str(counter+1) + " " + str (n+i+2) + " 0")
        print("-" + str(counter+1) + " " + str (2*n+i+2) + " 0")
        counter += 1

    print("-" + str(counter+1) + " -" + str (n + n)+ " 0")
    print("-" + str(counter+1) + " -" + str (n)+ " 0")
    
    for i in range (n): 
        print("-" + str(counter+1) + " " + str (3 * n + i + 1) + " 0") 
        
    counter += 1
    print("-" + str(counter+1) + " -" + str (2*n + n) + " 0")
    print("-" + str(counter+1) + " " + str (n) + " 0")

    for i in range (n): 
        print("-" + str(counter+1) + " " + str (3 * n + i + 1) + " 0") 
        
    counter += 1
    
    for i in range (n): 

        print("-" + str(counter+1) + " -" + str (i+1)+ " 0")
        print("-" + str(counter+1) + " -" + str (3*n+i+1)+ " 0")
        counter += 1

        print("-" + str(counter+1) + " " + str (i+1) + " 0")
        print("-" + str(counter+1) + " -" + str (3*n+i+1) + " 0")
        counter += 1

    print("-" + str(counter+1) + " " + str (n + 1) + " 0")
    print("-" + str(counter+1) + " " + str (2*n + 1) + " 0")
    
    for i in range(newlyGvariables):
        print(str(counter2+i+1), end=' ')
    print("0")
 

#kleine buening et al. Q-Resolution Paper
def KBKF (n): 

    print("p cnf " + str (4 * n) +  " " + str (4*n+1))  

    for i in range (n): 
        print("e " + str (n + i +1) + " " + str (2*n +i +1) + " 0")
        print("a " + str (i+1) + " 0")

    print("e", end=' ') 
    for i in range (n): 
        print(str (3*n + i + 1), end=' ') 
    print("0")


    for i in range (n-1):
        print(str (n + i + 1) + " " + str (i+1), end=' ') 
        print("-" + str (n+i+2) + " -" + str (2*n+i+2) + " 0")
 
        print(str (2*n + i + 1) + " -" + str (i+1), end=' ') 
        print("-" + str (n+i+2) + " -" + str (2*n+i+2) + " 0")

    print(str (n + n) + " " + str (n), end=' ') 

    for i in range (n): 
        print("-" + str (3 * n + i + 1), end=' ') 
    print("0")

    print(str (2*n + n) + " -" + str (n), end=' ') 

    for i in range (n): 
        print("-" + str (3 * n + i + 1), end=' ') 
    print("0")

    for i in range (n): 

        print(str (i+1) + " " + str (3*n+i+1) + " 0")
        print("-" + str (i+1) + " " + str (3*n+i+1) + " 0")

    print("-" + str (n + 1) + " -" + str (2*n + 1) + " 0")

#Valeriy Balabanov, Magdalena Widl, Jie-Hong R. Jiang:
#QBF Resolution Systems and Their Proof Complexities. SAT 2014: 154-169
def KBKF_LD (n): 

    print("p cnf " + str (4 * n) +  " " + str (4*n+1))  

    for i in range (n): 
        print("e " + str (n + i +1) + " " + str (2*n +i +1) + " 0")
        print("a " + str (i+1) + " 0")

    print("e", end=' ') 
    for i in range (n): 
        print(str (3*n + i + 1), end=' ') 
    print("0")


    for i in range (n-1):
        print(str (n + i + 1) + " " + str (i+1), end=' ') 
        print("-" + str (n+i+2) + " -" + str (2*n+i+2), end=' ') 

        for j in range (n): 
            print("-" + str (3*n + j +1), end=' ')
        print("0")
 
        print(str (2*n + i + 1) + " -" + str (i+1), end=' ') 
        print("-" + str (n+i+2) + " -" + str (2*n+i+2), end=' ')
        
        for j in range (n): 
            print("-" + str (3*n + j +1), end=' ')
        print("0")

    print(str (n + n) + " " + str (n), end=' ') 

    for i in range (n): 
        print("-" + str (3 * n + i + 1), end=' ') 
    print("0")

    print(str (2*n + n) + " -" + str (n), end=' ') 

    for i in range (n): 
        print("-" + str (3 * n + i + 1), end=' ') 
    print("0")

    for i in range (n): 

        print(str (i+1) + " " + str (3*n+i+1), end=' ') 
        for j in range (n-i-1): 
            print("-" + str (3*n+i+j+2), end=' ')
        print("0")


        print("-" + str (i+1) + " " + str (3*n+i+1), end=' ')
        for j in range (n-i-1): 
            print("-" + str (3*n+i+j+2), end=' ')
        print("0")

    print("-" + str (n + 1) + " -" + str (2*n + 1), end=' ')
    for j in range (n): 
        print("-" + str (3*n + j +1), end=' ')
    print("0")
    
#-------------------------------------------------------------------------------------
# Schleitzer, Beyersdorff — Gadget Construction
#
# A QBF family is obtained by taking a propositional base formula (SC / IC / EC)
# and connecting each "critical" clause with a QBF gadget (EQ / XOR).
# The gadget variables are divided into the leading existential and the following 
# universal block of the quantifier prefix, while the base variables form the 
# final existential block.

# --------------- input validation helpers ---------------

def checkBase(base):
    """
    Validate the base-formula identifier.

    Parameters:
        base (str): One of 'SC' (single clause), 'IC' (implication chain),
                    'EC' (equality chain).

    Returns:
        str: The validated base string.

    Raises:
        SystemExit: If base is not one of the valid choices.
    """
    valid = {'SC', 'IC', 'EC'}
    if base not in valid:
        error(f"{base} is not a valid base formula (choose from SC, IC, EC)")
    return base

def checkGadget(gadget):
    """
    Validate the gadget identifier.

    Parameters:
        gadget (str): One of 'EQ' (equality gadget) or 'XOR' (XOR gadget).

    Returns:
        str: The validated gadget string.

    Raises:
        SystemExit: If gadget is not one of the valid choices.
    """
    valid = {'EQ', 'XOR'}
    if gadget not in valid:
        error(f"{gadget} is not a valid gadget (choose from EQ, XOR)")
    return gadget

def checkN(n):
    """
    Validate and coerce the size parameter n.

    Parameters:
        n: Value to be interpreted as a positive integer.

    Returns:
        int: The validated size parameter >= 1.

    Raises:
        SystemExit: If n cannot be converted to a positive integer.
    """
    try:
        n = int(n)
        if n < 1:
            raise ValueError
    except ValueError:
        error("n must be an integer greater than 0")
    return n

# --------------- output helpers ---------------

def mapLiterals(l, s):
    """
    Shift a literal by an offset s while preserving its sign.

    Parameters:
        l (int): Literal (positive = variable, negative = negated variable).
        s (int): Positive integer offset to add to the absolute variable index.

    Returns:
        int: Shifted literal with the original sign.
    """
    return l+s if l > 0 else l-s
    
def printQBF(variables, clauses, e1, u1, e2, formula):
    """
    Print a three-block QBF (∃e1 ∀u1 ∃e2) in QDIMACS format.

    Empty quantifier blocks are silently omitted.

    Parameters:
        variables (int): Total number of variables.
        clauses   (int): Total number of clauses.
        e1  (iterable of int): Outermost existential variables.
        u1  (iterable of int): Universal variables.
        e2  (iterable of int): Innermost existential variables.
        formula (iterable of frozenset): Set of clauses, each a frozenset of literals.

    Output:
        QDIMACS representation printed to stdout.
    """
    print(f"p cnf {variables} {clauses}")
    if e1:
        print("e", *sorted(e1), 0)
    if u1:
        print("a", *sorted(u1), 0)
    if e2:
        print("e", *sorted(e2), 0)
    for c in formula:
        print(*sorted(c), 0)
        
# --------------- base-formula constructors ---------------
# Each returns: (variables, clauses, critical_clauses, other_clauses)
# where critical_clauses is the set of clauses to be combined with gadgets.

def constructSC(n):
    """
    Construct the SC (Simple Contradiction) base formula of size n.

    The formula has one large clause {1,…,n} ("others") and n unit-clause
    negations {-i} ("critical"). Variables: 1…n.

    Parameters:
        n (int): Number of propositional variables.

    Returns:
        tuple: (variables, clauses, critical, others)
            variables (int): n
            clauses   (int): n+1
            critical  (set of frozenset): unit clauses {-i} for i=1..n
            others    (set of frozenset): the single positive clause {1..n}
    """
    variables = n
    clauses = n+1
    others = {frozenset(range(1, n+1))}
    critical = {frozenset({-i}) for i in range(1, n+1)}
    return variables, clauses, critical, others

def constructIC(n):
    """
    Construct the IC (Implication Chain) base formula of size n.

    Encodes a chain -i → -(i+1) with boundary conditions -1 and n-1.
    Variables: 1…n-1.

    Parameters:
        n (int): Chain length; formula uses n-1 variables.

    Returns:
        tuple: (variables, clauses, critical, others)
            variables (int): n-1
            clauses   (int): n
            critical  (set of frozenset): implication and boundary clauses
            others    (set of frozenset): empty set
    """
    variables = n-1
    clauses = n
    others = set()
    critical = {frozenset({i, -(i+1)}) for i in range(1, n-1)}
    critical.add(frozenset({-1}))
    critical.add(frozenset({n-1}))
    return variables, clauses, critical, others

def constructEC(n):
    """
    Construct the EC (Equivalence Chain) base formula of size n.

    Encodes a cyclic equivalence chain i ↔ (i+1) over n+1 variables
    with boundary condition not(1 ↔ (n+1)).

    Parameters:
        n (int): Chain length; formula uses n+1 variables.

    Returns:
        tuple: (variables, clauses, critical, others)
            variables (int): n+1
            clauses   (int): 2n+2
            critical  (set of frozenset): one-directional implication clauses
            others    (set of frozenset): reverse implication and boundary clauses
    """
    variables = n+1
    clauses = 2*n+2
    others = {frozenset({-i, i+1}) for i in range(1, n+1)}
    others |= {frozenset({1, n+1}), frozenset({-1, -(n+1)})}
    critical = {frozenset({i, -(i+1)}) for i in range(1, n+1)}
    return variables, clauses, critical, others

# --------------- gadget constructors ---------------
# Each returns: (variables, clauses, existential_vars, universal_vars, gadget_clauses)

def constructEQ():
    """
    Construct the EQ (equality) gadget.

    Encodes x ↔ u using two clauses: {x,u} and {-x,-u}.
    Variable x is existential, variable u is universal.

    Returns:
        tuple: (variables, clauses, existential, universal, gadgetClauses)
    """
    variables = 2
    clauses = 2
    existential = {1}
    universal = {2}
    gadgetClauses = {frozenset({1,2}), frozenset({-1,-2})}
    return variables, clauses, existential, universal, gadgetClauses

def constructXOR():
    """
    Construct the XOR gadget.

    Encodes u = x_1 XOR x_2 using four clauses. Variables x_1,x_2 are existential,
    variable u (the universal witness) is universal.

    Returns:
        tuple: (variables, clauses, existential, universal, gadgetClauses)
    """
    variables = 3
    clauses = 4
    existential = {1,2}
    universal = {3}
    gadgetClauses = {
        frozenset({1,2,3}), frozenset({1,-2,-3}),
        frozenset({-1,2,-3}), frozenset({-1,-2,3})
    }
    return variables, clauses, existential, universal, gadgetClauses

# --------------- dispatch helpers ---------------

def constructBase(base, n):
    """
    Dispatch to the appropriate base-formula constructor.

    Parameters:
        base (str): One of 'SC', 'IC', 'EC'.
        n (int): Size parameter passed to the constructor.

    Returns:
        tuple: (variables, clauses, critical, others) as returned by the constructor.
    """
    if base == 'SC':
        return constructSC(n)
    elif base == 'IC':
        return constructIC(n)
    else:
        return constructEC(n)

def constructGadget(gadget):
    """
    Dispatch to the appropriate gadget constructor.

    Parameters:
        gadget (str): One of 'EQ', 'XOR'.

    Returns:
        tuple: (variables, clauses, existential, universal, gadgetClauses).
    """
    if gadget == 'EQ':
        return constructEQ()
    else:
        return constructXOR()
        
def constructFormula(base, gadget, n):
    """
    Assemble the full GADGETFAM QBF by replacing each critical clause of the
    base formula with a combination of clause and gadget.

    For each of the n critical clauses, a fresh copy of the gadget is created
    (with variables offset to avoid collisions) and its clauses are merged with
    the critical clause into the formula. The gadget's existential and universal
    variables are collected into e1 and u1 respectively; the base variables
    form e2 (innermost existential block).

    Parameters:
        base   (str): Base-formula identifier ('SC', 'IC', or 'EC').
        gadget (str): Gadget identifier ('EQ' or 'XOR').
        n      (int): Size parameter passed to the base-formula constructor.

    Returns:
        tuple: (variables, clauses, e1, u1, e2, formula)
            variables (int): Total variable count.
            clauses   (int): Total clause count.
            e1  (set of int): Outermost existential variables (gadget existentials).
            u1  (set of int): Universal variables (gadget universals).
            e2  (set of int): Innermost existential variables (base variables).
            formula (set of frozenset): Complete set of clauses.
    """
    base, gadget, n = checkBase(base), checkGadget(gadget), checkN(n)
    pVars, pClauses, critical, others = constructBase(base, n)  # propositional (base)
    gVars, gClauses, gExist, gUniv, gClausesSet = constructGadget(gadget)  # gadget

    variables = pVars + n * gVars
    clauses = pClauses - n + n * gClauses
    formula = set(others)
    varCount = pVars
    # base variables go into the innermost existential block
    e1, u1, e2 = set(), set(), set(range(1, pVars+1))

    for _ in range(n):
        if not critical:
            break
        p = critical.pop()
        # merge each gadget clause (shifted) with the current critical base clause
        for g in gClausesSet:
            g = {mapLiterals(l, varCount) for l in g}
            c = g | p
            formula.add(frozenset(c))
        # register the shifted gadget variables in the appropriate quantifier blocks
        e1 |= {x+varCount for x in gExist}
        u1 |= {x+varCount for x in gUniv}
        varCount += gVars

    return variables, clauses, e1, u1, e2, formula


def GADGETFAM(base, gadget, n):
    """
    Generate a GADGETFAM QBF formula and print it in QDIMACS format.

    Parameters:
        base   (str): Base formula identifier ('SC', 'IC', or 'EC').
        gadget (str): Gadget identifier ('EQ' or 'XOR').
        n      (int): Size parameter for the base formula.

    Output:
        QDIMACS representation printed to stdout.
    """
    v, c, e1, u1, e2, f = constructFormula(base, gadget, n)
    printQBF(v, c, e1, u1, e2, f)
        
#-------------------------------------------------------------------------------------
# Schleitzer, Beyersdorff — Formulas from computationally hard problems


# --------------- All-Equal-3SAT ---------------
def constructCriticalAESAT(n):
    """
    Build the critical All-Equal-\exists\forall-3SAT instance of size n.

    Parameters:
        n (int): Number of clauses / triple groups.

    Returns:
        tuple: (cnf, x, y)
            cnf (set of frozenset): The n clauses.
            x   (set of int): Existential variable indices.
            y   (set of int): Universal variable indices.
    """
    cnf = set()
    x = set()
    y = set()
    for i in range(1, n+1):
        cnf.add(frozenset({3*i-2, 3*i-1, -(3*i)}))
        x = x.union({3*i-2, 3*i-1})
        y.add(3*i)
    return cnf, x, y

def selectClause(i, variables, length):
    ''' 
    generates the set negChi of selector variables for a number i in [0, n-1] with log n (=selVar) bits
    b -> Binary representation of i
    Bit b_j = 1 → -j in negChi
    Bit b_j = 0 → j in negChi
    '''
    
    negChi = set()
    for j in range(length):
        # Check whether the j^th bit of i is set (from the right)
        if (i >> j) & 1:
            negChi.add(-(variables+j+1))
        else:
            negChi.add(variables+j+1)
    return negChi            

def constructAESAT(cnf, x, y):
    """
    Parameters:
        cnf (set of frozenset): The input 3-CNF clauses (from constructCriticalAESAT).
        x   (set of int):       Existential variable indices in cnf.
        y   (set of int):       Universal variable indices in cnf.

    Returns:
        tuple: (variables, clauses, e1, u1, e2, formula)
            variables (int): Total variable count (original + selector vars).
            clauses   (int): Total clause count.
            e1  (set of int): Outermost existential (x).
            u1  (set of int): Universal (y).
            e2  (set of int): Innermost existential (selector variables).
            formula (set of frozenset): Complete clause set.
    """
    e1 = x
    u1 = y
    clauses = len(cnf)
    variables = max(abs(var) for clause in cnf for var in clause)
    
    selVar = math.ceil(math.log2(clauses))
    # e2 contains the ⌈log₂ n⌉ selector variables
    e2 = set(range(variables+1, variables+selVar+1))
    
    cnf_list = list(cnf)
    
    f = set()
    for i, cnfClause in enumerate(cnf_list[:clauses]):
        # Compute the negated binary selector for clause index i
        negChi = selectClause(i, variables, selVar)
        
        # All-Equal constraint: all three literals have the same truth value.
        # Sorted to obtain a deterministic l1 < l2 < l3 ordering.
        l1, l2, l3 = sorted(cnfClause)
        # (l1 = l3) ∧ (l1 = l2) encoded as four implication clauses guarded by negChi
        f.add(frozenset(negChi.union({l1, -l3})))
        f.add(frozenset(negChi.union({l1, -l2})))
        f.add(frozenset(negChi.union({-l1, l2})))
        f.add(frozenset(negChi.union({-l1, l3})))

    # Treatment of redundant indices (if n is not a Power of Two):
    for j in range(clauses, pow(2, selVar)):
        negChi = selectClause(j, variables, selVar)
        f.add(frozenset(negChi))
        
    return variables+selVar, len(f), e1, u1, e2, f
    
def AllEqualSAT(n):
    """
    Generate the AESAT QBF formula family and print in QDIMACS format.

    Constructs the critical 3-CNF instance for n clauses, lifts it to a QBF
    using the All-Equal selector encoding, and outputs the result.

    Parameters:
        n (int): Number of (propositional) clauses.

    Output:
        QDIMACS representation printed to stdout.
    """
    # create the critical propositional 3-CNF instance
    cnf, x, y = constructCriticalAESAT(n)
    
    # TODO: alternatively, read an external CNF (must be verified to be 3-CNF first)
    
    v, c, e1, u1, e2, f = constructAESAT(cnf, x, y)
    printQBF(v, c, e1, u1, e2, f)
    
# --------------- Succinct-k-Radius ---------------
def constructCriticalSUCKRAD(n, k):
    """
    Build the symbolic QBF formula for the Succinct-k-Radius problem.

    The formula encodes: for a graph with rows 0…n-1 and columns 0…k+1,
    there is a k-center P[0] in the graph, such that every valid vertex P[k] 
    has a witnessing path of length k from P[0] through k-1 intermediate 
    vertices P[1]…P[k-1].

    Vertex coordinates are stored as bit-vectors (r: row, c: column).
    A Tseitin transformation is applied to obtain CNF; the resulting Tseitin
    auxiliary variables are placed in the innermost existential block.

    Parameters:
        n (int): Number of rows (grid height); must be >= 2.
        k (int): Path length / radius; must be > 2.

    Returns:
        tuple: (v, c, e1, u1, e2, f)
            v   (int): Total variable count.
            c   (int): Clause count.
            e1  (list): Outermost existential variables (start vertex P[0]).
            u1  (list): Universal variables (target vertex P[k]).
            e2  (list): Innermost existential variables (intermediate vertices + Tseitin).
            f   (And): Tseitin-transformed CNF formula (PyEDA).
    """
    bits_r = math.ceil(math.log2(n))
    bits_c = math.ceil(math.log2(k + 2))
    
    # Create bit-vector variables for each of the k+1 path vertices
    P = []
    for i in range(k + 1):
        P.append({
            'r': exprvars(f"p_{i}_r", bits_r),  # row bits
            'c': exprvars(f"p_{i}_c", bits_c)   # column bits
        })    
        
    # Sub-formulas used to build the matrix
    def is_valid(i):
        """Return formula asserting vertex i is within grid bounds (r <= n-1, c <= k+1)."""
        r, c = P[i]['r'], P[i]['c']
        cond = formula_leq(r, n-1) & formula_leq(c, k + 1)
        return cond

    def has_edge(i, j):
        """Return formula asserting an edge exists between vertices i and j."""
        r1, c1 = P[i]['r'], P[i]['c']
        r2, c2 = P[j]['r'], P[j]['c']
        
        # Chain edge: same row, adjacent columns
        same_row = formula_bitwise_eq(r1, r2)
        neighbouring_columns = Or(formula_inc(c1, c2), formula_inc(c2, c1))
        chain = And(same_row, neighbouring_columns)
        
        # Shortcut edge: different rows, columns are 0 and 2 (or vice versa)
        shortcut1 = formula_eq_const(c1, 0) & formula_eq_const(c2, 2)
        shortcut2 = formula_eq_const(c1, 2) & formula_eq_const(c2, 0)
        shortcut = And(~same_row, Or(shortcut1, shortcut2))
            
        return Or(chain, shortcut)
        
    def is_equal_vertice(i, j):
        """Return formula asserting vertices i and j are at identical coordinates."""
        eq_r = formula_bitwise_eq(P[i]['r'], P[j]['r'])
        eq_c = formula_bitwise_eq(P[i]['c'], P[j]['c'])
        return And(eq_r, eq_c)

    # Assemble the matrix:
    # The universal vertex P[k] must be valid; if so, there must exist a valid
    # path P[0]…P[k] where consecutive vertices are equal or connected by an edge.
    valid_start = is_valid(0)
    valid_end = is_valid(k)
    valid_path = And(*[is_valid(i) for i in range(1,k)])
    is_path = And(*[Or(is_equal_vertice(i-1, i),
                       has_edge(i-1, i)) for i in range(1, k+1)])                  
    
    matrix = And(valid_start,Implies(valid_end, And(valid_path, is_path)))
    
    # Assign quantifier blocks: P[0] = outermost ∃, P[k] = ∀, P[1..k-1] = inner ∃
    e1 = list(P[0]['r']) + list(P[0]['c'])
    u1 = list(P[k]['r']) + list(P[k]['c'])
    e2 = []
    for i in range(1, k):
        e2 += list(P[i]['r']) + list(P[i]['c'])

    # Apply Tseitin transformation to obtain CNF; add auxiliary variables to e2
    f = matrix.tseitin()
    c = len(f.xs)
    
    all_vars = f.support
    all_primary = set().union(set(e1), set(u1), set(e2))
    new_vars = all_vars - all_primary  # Tseitin auxiliary variables
    e2 = list(e2) + list(new_vars)
    
    v = len(e1) + len(u1) + len(e2)
    
    return v, c, e1, u1, e2, f

def formula_leq(binVars, val):
    """
    Build a PyEDA formula asserting that a bit-vector is <= an integer constant.

    Traverses bits from MSB to LSB. At each bit position where val has a 1-bit,
    there is a chance for binVars to be strictly less (current bit = 0); otherwise
    equality must hold at that position to keep the comparison viable.

    Parameters:
        binVars (tuple/list of Expr): Bit-vector variables, MSB-first.
        val (int): Non-negative integer upper bound.

    Returns:
        Expr: PyEDA formula that is true iff binVars <= val.
    """
    bits = len(binVars)
    or_terms = []
    current_eq = expr(1)
    
    for i in range(bits - 1, -1, -1):
        bit_val = (val >> i) & 1
        if bit_val == 1:
            # If val's bit is 1: binVars < val if current bit is 0 (strict), else continue
            or_terms.append(current_eq & ~binVars[i])
            current_eq &= binVars[i]
        else:
            # If val's bit is 0: binVars must also be 0 at this position; otherwise > val
            current_eq &= ~binVars[i]
    
    # If all bits matched exactly, binVars == val, which satisfies <=
    return Or(current_eq, *or_terms)

def formula_eq_const(binVars, val):
    """
    Build a PyEDA formula asserting that a bit-vector equals an integer constant.

    Parameters:
        binVars (tuple/list of Expr): Bit-vector variables (LSB at index 0).
        val (int): Non-negative integer to compare against.

    Returns:
        Expr: Conjunction of literals enforcing binVars == val bit by bit.
    """
    bits = []
    for i in range(len(binVars)):
        if (val >> i) & 1:
            bits.append(binVars[i])
        else:
            bits.append(~binVars[i])
    return And(*bits)

def formula_inc(vars1, vars2):
    """
    Build a PyEDA formula asserting vars2 == vars1 + 1 (no overflow).

    Implements a one-bit ripple-carry increment. The carry is initialised to 1
    (adding one). An explicit no-overflow constraint is added to prevent wrap-around.

    Parameters:
        vars1 (tuple/list of Expr): Input bit-vector (LSB at index 0).
        vars2 (tuple/list of Expr): Output bit-vector, same length (LSB at index 0).

    Returns:
        Expr: Formula that is true iff vars2 == vars1 + 1 and there is no carry-out.
    """
    bits = len(vars1)
    constraints = []
    carry = [None] * (bits + 1)
    carry[0] = expr(1)  # initial carry-in of 1 (i.e. we are adding 1)
    
    for i in range(bits):
        # Result bit: vars2[i] = vars1[i] XOR carry[i]
        constraints.append(vars2[i] == (vars1[i] ^ carry[i]))
        # Propagate carry: carry[i+1] = vars1[i] AND carry[i]
        carry[i+1] = vars1[i] & carry[i]
    
    # Reject overflow (e.g. 111…1 + 1 would produce 000…0 with carry-out 1)
    no_overflow = ~carry[bits]
    
    return And(no_overflow, *constraints)
    
def formula_bitwise_eq(vars1, vars2):
    """
    Build a PyEDA formula asserting two bit-vectors are equal.

    Parameters:
        vars1, vars2 (tuple/list of Expr): Bit-vectors of equal length (LSB at index 0).

    Returns:
        Expr: Conjunction of bit-wise equality constraints.
    """
    return And(*[vars1[i] == vars2[i] for i in range(len(vars1))])
    
def SuccinctKRadius(n, k):
    """
    Generate the SUCKRAD (Succinct-k-Radius) QBF formula family and print QDIMACS output.

    Parameters:
        n (int): Grid height (number of rows); must be >= 2.
        k (int): Path radius; must be > 2.

    Output:
        QDIMACS representation printed to stdout.
    """
    (v, c, e1, u1, e2, f) = constructCriticalSUCKRAD(n, k)
    GenerateQBF(v, c, e1, u1, e2, f)
    
# --------------- k-Clique Colouring ---------------
def qbf_clique_colouring(graph_edges, n, k):
    """
    Build the symbolic QBF formula CC_k(G) for the Clique-Colouring problem.

    The formula encodes: B is a proper k-colouring AND
    [(G[C] is a maximal clique) → (T ⊆ C has exactly 2 vertices with different colours)].

    Variable roles:
        B[v][c]  (existential e1): vertex v has colour c.
        C[v]     (universal  u1): vertex v is in the considered clique.
        T[v]     (existential e2): vertex v is one of the two witness vertices.

    The formula matrix is: f1 ∧ ((f2 ∧ f3) → (f4 ∧ f5 ∧ f6)), where:
        f1: B is a proper k-colouring (each vertex has exactly one colour).
        f2: C is a clique (no non-edge within C).
        f3: C is maximal (every non-C vertex has a non-neighbour in C).
        f4: T \subseteq C.
        f5: |T| = 2 (T selects exactly two vertices).
        f6: The two T-vertices have different colours.

    A Tseitin transformation is applied; Tseitin auxiliary variables go into e2.

    Parameters:
        graph_edges (list of (int, int)): Edge list with 0 ≤ u < v < n.
        n (int): Number of vertices.
        k (int): Number of colours.

    Returns:
        tuple: (v, c, e1, u1, e2, f)
            v   (int): Total variable count.
            c   (int): Clause count.
            e1  (list): Colour variables (B).
            u1  (list): Clique indicator variables (C).
            e2  (list): Witness + Tseitin variables (T + auxiliaries).
            f   (And): Tseitin CNF formula (PyEDA).
    """
    # Build symmetric adjacency matrix
    A = [[0]*n for _ in range(n)]
    for u, v in graph_edges:
        A[u][v] = 1
        A[v][u] = 1

    # Variable creation
    # B[v][c]: vertex v has colour c  (v = 0..n-1, c = 0..k-1)
    B = [[exprvar(f"b_{v}_{c}") for c in range(k)]
         for v in range(n)]

    # C[v]: vertex v is in the considered clique
    C = [exprvar(f"c_{v}") for v in range(n)]

    # T[v]: vertex v is one of the two witnesses
    T = [exprvar(f"t_{v}") for v in range(n)]

    # (1) B is a proper k-colouring: each vertex has at least one and at most one colour
    f1_parts = []

    # At least one colour: ∨_c B[v][c]
    for v in range(n):
        f1_parts.append(Or(*B[v]))

    # At most one colour: for each pair (c, d) with c < d: ¬B[v][c] ∨ ¬B[v][d]
    for v in range(n):
        for c in range(k):
            for d in range(c+1, k):
                f1_parts.append(Or(Not(B[v][c]), Not(B[v][d])))

    f1 = And(*f1_parts)

    # (2) C is a clique: for every non-edge {u,v}, ¬c_u ∨ ¬c_v
    f2_parts = []
    for u in range(n):
        for v in range(u+1, n):
            if A[u][v] == 0:
                f2_parts.append(Or(Not(C[u]), Not(C[v])))

    f2 = And(*f2_parts) if f2_parts else 1  # trivially true for complete graphs

    # (3) C is maximal: every non-C vertex u has at least one non-neighbour in C
    f3_parts = []
    for u in range(n):
        right = []
        for v in range(n):
            if u != v and A[u][v] == 0:
                right.append(C[v])
        if right:
            f3_parts.append(Implies(Not(C[u]), Or(*right)))
        else:
            # u is adjacent to all other vertices → u must be in C
            f3_parts.append(C[u])

    f3 = And(*f3_parts)

    # (4) T ⊆ C: t_v → c_v
    f4 = And(*[Implies(T[v], C[v]) for v in range(n)])

    # (5) Exactly two vertices selected by T:
    #   at most two: for every triple u<v<w, ¬t_u ∨ ¬t_v ∨ ¬t_w
    #   at least two: there exist u<v with t_u ∧ t_v
    f5_at_most = And(*[Or(Not(T[u]), Not(T[v]), Not(T[w]))
                       for u, v, w in combinations(range(n), 3)])
    f5_at_least = Or(*[And(T[u], T[v]) for u, v in combinations(range(n), 2)])
    f5 = And(f5_at_least, f5_at_most)

    # (6) The two selected witnesses must have different colours:
    #   (t_u ∧ t_v) → (∀c: ¬B[u][c] ∨ ¬B[v][c])
    f6_parts = []
    for u in range(n):
        for v in range(u+1, n):
            left = And(T[u], T[v])
            for c in range(k):
                right = Or(Not(B[u][c]), Not(B[v][c]))
                f6_parts.append(Implies(left, right))

    f6 = And(*f6_parts)

    # Final matrix: Ψ = f1 ∧ ((f2 ∧ f3) → (f4 ∧ f5 ∧ f6))
    f23 = And(f2, f3)
    f456 = And(f4, f5, f6)

    f = And(f1, Implies(f23, f456)).tseitin()
    
    # Collect variables into flat lists for quantifier assignment
    flat_B = [var for row in B for var in row]
    flat_C = list(C)
    flat_T = list(T)
    
    c = len(f.xs)
    
    all_vars = f.support
    new_vars = all_vars - set().union(flat_B, flat_C, flat_T)  # Tseitin auxiliaries
    e1 = flat_B
    u1 = flat_C
    e2 = flat_T + list(new_vars)
    
    v = len(e1) + len(u1) + len(e2)

    return v, c, e1, u1, e2, f

def generate_grotzsch_family(n):
    """
    Generate the graph family G_n used for the CliqueColouring formula family.

    G_1 is the Grötzsch graph (11 vertices, 20 edges). For i >= 2, G_i is built
    inductively by attaching a G^ips_3 graph to G_{i-1}: three special vertices
    (u, v', w) of the G^ips_3 are each connected to every existing vertex.

    Parameters:
        n (int): Family index; n=1 returns the plain Grötzsch graph.

    Returns:
        tuple: (V, E)
            V (list of int): Vertex IDs.
            E (list of (int, int)): Edge list.
    """
    # G_1 = Grötzsch graph: 11 vertices (0-10), 20 edges
    V = list(range(11))
    E = [
        (0,1),(0,2),(0,3),(0,4),(0,5),
        (1,7),(1,10),
        (2,6),(2,8),
        (3,7),(3,9),
        (4,8),(4,10),
        (5,6),(5,9),
        (6,7),(7,8),(8,9),(9,10),(10,6)
    ]
    
    next_vertex_id = 11  # first free vertex ID for inductively added vertices
    vertex_cover = {0,6,7,8,9,10}

    # Inductive step: attach one G^ips_3 gadget per level
    for i in range(1, n):
        (V_gips, E_gips, next_vertex_id, gips_u, gips_vprime, gips_w) = generate_gips3(next_vertex_id)
        
        # Connect every existing vertex to each of the three special new vertices
        for old in V:
            for new in (gips_u, gips_vprime, gips_w):
                E.append((old, new))
        
        V.extend(V_gips)
        E.extend(E_gips)

    return V, E
    
def generate_gips3(next_vertex_id):
    """
    Generate a G^ips_3 graph (two Grötzsch-minus-edge copies plus a linking vertex).

    Consists of two copies of the Grötzsch graph with the edge (9,10) removed,
    connected as: u – v (across copies), u' – w – v' (through a new vertex w).

    Parameters:
        next_vertex_id (int): First free global vertex ID; all new vertices are
                              assigned IDs starting from this value.

    Returns:
        tuple: (V_complete, E_complete, next_vertex_id, vert_u, vert_vprime, vert_w)
            V_complete (list of int): All 23 new vertex IDs.
            E_complete (list of (int, int)): All internal edges.
            next_vertex_id (int): Updated first free ID after this graph.
            vert_u      (int): Special vertex u (copy 1, node 9).
            vert_vprime (int): Special vertex v' (copy 2, node 10).
            vert_w      (int): Linking vertex w.
    """
    V = list(range(11))
    # Grötzsch graph with the edge (9,10) removed
    E = [
        (0,1),(0,2),(0,3),(0,4),(0,5),
        (1,7),(1,10),
        (2,6),(2,8),
        (3,7),(3,9),
        (4,8),(4,10),
        (5,6),(5,9),
        (6,7),(7,8),(8,9),(10,6)
    ]
    
    # First copy: nodes 9 → u, 10 → u'
    V1 = [v + next_vertex_id for v in V]
    vert_u = V1[9]
    vert_uprime = V1[10]
    
    # Second copy: nodes 9 → v, 10 → v'
    V2 = [v + next_vertex_id+11 for v in V]
    vert_v = V2[9]
    vert_vprime = V2[10]
    
    # Single linking vertex w
    V3 = [next_vertex_id+22]
    vert_w = V3[0]
    
    # Shift each copy's internal edges to the new global IDs
    E1 = [(u + next_vertex_id, v + next_vertex_id) for (u,v) in E]
    E2 = [(u + next_vertex_id+11, v + next_vertex_id+11) for (u,v) in E]
    # Cross-copy connections: u–v, u'–w, w–v'
    E3 = [
        (vert_u, vert_v),
        (vert_uprime, vert_w),
        (vert_w, vert_v)
    ]
    
    V_complete = V1 + V2 + V3
    E_complete = E1 + E2 + E3
    
    next_vertex_id = next_vertex_id + 11 + 11 + 1  # 23 new vertices consumed
    
    return (V_complete, E_complete, next_vertex_id, vert_u, vert_vprime, vert_w)
    
def CliqueColouring(n):
    """
    Generate the CLIQUECOLOURING QBF formula family and print QDIMACS output.

    Uses the n-th Grötzsch graph induction graph as the critical instance and k=3 colours.

    Parameters:
        n (int): Family index for the Grötzsch graph induction (1 = plain Grötzsch graph).

    Output:
        QDIMACS representation printed to stdout.
    """
    (V, E) = generate_grotzsch_family(n)
    k = 3  # number of colours (3-colourability is the hard case for Grötzsch graphs)
    (v, c, e1, u1, e2, f) = qbf_clique_colouring(E, len(V), k)
    GenerateQBF(v, c, e1, u1, e2, f)
   
# -------------- Generalised Subsetsum ----------------
def int_to_bits(x: int, L: int) -> list[int]:
    """
    Convert a non-negative integer to its LSB-first binary representation.
 
    Parameters:
        x (int): Non-negative integer to convert.
        L (int): Number of output bits (zero-padded or truncated to this length).
 
    Returns:
        list[int]: List of L bits (0 or 1), least-significant bit first.
    """
    return [(x >> i) & 1 for i in range(L)]
 
# -------------------------
# Ripple-carry adder (symbolic)
# -------------------------
def ripple_carry_addition(A: list, B: list, prefix: str):#, carry_in: bool = False):
    """
    Build symbolic ripple-carry adder that enforces Sum = A + B.
    A, B: length-L-lists of PyEDA variables or constants (0/1 ints) or mixed; LSB-first.
    prefix: name prefix for generated sum and carry variables.
    Returns:
        sum_bits: list of sum bit Expr variables (length = L)
        carry_out: final carry out Expr variable
        formula: conjunction (And) enforcing full-adder relationships
    Note: result width L = max(len(A), len(B))
    """
    L = max(len(A), len(B))
    # normalize to length L
    def get_bit(arr, i):
        if i < len(arr):
            return arr[i]
        else:
            return 0  # constant zero
 
    # create sum and carry variables
    s = [exprvar(f"{prefix}_s_{i}") for i in range(L)]
    c = [exprvar(f"{prefix}_c_{i}") for i in range(L+1)]  # c[0] initial carry, c[L] final carry
 
    # Build constraints
    subformulas = []
    #subformulas.append(Equal(c[0], carry_in))  # c[0] is incoming carry
    subformulas.append(Equal(c[0], 0))  # c[0] must be 0 for plain addition (no incoming carry)
 
    for i in range(L):
        a_i = get_bit(A, i)
        b_i = get_bit(B, i)
        # sum bit: s_i = a_i XOR b_i XOR c_i
        sum_expr = (a_i ^ b_i ^ c[i])
        subformulas.append(Equal(s[i], sum_expr))
 
        # carry_out: c[i+1] = (a_i&b_i) | (a_i&c_i) | (b_i&c_i)
        carry_expr = ( (a_i & b_i) | (a_i & c[i]) | (b_i & c[i]) )
        subformulas.append(Equal(c[i+1], carry_expr))
 
    # final outputs
    formula = And(*subformulas)
    return s, c[L], formula  # sum bits, final carry out, formula
 
# -------------------------
# Add constant conditionally: if sel then add(const_bits) else add 0
# Implemented by creating B' = [sel & const_bit_i] and using ripple_adder
# -------------------------
def conditional_add_constant(acc_bits: list, const_bits: list[int], sel, prefix: str):
    """
    Return new_acc_bits, carry_out, formula enforcing:
        new_acc = acc + (sel ? const : 0)
    acc_bits: list of Expr variables LSB-first
    const_bits: list of ints (0/1) LSB-first
    sel: Expr variable (0/1)
    prefix: naming prefix for created variables
    """
    # create masked bits = sel & const_bits[i]
    masked = []
    for i, cb in enumerate(const_bits):
        if cb == 0:
            masked.append(0)
        else:
            # cb==1: masked_i = sel
            masked.append(sel)
    # If const_bits shorter than acc_bits, masked implicit zeros for higher bits
    # use ripple_carry_addition
    return ripple_carry_addition(acc_bits, masked, prefix)
 
# -------------------------
# Sum selected constants: given vector U (list of ints) and selection bits X (Expr vars),
# compute Z bits representing sum = sum_i X_i * U_i
# -------------------------
def sum_selected_constants(U: list[int], X: list, out_bits: int, prefix: str):
    """
    U: list of integers (each fits in <= out_bits)
    X: list of selector Expr variables (same length)
    out_bits: output bit width (LSB-first)
    prefix: prefix for internal vars
    Returns:
        Z_bits: list of Expr vars (length out_bits) representing sum
        formula: conjunction encoding the iterative additions
    """
    # initialize accumulator bits to zeros (we create Expr vars for acc)
    acc = [exprvar(f"{prefix}_acc_{i}") for i in range(out_bits)]
    # force initial acc == 0
    init_clauses = []
    for b in acc:
        init_clauses.append(Equal(b, 0))
    clauses = [And(*init_clauses)]

    current_acc = acc
    # for each i: current_acc := current_acc + (X[i] ? U[i] : 0)
    for i, ui in enumerate(U):
        const_bits = int_to_bits(ui, out_bits)
        # create new sum bits for the addition
        sum_bits, carry_out, add_formula = conditional_add_constant(current_acc, const_bits, X[i], f"{prefix}_add_{i}")
        # add_formula ensures sum_bits + carry_out represent addition; we need to replace current_acc by sum_bits extended appropriately
        # But ripple_carry_addition returned sum_bits length = out_bits (as L = max lengths)
        clauses.append(add_formula)
        # Now set current_acc := sum_bits (we must identify these vars with next iteration acc variables)
        # To avoid renaming/aliasing complexity, we set current_acc = sum_bits (i.e., use sum_bits as accumulator)
        current_acc = sum_bits

    # final accumulator is current_acc
    Z = current_acc
    formula = And(*clauses)
    return Z, formula
 
# -------------------------
# Not-equal-to-constant formula
# Return formula that is TRUE iff bits != t
# -------------------------
def not_equal_constant(bits: list, t: int):
    L = len(bits)
    t_bits = int_to_bits(t, L)
    eq_clauses = []
    for i in range(L):
        if t_bits[i] == 1:
            eq_clauses.append(bits[i])
        else:
            eq_clauses.append(~bits[i])
    # eq_all is true iff bits == t
    eq_all = And(*eq_clauses)
    return ~eq_all  # true iff not equal
 
# -------------------------
# Top-level GSS formula builder
# -------------------------
def build_gss_qbf(U: list[int], V: list[int], t: int, n_bits: int):
    """
    builds the symbolic (non-CNF) PyEDA formula for GeneralisedSubsetSum instance:
        exists X forall Y exists Z : (sum(U * X) + sum(V * Y) != t)
 
    U: list of k integers (u_i), each assumed to fit in n_bits bits
    V: list of l integers (v_i), each assumed to fit in n_bits bits
    t: integer target, assumed to fit in n_bits bits
    n_bits: bit width to represent u_i, v_i, t
 
    returns a dict with:
        matrix: PyEDA Expr
        vars_exists_X: list of Expr variables for X selectors
        vars_forall_Y: list of Expr variables for Y selectors
        vars_exists_Z: list of Expr variables for Z output bits
        meta: dictionary with bit widths etc.
    """
    k = len(U)
    l = len(V)
    m = max(k, l)
 
    # choose output width: n + ceil(log2 m) + 1 (safe bound for sums)
    out_bits = n_bits + math.ceil(math.log2(max(1, m))) + 1
 
    # create selector variables
    X = [exprvar(f"x_{i}") for i in range(k)]
    Y = [exprvar(f"y_{i}") for i in range(l)]
 
    # Create Z1 (sum U·X), Z2 (sum V·Y), Z3 final sum
    Z1 = [exprvar(f"z1_{i}") for i in range(out_bits)]
    Z2 = [exprvar(f"z2_{i}") for i in range(out_bits)]
    Z3 = [exprvar(f"z3_{i}") for i in range(out_bits+1)]  # allow possible final carry -> one extra bit
 
    # Build formulas that enforce Z1 == sum(U*X) and Z2 == sum(V*Y)
    # We'll compute sums as intermediate accumulators and equate final accumulator to Z1/Z2
    sum1_bits, sum1_formula = sum_selected_constants(U, X, out_bits, "Usum")
    # force sum1_bits == Z1
    eq1 = And(*[Equal(sum1_bits[i], Z1[i]) for i in range(out_bits)])
 
    sum2_bits, sum2_formula = sum_selected_constants(V, Y, out_bits, "Vsum")
    eq2 = And(*[Equal(sum2_bits[i], Z2[i]) for i in range(out_bits)])
 
    # Add Z1 + Z2 -> Z3 (Z3 length out_bits+1)
    sum12_bits, carry12, add12_formula = ripple_carry_addition(Z1, Z2, "ADD12")
    # sum12_bits length = out_bits, carry12 is final carry -> compose Z3
    eq_add = And(*[Equal(sum12_bits[i], Z3[i]) for i in range(out_bits)] + [Equal(carry12, Z3[out_bits])])
 
    # inequality: Z3 != t  (t must fit into out_bits+1)
    neq_formula = not_equal_constant(Z3, t)
 
    # combine everything
    matrix = And(sum1_formula, eq1, sum2_formula, eq2, add12_formula, eq_add, neq_formula)
 
    return {
        "matrix": matrix,
        "vars_exists_X": X,
        "vars_forall_Y": Y,
        "vars_exists_Z": Z1 + Z2 + Z3,
        "meta": {
            "out_bits": out_bits,
            "k": k,
            "l": l
        }
    }
 
def ConstructCriticalSubsetSum(n):
    """
    Build the critical Generalised Subset Sum QBF instance of size n.
 
    Uses U = V = [1, 2, 4, …, 2^(n-1)] (powers of two) and target t = 2^n - 1,
    so that X*sum(U)+Y*sum(V) = t exactly when the bits of Y are complemetary
    to them of X.  This makes the QBF hard: the universal player must match 
    whatever assignment the existential player picks.
 
    Applies a Tseitin transformation; Tseitin variables are added to e2.
 
    Parameters:
        n (int): length of U,V / number of selector variables per player.
 
    Returns:
        tuple: (v, c, e1, u1, e2, f)
            v   (int): Total variable count.
            c   (int): Clause count.
            e1  (list of Expr): Outermost existential variables (X selectors).
            u1  (list of Expr): Universal variables (Y selectors).
            e2  (list of Expr): Innermost existential variables (Z bits + Tseitin).
            f   (And): Tseitin CNF formula (PyEDA).
    """
    V_vec = [2**i for i in range(n)]
    U_vec = V_vec.copy()
    t = 2**n - 1
    
    result = build_gss_qbf(U_vec, V_vec, t, n)
    matrix = result["matrix"]
    e1 = result["vars_exists_X"]
    u1 = result["vars_forall_Y"]
    e2 = result["vars_exists_Z"]
    v = len(e1) + len(u1) + len(e2)  
    f = matrix.tseitin()
    c = len(f.xs)
   
    # Collect Tseitin auxiliary variables and add them to the innermost ∃ block
    all_vars = f.support
    new_vars = all_vars - set().union(e1, u1, e2)
    e2 = list(e2) + list(new_vars)
    
    v = len(e1) + len(u1) + len(e2)
    return (v, c, e1, u1, e2, f)
    
def GeneralisedSubsetSum(n):
    """
    Generate the SUBSETSUM QBF formula family and print QDIMACS output.
 
    Parameters:
        n (int): length of the U, V vectors.
 
    Output:
        QDIMACS representation printed to stdout.
    """
    (v, c, e1, u1, e2, f) = ConstructCriticalSubsetSum(n)
    GenerateQBF(v, c, e1, u1, e2, f)
 


def GenerateQBF(v, c, e1, u1, e2, f):
    """
    Convert a PyEDA formula with a three-block quantifier prefix to QDIMACS and print it.

    Maps PyEDA variable objects to DIMACS integer indices via expr2dimacscnf,
    then prints the p-line, quantifier blocks (non-empty only), and clause lines.

    Parameters:
        v   (int): Total variable count.
        c   (int): Clause count.
        e1  (iterable of Expr): Outermost existential variables.
        u1  (iterable of Expr): Universal variables.
        e2  (iterable of Expr): Innermost existential variables.
        f   (And): Tseitin CNF (PyEDA) — the matrix of the QBF.

    Output:
        QDIMACS representation printed to stdout.
    """
    v_map, f = expr2dimacscnf(f)
    f_string = str(f)
    
    # Translate PyEDA variable objects to their DIMACS integer IDs
    e1 = [v_map[var] for var in e1]
    u1 = [v_map[var] for var in u1]
    e2 = [v_map[var] for var in e2]
    
    print(f"p cnf {v} {c}")
    if e1:
        print("e", *sorted(e1), 0)
    if u1:
        print("a", *sorted(u1), 0)
    if e2:
        print("e", *sorted(e2), 0)
    
    # Strip the "p cnf …" header line that expr2dimacscnf includes in its string output
    lines = f_string.splitlines()
    lines_without_first = lines[1:]                 # cut off the first line
    dimacs_new = "\n".join(lines_without_first)     # reassemble as a string
    print(dimacs_new)

# --------------- CLI entry point ---------------
# Families are dispatched here after argument parsing.
# "Old" families require exactly one size argument.
# "New" families may require additional arguments (see per-family checks below).
parser = argparse.ArgumentParser(description='Generate QBF formulas for specified families.')
parser.add_argument('family', type=str, help='Family name to generate')
parser.add_argument('size', type=int, nargs='?', help='Size parameter for the family')
parser.add_argument('extra', nargs='*', help='Extra parameters for certain families (e.g. GADGETFAM)')

args = parser.parse_args()

families = {
    # Original families (Seidl et al.)
    "EQ":        EQ,
    "EQ2":       EQ2,
    "CR":        CR,
    "TRAP":      TRAP,
    "LONSING":   LONSING,
    "BEQ":       blocked_EQ,
    "PARITY":    PARITY,
    "LQ_PARITY": LQ_PARITY,
    "QU_PARITY": QU_PARITY,
    "KBKF":      KBKF,
    "KBKF_QU":   KBKF_QU,
    "KBKF_LD":   KBKF_LD,
    "KBKFTRUE":  KBKFTrue,
    "PARITYTRUE":PARITYTrue,
    "KBKFQRE":   KBKFQRE,
    # Extended families (Schleitzer, Beyersdorff)
    "GADGETFAM":      GADGETFAM,
    "AESAT":          AllEqualSAT,
    "SUCKRAD":        SuccinctKRadius,
    "CLIQUECOLOURING":CliqueColouring,
    "SUBSETSUM":      GeneralisedSubsetSum,
}
# Sets used for documentation / help messages
oldFamilies = {'EQ','EQ2','CR','TRAP','LONSING','BEQ','PARITY','LQ_PARITY','QU_PARITY','KBKF','KBKF_QU','KBKF_LD','KBKFTRUE','PARITYTRUE','KBKFQRE'}
newFamilies = {'GADGETFAM','AESAT','SUCKRAD','CLIQUECOLOURING','SUBSETSUM'}

family = args.family.upper()

if family not in families:
    error(f'unknown family "{family}". Use -h to list available families.')
elif family == 'GADGETFAM':
    if args.size is None or len(args.extra) != 2:
        error("GADGETFAM requires 3 arguments: <size> <base> <gadget>")
    base, gadget = args.extra[0], args.extra[1]
    if base == 'IC' and args.size < 2:
        error(f'for base "{base}" size has to be >1')
    GADGETFAM(base, gadget, args.size)
elif family == 'SUCKRAD':
    if args.size is None or len(args.extra) != 1:
        error("SUCKRAD requires 2 arguments: <size> <radius>")
    try:
        k = int(args.extra[0])
    except ValueError:
        error("For SUCKRAD, the second argument must be an integer radius.")
    if args.size < 2 or k <= 2:
        error("SUCKRAD requires a size of at least 2 and a radius of at least 3.")
    SuccinctKRadius(args.size, k)
elif family in {'AESAT', 'CLIQUECOLOURING', 'SUBSETSUM'}:
    if args.size is None or len(args.extra) != 0:
        error(f'"{family}" requires exactly 1 argument: <size>')
    families[family](args.size)
else:
    if args.size is None:
        error(f'Family "{family}" requires a size parameter')
    families[family](args.size)