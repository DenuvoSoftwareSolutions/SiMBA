#!/usr/bin/python3

import io
import sys
import time
import random
import re
try: import z3
except ModuleNotFoundError: pass

from simplify import simplify_linear_mba


# Get the name of the i-th variable.
def get_vname(i):
    return "X[" + str(i) + "]"

# Verify that the given expressions are equivalent using Z3.
def verify_mba_unsat(expr1, expr2, bitCount):
    if expr1 == expr2:
        return True

    # List of variables including multiple occurences.
    varList1 = re.findall(r'[a-zA-Z][a-zA-Z0-9]*', expr1)
    varList2 = re.findall(r'[a-zA-Z][a-zA-Z0-9]*', expr2)
    varList = varList1 + varList2

    # Store them in set in order to get rid of duplicates.
    varSet = set(varList)
    # List of unique variables.
    varList = list(varSet)

    X = []
    # Finally replace the variables by 'X<i>'.
    for i in range(len(varList)):
        expr1 = expr1.replace(varList[i], get_vname(i))
        expr2 = expr2.replace(varList[i], get_vname(i))
        X.append(z3.BitVec(get_vname(i), bitCount))

    expr1Eval = eval(expr1)
    expr2Eval = eval(expr2)

    solver = z3.Solver()
    solver.add(expr1Eval != expr2Eval)
    result = solver.check()

    return str(result) == "unsat"


# Returns a random integer between 1 and 2**bitCount-1.
def rand(bitCount):
    return random.randint(1, 2**bitCount - 1)

# Returns the given expression after encoding its output using the affine
# function f(x) = a*x+b.
def encode_out(expr, a, b):
    return str(a) + "*(" + expr + ")+" + str(b)

# Returns the given expressions after encoding their outputs using an affine
# function f(x) = a*x+b for random integers a and b.
def encode_out_pair(expr1, expr2, bitCount):
    a = rand(bitCount)
    b = rand(bitCount)

    return encode_out(expr1, a, b), encode_out(expr2, a, b)


# Simplify all expressions included in the file with given name but the first
# one and compare them to the first one.
def simplify_dataset(datafile, bitCount=64, checkLinear=False, encode=False, useZ3=False, verbose=False, runs=-1):
    print("Simplify expressions from " + datafile + " ...")
    if verbose:
        print("")
    with open(datafile, "rt") as fr:
        first = True
        groundtruth = ""
        groundtruth_orig = ""

        dur = 0
        cnt = 0
        verified = 0
        equal = 0

        for line in fr:
            if cnt == runs:
                break

            if "#" not in line:
                line = line.strip()
                itemList = re.split(",", line)
                expr = itemList[0]
                groundtruth = itemList[1]

                if encode:
                    (expr, groundtruth) = encode_out_pair(expr, groundtruth, bitCount)

                groundtruth = simplify_linear_mba(groundtruth, bitCount, False)

                cnt = cnt + 1

                start = time.perf_counter()
                simplified = simplify_linear_mba(expr, bitCount, useZ3)
                dur += time.perf_counter() - start

                z3res = verify_mba_unsat(groundtruth, simplified, bitCount)

                if verbose:
                    print("    *** " + str(cnt) + " groundtruth " + groundtruth + ", simplified " + simplified + " => equal: " + str(groundtruth == simplified) + ", verified: " + str(z3res))

                if z3res:
                    verified = verified + 1
                    if groundtruth == simplified:
                        equal = equal + 1

        if verbose:
            print("")
        print("  * total count: " + str(cnt))
        print("  * verified: " + str(verified))
        print("  * equal: " + str(equal))
        avg = (1.0 * dur) / cnt
        print("  * average duration: " + str(avg))

        return cnt, verified, equal


# Print options.
def print_usage():
    print("Usage: python3 simplify_dataset.py")
    print("Command line options:")
    print("    -h:    print usage")
    print("    -b:    specify the bit number of variables (default is 64)")
    print("    -e:    encode the output using random affine functions")
    print("    -z:    enable a check for valid simplification using Z3")
    print("    -l:    enable a check for input expressions being linear MBAs")
    print("    -v:    activate verbose mode providing additional output")
    print("    -f:    specify a file containing expressions to be simplified")
    print("    -r:    specify a maximum number of expressions to simplify in case a file is used for input")


if __name__ == "__main__":
    argc = len(sys.argv)
    bitCount = 64
    encode = False
    useZ3 = False
    checkLinear = False
    verbose = False
    fileread = ""
    runs = -1

    i = 0
    while i < argc - 1:
        i = i + 1

        if sys.argv[i] == "-h":
            print_usage()
            sys.exit(0)

        elif sys.argv[i] == "-b":
            i = i + 1
            if i == argc:
                print_usage()
                sys.exit("Error: No bit count given!")

            bitCount = int(sys.argv[i])

        elif sys.argv[i] == "-e":
            encode = True

        elif sys.argv[i] == "-z":
            useZ3 = True

        elif sys.argv[i] == "-l":
            checkLinear = True

        elif sys.argv[i] == "-v":
            verbose = True

        elif sys.argv[i] == "-f":
            i = i + 1
            if i == argc:
                print_usage()
                sys.exit("Error: No file given!")

            fileread = sys.argv[i]

        elif sys.argv[i] == "-r":
            i = i + 1
            if i == argc:
                print_usage()
                sys.exit("Error: No maximum number of runs given!")

            runs = int(sys.argv[i])

        else:
            sys.exit("Error: Unknown command line option '" + sys.argv[i] + "'!")

    if fileread == "":
        sys.exit("Error: No file specified!")

    simplify_dataset(fileread, bitCount, checkLinear, encode, useZ3, verbose, runs)

