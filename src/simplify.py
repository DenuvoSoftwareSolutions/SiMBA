#!/usr/bin/python3

import inspect
import io
import os
import re
import sys
import traceback
try: import z3
except ModuleNotFoundError: pass

from check_linear_mba import check_linear_mba


# The main simplification class which stores relevant parameters such as the
# number of variables, the modulus of the modular field as well as the vector
# of results of the target expression for combinations of truth values.
class Simplifier():
    # Initialize internals.
    def init(self, bitCount, expr):
        self.groupsizes = [1]
        self.bitCount = bitCount
        self.modulus = 2**bitCount
        self.originalVariables = []
        self.originalExpression = expr
        self.vnumber = 0
        self.resultVector = []

        self.parse_and_replace_variables()
        self.init_groupsizes()
        self.init_result_vector()

    # Constructor which initiates the initialization.
    def __init__(self, modulus, expr):
        self.init(modulus, expr)

    # Get the internal name of the variable with given index.
    def get_vname(self, i):
        return "X[" + str(i) + "]"

    # Reduces the given number modulo modulus.
    def mod_red(self, n):
        return n % self.modulus

    # Find all variables included in the stored original expression, store them
    # in a list and replace them by internal variable names.
    def parse_and_replace_variables(self):
        # List of variables as well as binary or hexadecimal numbers (or
        # potentially any illegal strings). We include these constants because
        # we want to make sure not to consider parts of binary or hex numbers
        # as variable names.
        varsAndConstants = re.findall(r'[0]?[a-zA-Z][a-zA-Z0-9_]*', self.originalExpression)

        # List of variables including multiple occurences.
        varList = [s for s in varsAndConstants if s[0] != '0']
        # Store them in set in order to get rid of duplicates.
        varSet = set(varList)
        # List of unique variables.
        self.originalVariables = list(varSet)
        

        # First sort in alphabetical order since it is nice to have, e.g., 'x'
        # preceding 'y'.
        self.originalVariables.sort()
        # Sort by length, but afterwards they have to be replaced in reverse
        # order in order not to replace substrings of variables.
        self.originalVariables.sort(key=len)

        # List of binary or hex numbers.
        constants = [s for s in varsAndConstants if s[0] == '0']
        # Again remove duplicates for efficiency.
        constants = list(set(constants))
        # Sort the constants by length in order not to replace substrings of
        # larger numbers.
        constants.sort(key=len)
        # Finally replace those numbers by their decimal equivalents.
        for i in range(len(constants) - 1, -1, -1):
            c = constants[i]
            assert(len(c) > 1)

            base = 16
            if c[:2] == "0b" or c[:2] == "0B":
                base = 2
            elif c[:2] != "0x" and c[:2] != "0X":
                sys.exit("Error: Invalid string " + c)

            try:
                n = int(c, base)
                self.originalExpression = self.originalExpression.replace(c, str(n))
            except:
                sys.exit("Error: Invalid string " + c)

        self.vnumber = len(self.originalVariables)
        # Finally replace the variables by 'X<i>'.
        for i in range(self.vnumber - 1, -1, -1):
            self.originalExpression = self.originalExpression.replace(self.originalVariables[i], self.get_vname(i))

    # Initialize the group sizes of the various variables, i.e., their numbers
    # of subsequent occurences in the truth table.
    def init_groupsizes(self):
        for i in range(1, self.vnumber):
            self.groupsizes.append(2 * self.groupsizes[-1])

    # Initialize the vector storing results of expression evaluation for all
    # truth value combinations, i.e., [e(0,0,...), e(1,0,...), e(0,1,...),
    # e(1,1,...)].
    def init_result_vector(self):
        def f(X):
            return self.mod_red(eval(self.originalExpression))

        self.resultVector = []
        for i in range(2**self.vnumber):
            n = i
            par = []
            for j in range(self.vnumber):
                par.append(n & 1)
                n = n >> 1
            self.resultVector.append(f(par))

    # Replace the internal variable names by the original ones in the given
    # expression.
    def replace_variables_back(self, expr):
        for i in range(self.vnumber):
            expr = expr.replace(self.get_vname(i), self.originalVariables[i])
        return expr

    # Parses and returns the lookup table containing 2^2^t base expressions for
    # the used number t of variables.
    def get_bitwise_list(self):
        if not self.vnumber in [1, 2, 3]:
            print("vnumber must be 1, 2 or 3.")
            traceback.print_stack()
            sys.exit(0)

        if self.vnumber == 1:
            return [
                    "0",    # [0 0]
                    "X[0]"  # [0 1]
                   ]

        if self.vnumber == 2:
            return [
                    "0",                # [0 0 0 0]
                    "(X[0]&~X[1])",     # [0 1 0 0]
                    "~(X[0]|~X[1])",    # [0 0 1 0]
                    "(X[0]^X[1])",      # [0 1 1 0]
                    "(X[0]&X[1])",      # [0 0 0 1]
                    "X[0]",             # [0 1 0 1]
                    "X[1]",             # [0 0 1 1]
                    "(X[0]|X[1])"       # [0 1 1 1]
                   ]

        currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
        truthfile = os.path.join(currentdir, "bitwise_list_" + str(self.vnumber) + "vars.txt")
        bitwiseExprList = []

        with open(truthfile, "r") as fr:
            for line in fr:
                line = line.strip()
                b = re.split("#", line)[0].rstrip()
                bitwiseExprList.append(b)

        return bitwiseExprList

    # For the given vector of truth values, returns the index of the
    # corresponding expression in the lookup table after subtracting the given
    # offset. That is, returns the index of the truth table entry for a truth
    # value vector which has zeros exactly in the positions where the given
    # vector contains the given offset.
    def get_bitwise_index_for_vector(self, vector, offset):
        index = 0
        add = 1
        for i in range(len(vector) - 1):
            if vector[i+1] != offset:
                index += add
            add <<= 1

        return index

    # For the used vector of truth values, returns the index of the
    # corresponding expression in the lookup table after subtracting the given
    # offset. That is, returns the index of the truth table entry for a truth
    # value vector which has zeros exactly in the positions where the given
    # vector contains the given offset.
    def get_bitwise_index(self, offset):
        return self.get_bitwise_index_for_vector(self.resultVector, offset)


    # Returns true iff a is the sum of s1 and s2 in the modular field.
    def is_sum_modulo(self, s1, s2, a):
        return s1 + s2 == a or s1 + s2 == a + self.modulus

    # Returns true iff a is double b in the modular field.
    def is_double_modulo(self, a, b):
        return 2 * b == a or 2 * b == a + self.modulus


    # Append a simple expression from the given lookup table corresponding to
    # the positions where the vector of results for truth value combinations
    # has a value of r1 or rAlt to the given expression.
    def append_term_refinement(self, expr, bitwiseList, r1, rAlt=None):
        t = []
        for r2 in self.resultVector:
            t.append(int(r2 == r1 or (rAlt is not None and r2 == rAlt)))

        index = self.get_bitwise_index_for_vector(t, 0)
        if r1 == 1:
            return expr + bitwiseList[index] + "+"

        return expr + str(r1) + "*" + bitwiseList[index] + "+"

    # Build an expression by summing up expressions from the given lookup
    # table, each corresponding to a value in the lookup table and multiplied
    # by this value thereafter.
    def expression_for_each_unique_value(self, resultSet, bitwiseList):
        expr = ""
        for r in resultSet:
            if r != 0:
                expr = self.append_term_refinement(expr, bitwiseList, r)

        # Get rid of '+' at the end.
        expr = expr[:-1]

        # If we only have 1 term, get rid of parentheses, if present.
        if len(resultSet) == 1 and expr[0] == '(' and expr[-1] == ')':
            expr = expr[1:-1]

        return expr

    # For the given set of results of the input expression for combinations of
    # truth values and the given lookup table, try to find a single negated
    # expression representing the result vector in the lookup table.
    def try_find_negated_single_expression(self, resultSet, bitwiseList):
        # We can only find a negated expression if we have 2 distinct values.
        assert(len(resultSet) == 2)

        # Check whether we have a bitwise negation of a term in the lookup table.
        # This is the only chance for reducing the expression to one term.

        s = resultSet.copy()
        a = s.pop()
        b = s.pop()
        aDouble = self.is_double_modulo(a, b)
        bDouble = self.is_double_modulo(b, a)
        if not aDouble and not bDouble:
            return ""

        # Make sure that b is double a.
        if aDouble:
            a, b = b, a

        if self.resultVector[0] == b:
            return ""

        coeff = self.mod_red(-a)

        t = []
        for r in self.resultVector:
            t.append(int(r == b))

        index = self.get_bitwise_index_for_vector(t, 0)
        e = bitwiseList[index]
        if e[0] == "~":
            e = e[1:]
        else:
            e = "~" + e

        if coeff == 1:
            return e

        return str(coeff) + "*" + e

    # For the given unique values appearing in the simplifier's result vector,
    # possibly, after subtraction of a constant, try to express one of them as
    # sum of others in order to find a combination of fewer simple expressions
    # from a lookup table.
    def try_eliminate_unique_value(self, uniqueValues, bitwiseList):
        l = len(uniqueValues)
        # NOTE: Would be possible also for higher l, implementation is generic.
        if l > 4:
            return ""

        # Try to get rid of a value by representing it as a sum of the others.
        for i in range(l - 1):
            for j in range(i + 1, l):
                for k in range(l):
                    if k == i or k == j:
                        continue

                    if self.is_sum_modulo(uniqueValues[i], uniqueValues[j], uniqueValues[k]):
                        simpler = ""
                        for i1 in [i, j]:
                            simpler = self.append_term_refinement(simpler, bitwiseList, uniqueValues[i1], uniqueValues[k])

                        if l > 3:
                            resultSet = set(uniqueValues)
                            resultSet.discard(uniqueValues[i])
                            resultSet.discard(uniqueValues[j])
                            resultSet.discard(uniqueValues[k])

                            while len(resultSet) > 0:
                                r1 = resultSet.pop()
                                simpler = self.append_term_refinement(simpler, bitwiseList, r1)

                        simpler = simpler[:-1]
                        return simpler

        if l < 4:
            return ""

        # Finally, if we have more than 3 values, try to express one of them as
        # a sum of all others.
        for i in range(l):
            if not 2 * uniqueValues[i] == sum(uniqueValues):
                continue

            simpler = ""
            for j in range(l):
                if i == j:
                    continue

                simpler = self.append_term_refinement(simpler, bitwiseList, uniqueValues[j], uniqueValues[i])

            return simpler

        return ""

    # For the given expression, check whether the number of its terms can be
    # decreased by finding suitable combinations of simple expressions in a
    # lookup table. Currently only tries to simplify to at most 3 terms.
    # NOTE: Could be extended to more terms for 3 variables.
    def try_refine(self, expr):
        # Rebuild the result vector since it has been modified during
        # simplification.
        self.init_result_vector()

        # The number of terms.
        count = expr.count('+') + 1

        # The expression is already as simple as it can be.
        if count <= 1:
            return expr

        resultSet = set(self.resultVector)
        l = len(resultSet)
        assert(l > 1)

        # We try to find a solution that is simpler than the linear combination.
        # In this course we perform several attempts, numbered according to the
        # paper.
        # NOTE: The case (1) that we only have one unique value has already
        # been handled in simplify_one_value().

        bitwiseList = self.get_bitwise_list()

        if l == 2:
            # (2) If only one nonzero value occurs and the result for all
            # variables being zero is zero, we can find a single expression.
            if self.resultVector[0] == 0:
                simpler = self.expression_for_each_unique_value(resultSet, bitwiseList)
                if simpler[0] == '(' and simpler[-1] == ')':
                    simpler = simpler[1:-1]
                return simpler

            # (3) Check whether we can find one single negated term.
            simpler = self.try_find_negated_single_expression(resultSet, bitwiseList)
            if simpler != "":
                return simpler

        # We cannot simplify the expression better.
        if count <= 2:
            return expr

        # If the first result is nonzero, this is the term's constant. Subtract
        # it.
        constant = self.resultVector[0]
        if constant != 0:
            for i in range(len(self.resultVector)):
                self.resultVector[i] -= constant
                self.resultVector[i] = self.mod_red(self.resultVector[i])

        resultSet = set(self.resultVector)
        l = len(resultSet)

        if l == 2:
            # (4) In this case we know that the constant is nonzero since we
            # would have run into the case above otherwise.
            return str(constant) + "+" + self.expression_for_each_unique_value(resultSet, bitwiseList)

        if l == 3 and constant == 0:
            # (5) We can reduce the expression to two terms.
            return self.expression_for_each_unique_value(resultSet, bitwiseList)

        uniqueValues = []
        for r in resultSet:
            if r != 0:
                uniqueValues.append(r)

        if l == 4 and constant == 0:
            # (6) We can still come down to 2 expressions if we can express one
            # value as a sum of the others.
            simpler = self.try_eliminate_unique_value(uniqueValues, bitwiseList)
            if simpler != "":
                return simpler

        # NOTE: One may additionally want to try to find a sum of two negated
        # expressions, or one negated and one unnegated...

        # We cannot simplify the expression better.
        if count == 3:
            return expr

        if constant == 0:
            # (7) Since the previous attempts failed, the best we can do is find
            # three expressions corresponding to the three unique values.
            return self.expression_for_each_unique_value(resultSet, bitwiseList)

        # (8) Try to reduce the number of unique values by expressing one as a
        # combination of the others.
        simpler = self.try_eliminate_unique_value(uniqueValues, bitwiseList)
        if simpler != "":
            if constant == 0:
                return simpler
            return str(constant) + "+" + simpler

        return expr


    # Returns a trivial expression constituted by only one constant which is
    # the only element of the given set.
    def simplify_one_value(self, resultSet):
        coefficient = resultSet.pop()
        simExpre = str(self.mod_red(coefficient))
        return simExpre

    # Returns all sublists of the list [0,...,vnumber-1] ordered by their
    # sizes, whereas each sublist is sorted in increasing order.
    def get_variable_combinations(self):
        comb = [[v] for v in range(self.vnumber)]
        new = self.vnumber

        for count in range(1, self.vnumber):
            size = len(comb)
            nnew = 0
            for e in comb[size-new:size]:
                for v in range(e[-1] + 1, self.vnumber):
                    comb.append(e + [v])
                    nnew += 1

            new = nnew

        return comb

    # Append the conjunction of all variables included in the given list to the
    # given expression if the given coefficient is nonzero and multiply it with
    # that coefficient.
    def append_conjunction(self, expr, coeff, variables):
        assert(len(variables) > 0)
        if coeff == 0:
            return expr

        if coeff != 1:
            expr += str(coeff) + "*"

        # If we have a nontrivial conjunction, we need parentheses.
        if len(variables) > 1:
            expr += "("

        for v in variables:
            expr += self.get_vname(v) + "&"
        # Get rid of last '&'.
        expr = expr[:-1]

        if len(variables) > 1:
            expr += ")"

        return expr + "+"

    # Returns true iff the given variables hold in the result vector's entry
    # with given index.
    def are_variables_true(self, n, variables):
        prev = 0
        for v in variables:
            n >>= (v - prev)
            prev = v

            if (n & 1) == 0:
                return False

        return True

    # Subtract the given coefficient from all elements of the result vector
    # which correspond to the same conjunction.
    def subtract_coefficient(self, coeff, firstStart, variables):
        groupsize1 = self.groupsizes[variables[0]]
        period1 = 2 * groupsize1
        for start in range(firstStart, len(self.resultVector), period1):
            for i in range(start, start + groupsize1):
                # The first variable is true by design of the for loops.
                if i != firstStart and (len(variables) == 1 or self.are_variables_true(i, variables[1:])):
                    self.resultVector[i] -= coeff

    # For the given vector of results for the combinations of truth values for
    # variables, and for the used number t of variables, determine a linear
    # combination of the 2^t base bitwise expressions.
    def simplify_generic(self):
        l = len(self.resultVector)
        expr = ""

        # The constant term.
        constant = self.mod_red(self.resultVector[0])
        for i in range(1, l):
            self.resultVector[i] -= constant

        if constant != 0:
            expr += str(constant) + "+"

        # Append all conjunctions of variables (including trivial conjunctions
        # of single variables) if their coefficients are nonzero.
        combinations = self.get_variable_combinations()
        for comb in combinations:
            index = sum([self.groupsizes[v] for v in comb])
            coeff = self.mod_red(self.resultVector[index])

            if coeff == 0:
                continue

            self.subtract_coefficient(coeff, index, comb)
            expr = self.append_conjunction(expr, coeff, comb)

        if expr == "":
            expr = "0"
        else:
            # Remove '+' at the end.
            expr = expr[:-1]

            if expr.count('+') == 0 and expr[0] == '(' and expr[-1] == ')':
                expr = expr[1:-1]

        return expr

    # For the given expression, check how many variables it uses effectively.
    # If it is not more than 3, run the simplification procedure again for that
    # variable count since we might be able to simplify the expression using
    # truth tables.
    def try_simplify_fewer_variables(self, expr):
        occuring = []

        for v in range(self.vnumber):
            if expr.find(self.get_vname(v)) != -1:
                occuring.append(v)

        vnumber = len(occuring)
        # No function available for more than 3.
        if vnumber > 3:
            return expr

        for i in range(vnumber):
            expr = expr.replace(self.get_vname(occuring[i]), "v" + str(i))

        innerSimplifier = Simplifier(self.bitCount, expr)
        expr = innerSimplifier.simplify(False)

        for i in range(vnumber):
            expr = expr.replace("v" + str(i), self.originalVariables[occuring[i]])

        return expr

    # Verify that the original expression and the simplified one are equivalent
    # using Z3.
    def verify_mba_unsat(self, simpl):
        if simpl == self.originalExpression:
            return True

        X = []
        for i in range(self.vnumber):
            X.append(z3.BitVec(self.get_vname(i), self.bitCount))

        exprEval = eval("(" + self.originalExpression + ") % " + str(self.modulus))
        simplEval = eval("(" + simpl + ") % " + str(self.modulus))

        solver = z3.Solver()
        solver.add(exprEval != simplEval)
        result = solver.check()

        return str(result) == "unsat"

    # Simplify the expression with used number of variables.
    def simplify(self, useZ3):
        if self.vnumber > 3:
            simpl = self.simplify_generic()
            simpl = self.try_simplify_fewer_variables(simpl)

        else:
            resultSet = set(self.resultVector)

            if len(resultSet) == 1:
                simpl = self.simplify_one_value(resultSet)

            else:
                simpl = self.simplify_generic()
                simpl = self.try_refine(simpl)

        if useZ3 and not self.verify_mba_unsat(simpl):
            sys.exit("Error in simplification! Simplified expression is not equivalent to original one!")

        simpl = self.replace_variables_back(simpl)

        return simpl


# Simplify the given expression with given number of variables. For that,
# evaluate it for all possible combinations of truth values for the variables
# and run the simplification procedure based on the resulting vector.
def simplify_linear_mba(expr, bitCount, useZ3, checkLinear=False):
    if checkLinear and not check_linear_mba(expr):
        sys.exit("Error: Input expression may be no linear MBA: " + expr)

    simplifier = Simplifier(bitCount, expr)
    simpl = simplifier.simplify(useZ3)
    return simpl


# Print options.
def print_usage():
    print("Usage: python3 simplify.py")
    print("Each command line input not preceded by option indicators below is considered an expression to be simplified.")
    print("Command line options:")
    print("    -h:    print usage")
    print("    -b:    specify the bit number of variables (default is 64)")
    print("    -z:    enable a check for valid simplification using Z3")
    print("    -l:    enable a check for input expressions being linear MBAs")


if __name__ == "__main__":
    argc = len(sys.argv)
    bitCount = 64
    useZ3 = False
    checkLinear = False
    expressions = []

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

        elif sys.argv[i] == "-z":
            useZ3 = True

        elif sys.argv[i] == "-l":
            checkLinear = True

        else:
            expressions.append(sys.argv[i])

    if len(expressions) == 0:
        sys.exit("No expressions to simplify given!")

    for expr in expressions:
        print("*** Expression " + expr)
        simpl = simplify_linear_mba(expr, bitCount, useZ3, checkLinear)
        print("*** ... simplified to " + simpl)

    sys.exit(0)
