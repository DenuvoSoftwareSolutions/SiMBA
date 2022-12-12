#!/usr/bin/python3

import io
import re
import sys
import traceback


# Class for checking whether a given expression is a valid linear MBA.
class MbaChecker():
    def __init__(self, expr):
        self.expr = expr
        self.idx = 0

    # Precedence:
    #   0. **
    #   1. ~, - (unary)
    #   2. *
    #   3. +, - (binary)
    #   4. &
    #   5. ^
    #   6. |

    # Expression type:
    #   0: bitwise
    #   1: arithmetic
    #   2: mixed

    # Returns true iff the expression is a valid linear MBA.
    def check_expression(self):
        valid, _ = self.check_inclusive_disjunction()
        if not valid:
            return False

        while self.idx < len(self.expr) and self.has_space():
            self.skip_space()

        return self.idx == len(self.expr)

    # Returns true iff the inclusive disjunction starting at current idx of
    # expr fulfills the requirements of a linear MBA. Additionally returns 0 if
    # it is composed by bitwise expressions only, 1 if it is composed by
    # arithmetic expressions only and 2 if it is a mixed expression. An
    # inclusive disjunction of arithmetic expressions is considered to be
    # arithmetic since one can simplify that easily to a constant.
    def check_inclusive_disjunction(self):
        valid, exprType = self.check_exclusive_disjunction()
        if not valid:
            return False, exprType
        if exprType == 2 and self.peek() == '|':
            return False, exprType

        while self.peek() == '|':
            self.get()
            valid, t = self.check_exclusive_disjunction()
            if not valid or t != exprType:
                return False, exprType

        return True, exprType

    # Returns true iff the exclusive disjunction starting at current idx of
    # expr fulfills the requirements of a linear MBA. Additionally returns 0 if
    # it is composed by bitwise expressions only, 1 if it is composed by
    # arithmetic expressions only and 2 if it is a mixed expression. An
    # exclusive disjunction of arithmetic expressions is considered to be
    # arithmetic since one can simplify that easily to a constant.
    def check_exclusive_disjunction(self):
        valid, exprType = self.check_conjunction()
        if not valid:
            return False, exprType
        if exprType == 2 and self.peek() == '^':
            return False, exprType

        while self.peek() == '^':
            self.get()
            valid, t = self.check_conjunction()
            if not valid or t != exprType:
                return False, exprType

        return True, exprType

    # Returns true iff the conjunction starting at current idx of expr fulfills
    # the requirements of a linear MBA. Additionally returns 0 if it is composed
    # by bitwise expressions only, 1 if it is composed by arithmetic
    # expressions only and 2 if it is a mixed expression. An inclusive
    # disjunction of arithmetic expressions is considered to be arithmetic
    # since one can simplify that easily to a constant.
    def check_conjunction(self):
        valid, exprType = self.check_sum()
        if not valid:
            return False, exprType
        if exprType == 2 and self.peek() == '&':
            return False, exprType

        while self.peek() == '&':
            self.get()
            valid, t = self.check_sum()
            if not valid or t != exprType:
                return False, exprType

        return True, exprType

    # Returns true iff the sum starting at current idx of expr fulfills the
    # requirements of a linear MBA. Additionally returns 0 if it is composed by
    # bitwise expressions only, 1 if it is composed by arithmetic expressions
    # only and 2 if it is a mixed expression.
    def check_sum(self):
        valid, exprType = self.check_product()
        if not valid:
            return False, exprType

        while self.peek() == '+' or self.peek() == '-':
            self.get()
            valid, t = self.check_product()
            if not valid:
                return False, exprType
            if exprType == 0 or (exprType != 2 and t != exprType):
                exprType = 2

        return True, exprType

    # Returns true iff the product starting at current idx of expr fulfills the
    # requirements of a linear MBA. Additionally returns 0 if it is composed by
    # bitwise expressions only, 1 if it is composed by arithmetic expressions
    # only and 2 if it is a mixed expression.
    def check_product(self):
        valid, exprType = self.check_factor()
        if not valid:
            return False, exprType

        bitwiseCount = int(exprType != 1)

        while self.peek() == '*':
            self.get()
            valid, t = self.check_factor()
            if not valid:
                return False, exprType
            if t != 1:
                bitwiseCount += 1
            if exprType != 2 and t != exprType:
                exprType = 2
            if bitwiseCount > 1:
                return False, exprType

        return True, exprType

    # Returns true iff the factor starting at current idx of expr fulfills the
    # requirements of a linear MBA. Additionally returns 0 if it is composed by
    # bitwise expressions only, 1 if it is composed by arithmetic expressions
    # only and 2 if it is a mixed expression. A factor is
    #   - an expression surrounded by parentheses,
    #   - a bitwise negation,
    #   - an arithmetic negation,
    #   - a variable, or
    #   - a constant.
    def check_factor(self):
        if self.peek() == '(':
            self.get()
            valid, exprType = self.check_inclusive_disjunction()
            if not valid:
                return False, exprType
            if not self.peek() == ')':
                return False, exprType
            self.get()

            return True, exprType

        if self.has_bitwise_negated_expression():
            return self.check_bitwise_negated_expression()

        if self.has_negative_expression():
            return self.check_negative_expression()

        return self.check_terminal()

    # Returns true iff the bitwise negated expression starting at current idx
    # of expr fulfills the requirements of a linear MBA. Additionally returns 0
    # if it is composed by bitwise expressions only, 1 if it is composed by
    # arithmetic expressions only and 2 if it is a mixed expression. A bitwise
    # negation of a constant is considered to be arithmetic since one can
    # simplify that easily to a constant.
    def check_bitwise_negated_expression(self):
        # Skip '~'.
        self.get()

        # We have a nested negation.
        while self.has_bitwise_negated_expression():
            self.get()

        if self.peek() == '(':
            self.get()
            valid, exprType = self.check_inclusive_disjunction()
            if not valid or exprType == 2:
                return False, exprType
            if not self.peek() == ')':
                return False, exprType
            self.get()

            return True, exprType

        return self.check_terminal()

    # Returns true iff the arithmetic negation starting at current idx of expr
    # fulfills the requirements of a linear MBA. Additionally returns 1 if it
    # is composed by arithmetic expressions only and 2 if it is a mixed
    # expression.
    def check_negative_expression(self):
        # Skip '-'.
        self.get()

        # Allow multiple arithmetic negations.
        while self.has_negative_expression():
            self.get()

        if self.peek() == '(':
            self.get()
            valid, exprType = self.check_inclusive_disjunction()
            if not valid:
                return False, exprType
            if not self.peek() == ')':
                return False, exprType
            self.get()

            if exprType == 0:
                exprType = 2
            return True, exprType

        if self.has_bitwise_negated_expression():
            return self.check_bitwise_negated_expression()

        valid, exprType = self.check_terminal()
        if exprType == 0:
            exprType = 2
        return True, exprType

    # Returns true iff the terminal expression (variable or constant) starting
    # at current idx of expr fulfills the requirements of a linear MBA.
    # Additionally returns 0 if it is a variable and 1 if it is a constant.
    # Moreover, powers constituted by constants only are permitted.
    def check_terminal(self):
        if self.has_variable():
            return self.check_variable(), 0

        valid = self.check_constant()
        if not valid:
            return False, 1

        if self.peek() == '*' and self.peek_next() == '*':
            self.get()
            self.get()

            if self.peek() == '(':
                self.get()
                valid, exprType = self.check_inclusive_disjunction()
                if not exprType == 1:
                    return False, exprType
                if not valid:
                    return False, 1
                if not self.peek() == ')':
                    return False, 1
                self.get()
                return True, 1

            return self.check_constant(), 1

        return True, 1

    # Returns true and skips the variable starting at current idx of expr. A
    # variable has to start with a letter and has to be composed by letters and
    # digits.
    def check_variable(self):
        # Skip first character that has already been checked.
        self.get()

        while self.has_decimal_digit() or self.has_letter() or self.peek() == '_':
            self.get()

        return True

    # Returns true iff the constant starting at current idx of expr is valid.
    # It can be in decimal, binary or hexadecimal representation.
    def check_constant(self):
        if self.has_binary_constant():
            return self.check_binary_constant()

        if self.has_hex_constant():
            return self.check_hex_constant()

        return self.check_decimal_constant()

    # Returns true iff the binary constant starting at current idx of expr is
    # valid. A binary constant starts with '0b'.
    def check_binary_constant(self):
        # Skip '0' and 'b'.
        self.get()
        self.get()

        if self.peek() not in ['0', '1']:
            return False
        while self.peek() in ['0', '1']:
            self.get()

        return True

    # Returns true iff the hexadecimal constant starting at current idx of expr
    # is valid. A hexadecimal constant starts with '0x'.
    def check_hex_constant(self):
        # Skip '0' and 'x'.
        self.get()
        self.get()

        if not self.has_hex_digit():
            return False
        while self.has_hex_digit():
            self.get()

        return True

    # Returns true iff the decimal constant starting at current idx of expr is
    # valid.
    def check_decimal_constant(self):
        if not self.has_decimal_digit():
            return False
        while self.has_decimal_digit():
            self.get()

        return True

    # Returns the character at position idx of expr, increments idx and skips
    # spaces.
    def get(self):
        c = self.peek()
        self.idx += 1
        while self.has_space():
            self.skip_space()
        return c

    # Set idx to the position of the next character of expr which is no space.
    def skip_space(self):
        self.idx += 1

    # Returns the character at position idx of expr or '' if the end of expr is
    # reached.
    def peek(self):
        if self.idx >= len(self.expr):
            return ''
        return self.expr[self.idx]

    # Returns true iff the character at position idx of expr indicates a
    # bitwise negation.
    def has_bitwise_negated_expression(self):
        return self.peek() == '~'

    # Returns true iff the character at position idx of expr is a unary minus.
    def has_negative_expression(self):
        return self.peek() == '-'

    # Returns true iff the character at position idx of expr and its succeeding
    # character indicate a binary number, i.e., are '0b'.
    def has_binary_constant(self):
        return self.peek() == '0' and self.peek_next() == 'b'

    # Returns true iff the character at position idx of expr and its succeeding
    # character indicate a hexadecimal number, i.e., are '0x'.
    def has_hex_constant(self):
        return self.peek() == '0' and self.peek_next() == 'x'

    # Returns true iff the character at position idx of expr is a valid digit in
    # hexadecimal representation.
    def has_hex_digit(self):
        return self.has_decimal_digit() or re.match(r'[a-fA-F]', self.peek())

    # Returns true iff the character at position idx of expr is a valid digit in
    # decimal representation.
    def has_decimal_digit(self):
        return re.match(r'[0-9]', self.peek())

    # Returns true iff the character at position idx of expr indicates a
    # variable name.
    def has_variable(self):
        return self.has_letter()

    # Returns true iff the character at position idx of expr is a letter.
    def has_letter(self):
        return re.match(r'[a-zA-Z]', self.peek())

    # Returns true iff the character at position idx of expr is a space.
    def has_space(self):
        return self.peek() == ' '

    # Returns the character at position idx + 1 of expr or '' if the end of
    # expr would be reached.
    def peek_next(self):
        if self.idx >= len(self.expr) - 1:
            return ''
        return self.expr[self.idx + 1]


# Returns true iff the given expression is a linear MBA.
def check_linear_mba(expr):
    checker = MbaChecker(expr)
    return checker.check_expression()


# Print usage.
def print_usage():
    print("Usage: python3 check_linear_mba.py")
    print("Command line inputs are considered expressions to be simplified.")
    print("The variables are expected to start with letters and consist of letters, underscores and digits.")


if __name__ == "__main__":
    argc = len(sys.argv)
    expressions = []

    for i in range(1, argc):
        expressions.append(sys.argv[i])

    if len(expressions) == 0:
        sys.exit("No expressions to check given!")

    for expr in expressions:
        print("*** Expression " + expr)
        valid = check_linear_mba(expr)
        if valid:
            print("*** +++ valid")
        else:
            print("*** --- not valid")
