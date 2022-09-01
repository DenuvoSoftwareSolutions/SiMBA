
# SiMBA
SiMBA is a tool for the simplification of linear mixed Boolean-arithmetic expressions (MBAs). Like [MBA-Blast](https://github.com/softsec-unh/MBA-Blast) and [MBA-Solver](https://github.com/softsec-unh/MBA-Solver/), it uses a fully algebraic approach based on the idea that a linear MBA is fully determined by its values on the set of zeros and ones, but leveraging the new insights that a transformation to the 1-bit-space is not necessary for this.

It is based on the following paper:
<pre>@inproceedings{simba2022,
	author = {Reichenwallner, Benjamin and Meerwald-Stadler, Peter},
    title = {Efficient deobfuscation of linear mixed Boolean-arithmetic expressions},
    year = {2022},
    booktitle = {CheckMATE 2022} 
}
</pre>

## Content

Two main programs are provided:

- <code>simplify.py</code> for the simplification of single linear MBAs
- <code>simplify_dataset.py</code> for the simplification of a set of linear MBAs contained in a file and their verification via a comparison with corresponding simpler expressions also contained in this file

Additionally, the program <code>check_linear_mba.py</code> can be used for checking whether expressions represent linear MBAs.

## Usage

### Simplifying single expressions

In order to simplify a single expression <code>expr</code>, use

    python3 src/simplify.py "expr"
 
 Alternatively, multiple expressions can be simplified at once, e.g.:

    python3 src/simplify.py "x+x" "a&a"

In fact, each command line argument which is no option is considered an expression to be simplified. Note that omitting the quotation marks may imply undesired behavior. The simplification results are printed to the command line as shown in the following:

    *** Expression x+x
    *** ... simplified to 2*x
    *** Expression a
    *** ... simplified to a

Per default no check for the input expressions being linear MBAs is performed. This check can optionally be enabled via the option **-l**:

    python3 src/simplify.py "x*x" -l

Since $x*x$ is no linear MBA, the following output would show up in this case:

    *** Expression x*x
    Error: Input expression may be no linear MBA: x*x

If option **-z** is used, the simplification results are finally verified to be equal to the original expressions using *Z3*. This does not effect the command line output as long as the algorithm works correctly or an input expression is no linear MBA and no linearity check is performed:

    python3 src/simplify.py "x*x" -z

This would trigger the following error:

    *** Expression x*x
    Error in simplification! Simplified expression is not equivalent to original one!

Since the constants occuring in SiMBA's output expressions are always nonnegative, they may depend on the number of bits used for constants as well as variables. This number is $64$ by default and can be set using the option **-b**:

    python3 src/simplify.py "-x" -b 32

For a number $b$ of bits, the constants occuring in the output always lie between $0$ and $2^b-1$. Hence the call above would imply the following output:

    *** Expression -x
    *** ... simplified to 4294967295*x


### Simplifying and verifying expressions from a file

In order to simplify expressions stored in a file with path <code>path_to_file</code>, use

    python3 src/simplify_dataset.py -f path_to_file

That is, the file has to be specified using the option **-f**. Each line of the file has to contain a complex expression as well as an equivalent simpler one, separated by a comma, e.g.:

<pre>
(x&y) + (x|y), x+y
(x|y)-(~x&y)-(x&~y), x&y
-(a|~b)+(~b)+(a&~b)+b, a^b
2*(s&~t)+2*(s^t)-(s|t)+2*~(s^t)-~t-~(s&t), s
</pre>

For each line, both the complex and the simple expression are simplified and finally compared. The reason for simplifying the latter is to make verification results independent of whitespace, the order of factors or summands etc.

As with <code>simplify.py</code>, a linearity check as well as a check for a correct simplification can be enabled using the options **-l** and **-z**, resp., and the number of bits can be specified using option **-b**. If the user wants to run SiMBA on only a certain maximum number of expressions contained in the specified file, this maximum number can be specified via option **-r**:

    python3 src/simplify_dataset.py -f some_file.txt -r 2

If <code>some_file.txt</code> would contain the expressions listed above, only the first two of them would be simplified:

	Simplify expressions from data/some_file.txt ...
	  * total count: 2
	  * verified: 2
	  * equal: 2
	  * average duration: 0.00014788552653044462

In any case, the output gives information about
- the total number of expressions simplified,
- the number of expressions which could be verified to be equivalent to the corresponding simpler expression using Z3 after simplification (unless the simplification result already has the exact same string representation),
- the number of expressions which are simplified to the very same expression as the corresponding simple expression, and
- the average runtime in seconds.

> Please note that an optional verification of a correct simplification using Z3 contributes to the runtime, while this is not the case for the comparison of the simplification results of the pairs consisting of a complex and a simpler expression.

Per default the simplification results are not printed, but only these statistics are presented. If information about the former is desired, the option **-v** can be used:

    python3 src/simplify_dataset.py -f some_file.txt -v

The following output would then be shown in the command line:

	Simplify expressions from data/some_file.txt ...

	    *** 1 groundtruth x+y, simplified x+y => equal: True, verified: True
	    *** 2 groundtruth x&y, simplified x&y => equal: True, verified: True
	    *** 3 groundtruth a^b, simplified a^b => equal: True, verified: True
	    *** 4 groundtruth s, simplified s => equal: True, verified: True

	  * total count: 4
	  * verified: 4
	  * equal: 4
	  * average duration: 0.00016793253598734736

Another option **-e** provides the possibility to encode all expressions' outputs by affine functions $f(x) = ax+b$ with random integers $a,b$ between $1$ and $2^b-1$ if $b$ is the number of bits:

    python3 src/simplify_dataset.py -f some_file.txt -v -e

Of course the same function is applied to a pair of expressions in the same line. This would give output similar to the following:

	Simplify expressions from data/some_file.txt ...

	    *** 1 groundtruth 10623056950310032687+5038261596809828791*x+5038261596809828791*y, simplified 10623056950310032687+5038261596809828791*x+5038261596809828791*y => equal: True, verified: True
	    *** 2 groundtruth 15181401701264988765+3962868592131193124*(x&y), simplified 15181401701264988765+3962868592131193124*(x&y) => equal: True, verified: True
	    *** 3 groundtruth 6812440940417974076+11894131080657788315*(a^b), simplified 6812440940417974076+11894131080657788315*(a^b) => equal: True, verified: True
	    *** 4 groundtruth 4558303267887122851+10271005790757592209*s, simplified 4558303267887122851+10271005790757592209*s => equal: True, verified: True

	  * total count: 4
	  * verified: 4
	  * equal: 4
	  * average duration: 0.00019435951253399253

For a reproduction of part of the experiments stated in the paper, one may use any of the dataset files contained in the folder <code>data</code>. For each of the following functions $e_1,\ldots, e_5$, datasets of $1\,000$ equivalent linear MBAs using $2$, $3$ or $4$ variables are provided:

- $e_1(x,y) = x+y$
- $e_2 = 49\,374$
- $e_3(x) = 3\,735\,936\,685\, x + 49\,374$
- $e_4(x,y) = 3\,735\,936\,685\, (x\mathbin{^\wedge}y) + 49\,374$
- $e_5(x) = 3\,735\,936\,685\cdot \mathord{\sim} x$

For $e_1$, additional datasets for $5$ to $7$ variables are provided. These MBAs have been generated using an algorithm based on the method described by Zhou et al. in 2007 and described in the paper.

> Please note that these datasets have been generated for $b=64$ bits. For different numbers of bits, their equivalence to the $e_i$'s cannot be guaranteed.

For the reproduction of further experiments, we refer to the datasets provided by the [MBA-Solver repository](https://github.com/softsec-unh/MBA-Solver/blob/main/full-dataset/pldi_dataset_linear_MBA.txt) and the [NeuReduce repository](https://github.com/fvrmatteo/NeuReduce/tree/master/dataset/linear/test), resp.

### Checking linearity

The file <code>check_linear_mba.py</code> is used by the simplifier, but it also provides its own interface, e.g.:

    python3 src/check_linear_mba.py "x+x" "x*x"

It checks all expressions which are passed via command line arguments. In this case it would imply the following output:

	*** Expression x+x
	*** +++ valid
	*** Expression x*x
	*** --- not valid

## Format of MBAs

The number of variables is in theory unbounded, but of course the runtime increases with variable count. There is no strong restriction on the notation of variables. They have to start with a letter and can contain letters, numbers and underscores. E.g., the following variable names would all be fine:
- $a$, $b$, $c$, ..., $x$, $y$, $z$, ...
- $v0$, $v1$, $v2$, ...
- $v\_0$, $v\_1$, $v\_2$, ...
- $X0$, $X1$, $X2$, ...
- $var0$, $var1$, $var2$, ...
- $var1a$, $var1b$, $var1c$, ...
- ...

The following operators are supported, ordered by their precedence in Python:
- $\mathord{\sim}$, $-$: bitwise negation and unary minus
- $*$: product
- $+$, $-$: sum and difference
- &: conjunction
- $\mathbin{^\wedge}$: exclusive disjunction
- $|$: inclusive disjunction

Whitespace can be used in the input expressions. E.g., the expression <code>"x+y"</code> may alternatively be written <code>"x + y"</code>.

> Please respect the precedence of operators and use parentheses if necessary! E.g., the expressions $1 + (x|y)$ and $1 + x|y$ are not equivalent since $+$ has a higher precedence than $|$. Note that the latter is not even a linear MBA.

## Dependencies
The SMT Solver **Z3** is required
- by simplify_dataset.py where simplified expressions are verified to be equivalent to corresponding simple expressions, and
- by simplify.py if the optional verification of simplified expressions is used. If this option is unused, no error is thrown even if Z3 is not installed.

Installing Z3:
- from  the Github repository: https://github.com/Z3Prover/z3
- on Debian: <code>sudo apt-get install python3-z3</code>

## Contact
- Benjamin Reichenwallner: benjamin(dot)reichenwallner(at)denuvo(dot)com
- Peter Meerwald-Stadler: peter(dot)meerwald(at)denuvo(dot)com
