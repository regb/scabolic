DEVELOPMENT NOTES
=================

This file will collect all relevant notes for the project, such as design
decision that might need to be reconsidered or any general advice in building
this kind of system.  This is mostly to be used as a remainder of some
sensitive point in the project.



Variable vs Uninterpreted Function Symbol 
-----------------------------------------

The difference is not clear, especially in SMTLIB where it is necessary to
collect uninterpreted symbol as free variables.

Now it seems that in satisfiability type problems, we should be using uninterpreted
symbol instead of variable. An interpretation/assignment would then be a mapping from
uninterpreted symbols to Terms.

Formula + Term vs all terms with boolean sort used to build formulas 
--------------------------------------------------------------------

Having a static type distinction can allow some static checking by the
compiler, but this makes the definition of maps and fold over tree very heavy
with the need to carry around both functions to map formulas and terms

Semantics of tree transformation over binded variable
-----------------------------------------------------

What should be the semantic of substitute or map with variable that are bound
to a quantifier?

Minicore + extractors
---------------------

This is, I believe, a very elegant way to have a compatible tree among all
theories that can be extended with any operator with very minimal amount of
code and still get all the usefull tree function without any change. However we
lose the static type information of all these new operators that simply become
FunctionApplication, and we cannot statically declare function that only accept
a very specific part of the tree. This forces to use dynamic check everywhere.
I believe this is not foundamentally a performence issue because the dynamic
check can simply be ignore once the code is sufficiently tested and every
function is used with the correct kind of arguments.

How to use
----------

The idea is to support many different ways of using the solver. In particular, we
will support several standard file format. For now, we identified 3 file formats
that we aim at supporting:
- DIMACS cnf
  Our support will be very basic: each line starting with a 'c' is ignored. The problem
  line must appear before any clauses and will be of the form 'p cnf N M' where N and M are
  positive integers. Finally clauses can span several lines and are ended by a '0'.
- SMTLIB version 2
  There is a very complete documentation online (smtlib.org). We aim at full support.
- TPTP

The behaviour of the tool will depend on the kind of input file. On a DIMACS problem, this
will act as a SAT solver for the given problem. On the smtlib, it will execute the smtlib2 
script from the input file. On TPTP, this will try to solve the TPTP file.

Another mode is as a DSL in the Scala REPL. This is expected to provide many primitive to
do symbolic manipulations of formulas and terms and, combined with the powerful programming
environment of Scala, should make a solid tool to solve various problems. Potentially this could
look like an interactive theorem prover in that mode ?

A third alternative to use the tool is as a API for Scala programs.

renaming smt to dp
------------------

dp stands for decision procedure and seems more general and standard.
