https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

Define an inductive type for arithemtic expressions, of type Type, with four constructors :
one for integers, taking an integer,
and three for addition, substraction and multiplication.

Do the same for boolean expressions, with two constructors for true and false, and four constructors for equality, negation, conjunction and less-or-equal. Use arithmetic expressions in place of integers.

Define two evaluation functions for arithmetic expressions and boolean expressions.
Use beq_nat for equality, leb for comparison, negb and andb for negation and conjunction.

Define a function to optimize out zeros in arithmetic expressions.

Check that the optimization is sound.

Define inductive relations which correlates arithmetic expressions and integers, and boolean expressions and booleans.

Check that the evaluations functions and the relations do the same thing.



Add the concept of identifier.

Add an inductive type for commands : skip, assignment, sequence, conditionals and loops.

Define the evaluation relation for commands.

Check that evaluation is deterministic.

-----------------------------------------------------------------------------------------------------------------

Module MSkip

Define the concept of `state`, as total maps to integers.

Define an inductive type `com` for commands, with a constructor `CSkip` which skips.

Define a relation `ceval` over commands, source states and destination states, with constructor `E_Skip`.

Check that ceval is deterministic, which means that for any commands, if the source states are the same, then the final states must be the same.

Check that all programs in this language do not change the state.

End Module

-----------------------------------------------------------------------------------------------------------------

Module MAssignment

