The 'left', 'right', and 'split' tactics are equivalent to using the 'constructor' tactic.

The 'and' and 'or' functions are defined inductively.

'or' has two constructors each with one prerequisite, and 'and' has one constructor with two prerequisite.

'left' is equivalent to 'constructor 1' and invokes the first constructor
'right' is equivalent to 'constructor 2' and invokes the second constructor
'split' is equivalent to 'constructor' (or 'constructor 1' ?) because it expects only one constructor.

This means that 'left' can be used with any inductive types that has at least one constructor (i.e. all of them).
And 'right' can be used with any inductive types that has at least two constructors.
'split' can be used with any inductive type.

In most cases, such uses of the 'left', 'right' and 'split' tactics would be quite curious. I.e. natural integers have two constructors, but they are not usually regarded as a disjunctive inductive type.

But this is to show that the 'constructor' tactic is more fundamental that 'left', 'right' and 'split'.

This is also to record the fact that I peered into Coq source code to see how these two ('left' and 'right') tactics were defined.

I didn't investigate 'split', but it should be quite similar, i.e. either 'constructor' or 'constructor 1'.