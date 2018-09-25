https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html

Import String from Coq's Strings module.

Define 'beq_string' which uses 'string_dec' and output 'true' whenever two strings are equal.

Prove the following theorems:
* `beq_string_refl`: for any string `s`, `beq_string s s` outputs `true`
* `beq_string_true_iff`: `beq_string` outputs `true` iff the strings are equal
* `beq_string_false_iff`: `beq_string` outputs `false` iff the strings are not equal
* `false_beq_string`: When two strings are not equal, `beq_string` outputs `false`

Hint : when one theorem proves an iff, and another theorem ask to prove only one direction, rewriting of the iff can be used.
I.e. `rewrite` works on equality, but also on equivalences.

Define `total_map` as functions which map strings to value of some type.

Define the empty map `t_empty` as a total_map which maps everything to the same supplied value.

Define `t_update` as a function which takes a total_map `m` as input, a string `s` and a value `v`, and outputs a total map which does the same thing as `m`, except that it outputs `v` for `s`.

Define `partial_map` as total_map which works other options.

Define `empty` as a function which always outputs `None`. Use `t_empty` to define `empty`.

Use `t_update` to define `update` which works other `partial_map`.
