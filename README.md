## intuitionistic-theorem-proving
The Python code from my Senior Research Project about Automated Theorem Proving in Intuitionistic Propositional Logic.

#### start.py
The main program with the `Sequent` class, all the rules of inference, and all three provers. If you actually want to use a prover, run `start.py` and then type statements of the form `prove(~(p|q) >> (~p & ~q))`. Logical connectives are `&` and, `|` or, `>>` implies, `~` not, and `-` iff. Optional `method` argument lets you specify which prover to use -- the options are `randomDFS`, `randomDFS_noRepeats`, or `randomDFS_LJT` (default).

#### sat.py
Contains the Boolean SAT solver used by `start.py` to check if statements are tautologies in classical logic.

#### tests.py
Contains selected propositional SYJ tests from the Intuitionistic Theorem Proving Library and a driver to time all three methods. When aborting a run, make sure to call `reset()` so that the `subprocess` module doesn't continue running in the background.

#### percent_intuit.py
Code to generate random binary trees and random propositional formulas. Includes a driver to test the proportion of tautologies that are intuitionistically true.

#### polarity.py
Unfinished code I was using to test out the polarity with focusing technique that the [Imogen](https://link.springer.com/chapter/10.1007/978-3-540-89439-1_12) automated prover uses. Never implemented into a working prover.

#### permutations.py
Code I used before writing `tests.py` to measure the efficiency of the provers on and/or permutations.
