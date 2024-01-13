# PR2 final project - OCaml Interpreter

## Interpreter
The interpreter is based on the didactic language, which has been extended with expressions tuples, function concatenation and iterative functions.

We assume all the functions can be applied to a single parameter which is not one of the following:
- `Etup(_)`
- `Pipe(_)`
- `ManyTimes(_)`

The `eval` type has been extended with the `Tup` constructor representing a closure for function concatenation.

The function `sem(e,r)` has been extended with patterns for `Etup(t)`, `Pipe(t)`, `ManyTimes(n,f)`. These expressions are evaluated, respectively, by the functions `tup_list(t)` without functional values control, `tup_list(t)` with functional values control, `n_times(n,foo)`.

The functions which have been added to the didactic language are:
- `reverse l`: auxiliary function for the evaluation of function concatenation. It inverts the functional closures to apply the results of a function to the next one. It also checks that elements of the list of closures are functional values.
- `tup_list t`: function with a `tuple` parameter, builds a list from the evaluation of the expressions contained in the `tuple` parameter. This function is used in the evaluation of `Etup(t)` and `Pipe(t)`. The only difference is that in the evaluation of `Pipe(t)` it also checks that elements are functional values.
- `sem_list lst v`: auxiliary function for function concatenation. It applies every function in `lst` to the result of the next function in `lst`. The last function is applied to `v`.
- `n_times(n,e)`: builds a list of length `n` with all the elements equal to evaluation of expression `e`.

## Exceptions
Exceptions have been defined to signal errors in the construction of expressions.

In particular:
- `Unbound(s)`: signals that an undefined identifier is being used.
- `UnknownType(s)`: signals that an undefined type is being used.
- `TypeError(s)`: signals a type mismatch in the expression.
- `NonFunctionalValue(s)`: signals that a non-functional value is being used where one is required.

## Tests
All the tests are at the bottom of the interpreter file.

Every test has a comment with the expected results. The execution of every test is followed by a print indicating if the test failed or passed.