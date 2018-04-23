## Cedille-Core Modification

This is a modification of [MaiaVictor's](https://github.com/MaiaVictor) [Cedille-Core](https://github.com/MaiaVictor/cedille-core) implementation which adds support for [Dhall](https://github.com/dhall-lang/dhall-haskell)-style "IO". See MaiaVictor's original repository for more information.

I mainly made this as a simple prototype to explore usability issues. I'll spend some time in the future making a small library for this language, but without some facilities for producing certificates for checked and evaluated files, this isn't practically efficient enough. However, if this is to be used as some sort of standard for interchanging specification of functions, this is the right way of doing imports and dependancies, in my opinion. See the [Dhall tutorial](https://hackage.haskell.org/package/dhall-1.12.0/docs/Dhall-Tutorial.html#g:3) for more information.

## IO Usage

This version now supports references to file names directly within files by surrounding them with apostrophes. Those file names will then be interpreted as the contents of the files they refer to. For example, in the example's folder is the file `and.ced` which references `Bool.ced` using `'Bool'`. After the main file is compiled, one can run `main "//'and' 'true' 'false'"` in the examples directory, getting back the normal-form of false as an output.

In general, text can be piped into the binary executable to get some output.

One can check types using the `the.ced` file. It contains a simple dependent identity type which takes a type `T` and an element `t` of type `T`. Running `main "//'the' 'Bool' 'true'"` returns basic information about the contents of `true.ced`, but running `main "//'the' 'Nat' 'true'"` gives a null-value for the type since the file doesn't type-check.

