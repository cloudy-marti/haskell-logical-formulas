
# Haskell Project
## Mathematical Logic and Formulas

This is the final project on the Haskell and Functional Programming course of the 3rd Year of IT Engineering Course in the ESIPE school, University Gustave Eiffel, France.

This project has been developed by the trainees: Emilie Marti and Vincent Agullo.

In this project we discovered the mathematical logical formulas and how to program them using Haskell.

### Structure of the project
Source code can be found on the package ``src/Data/Logic`` on the following files:
* **Var.hs**

Haskell file with the definition of the Var type (given by the teacher).

* **Fml.hs**

Haskell file with the definition of all the formula transformation functions and testing.

* **Combinator.hs**

Haskell file with the definition of the *utils* functions, which are mostly combinatory functions that gives the user a formula from a list of Var's.

A battery of tests using the ``Test.HUnit`` library has been also developed to test all the functions of ``Fml.hs`` and ``Combinator.hs``. It can be found on the package ``test/Data/Logic`` on the following file:
* **Spec.hs**

Haskell file with multiple tests for each newly developed functions from ``Fml.hs`` and ``Combinator.hs``. Variables are declared on top of the file and reused throughout all the tests. Those tests are then added to a ``TestList`` that is ran on a main function.

### How to
To build and test this project, please go on the root of the project (directory hs-solver) and follow the instructions below.

Please make sure you have stack installed.

* **Build**
```bash
$ stack build
```

* **Run on terminal**
```bash
$ stack -- exec ghci
# Enter the Haskell console and import Libraries
Prelude> import qualified Data.Logic.Var as Var
Prelude Var> import qualified Data.Logic.Fml as Fml
Prelude Var Fml> import qualified Data.Logic.Combinator as Comb
# Now you can test your fonctions using Var.fnc / Fml.fnc / Comb.fnc
Prelude Var Fml Comb>
```
* **Test**

You can run the given tests directly by simply doing the following command:
```bash
stack test
```
