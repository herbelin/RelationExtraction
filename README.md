# User Manual for Extraction from Inductive Specifications

## Installation

### Prerequisites
You need to have OCaml and Coq >= 8.9.
The COQBIN (/usr/local/bin/ by default) and the COQDIR (/usr/local/
by default) environment variables must be set prior to use this plugin.
For example in a linux environment, type the following lines in a bash terminal or in the .bashrc file

```
export COQBIN=/usr/local/bin/
```

### Building the plugin
Simply type `make` in the plugin source directory. This will build the
plugin and launch a test suite, which contains many examples.
Be sure the version of OCaml used to compile Coq is the one used to compile the plugin.

Type `make install` to make the plugin available to the corresponding version of Coq.

## Usage
First of all, many examples are given in the ``test`` directory. They show
many possible usages of the plugin. To use the plugin in a Coq file, you need
to add this line at top of this file:

    From RelationExtraction Require Import RelationExtraction.

Then the relation extraction commands can be used everywhere in the
file.

## Extraction to OCaml
The syntax of the command is:

    Extraction Relation [Single] [Relaxed] (rel mode as "f") [(rel1 mode1 as "f1") (rel2 mode2 as "f2") ...]

where rel, rel1, rel2 are inductive definitions of relations and mode, mode1,
mode2 their respective extraction modes. The extracted function names can be omitted
as in the following command (the names of the extracted functions are then obtained by concatenating the name of the inductive relation and the mode):

    Extraction Relation [Single] [Relaxed] (rel mode) (rel1 mode1)

When the Single flag is set, the plugin
only extracts the first relation (rel) whereas when it is not set, all the
relations and their dependencies (Fixpoints, Definitions, Inductive data types)
are extracted.

The Relaxed flag activates an optimisation relative to non-deterministic specifications.
(see [1] for further details on non-deterministic specifications) 

Modes are given as an integer list ([1], [1 3] for examples). 
Each integer denotes an argument (of the inductive relation) position, starting with 1.

This command produces OCaml code on the standard output. 

## Extraction to Haskell
Please type the following line before using the previously described command:

    Extraction Language Haskell.

## Extraction to Coq

The syntax of the command is:

    Extraction Relation Fixpoint [Relaxed] (rel mode [termination hint] as "f") [(rel1 mode1 [termination hint] as "f1") ...]

If the termination argument is not specified, the first argument of the expected Coq functions is assumed 
to be the decreasing argument.
If a termination hint is provided, it may be one of the following:
- Struct n: the nth argument of the expected Coq functions is assumed to be the decreasing argument,
- Counter: the expected Coq functions are Fixpoints using a supplementary argument which is a counter 
decreasing at each recursive call. 


The same convention for names of extracted functions as in OCaml applies in Coq. 
To see the extracted functions, use Print.

For the moment, soundness proofs are produced in the simplest cases (see [1] for further details). 

## License

This program is free software: you can redistribute it and/or modify it under the terms of the 
GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or 
(at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of 
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details. 

You should have received a copy of the GNU General Public License 
along with this program. If not, see <http://www.gnu.org/licenses/>. 

Copyright 2011, 2012, 2013, 2014 
Catherine Dubois CNAM-ENSIIE
David Delahaye CNAM
Pierre-Nicolas Tollitte

## Contacts

Catherine Dubois <catherine.dubois@ensiie.fr>
David Delahaye <david.delahaye@cnam.fr> 
Pierre-Nicolas Tollitte <pierrenicolas.tollitte@gmail.com>


[1] P.-N. Tollitte, D. Delahaye, C. Dubois. Producing Certified Functional Code from Inductive
Specifications. International Conference on Certified Programs and Proofs (CPP 2012), december 2012,
Vol. 7679, Series LNCS, pp. 76-91, Kyoto, Japan
