Require Import FunInd Extraction.
Declare ML Module "relation_extraction_plugin".

Parameter generic_eq_bool : forall A, A -> A -> bool.
Extract Inlined Constant generic_eq_bool => "Pervasives.(=)".
