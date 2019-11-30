Require Import RelationExtraction.

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

Extraction Relation (even [1 2] as "ev") (odd [1 2] as "od").

