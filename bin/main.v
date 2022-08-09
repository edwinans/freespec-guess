From Coq Require Extraction.
From ExtLib Require Import MonadFix.
From SimpleIO Require Import SimpleIO.
From CoqFFI Require Import Int.
From Guess Require Import Guess.

Definition main : io_unit :=
  let target : i63 := 5 in
  let max_attempt : nat := 10%nat in
  IO.unsafe_run (guess target max_attempt).

Extraction "main.ml" main.
