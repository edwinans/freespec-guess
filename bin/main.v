From Coq Require Extraction.
From ExtLib Require Import MonadFix.
From SimpleIO Require Import SimpleIO.
From FreeSpec.Example.Guess Require Import Guess.
From CoqFFI Require Import Int.

Definition main : io_unit :=
  let target : i63 := 2 in 
  let max_attempt : nat := 10%nat in
  IO.unsafe_run (guess target max_attempt).

Extraction "main.ml" main.
