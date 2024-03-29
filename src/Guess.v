From Coq Require Import Arith String Streams.
From FreeSpec.Core Require Import Core CoreFacts.
From FreeSpec.FFI Require Import FFI.
From ffi Require Import Console.

Open Scope i63_scope.

(** * Specifying the Guess Game *)

Generalizable All Variables.

(** * Definition of a semantic for the [CONSOLE] interface *)
CoFixpoint console (in_flow : Stream i63) (out_flow : list string)
  : semantics (CONSOLE) :=
  mk_semantics (fun α (c : CONSOLE α) =>
                  match c with
                  | Read_int _ => (
                      Streams.hd in_flow,
                      console (Streams.tl in_flow) out_flow
                    )
                  | Write s => (
                      tt, console in_flow (s :: out_flow)
                    )
                  end).

Fixpoint guess `{MonadConsole m, Monad m} (target : i63) (max_attempt : nat)
  : m unit :=
  match max_attempt with
  | O => write "Game Over: max attempt limit exceeded"
  | S m =>
    let* _ := write "Guess the number:" in
    let* g := read_int tt in
      if (g =? target)%i63 then
        write "Won !"
      else if (g <? target)%i63 then
        write "The target is greater";;
        guess target m
      else
        write "The target is smaller";;
        guess target m
  end.

Inductive game_state : Type :=
| Won : game_state
| GameOver : game_state
| GSmall : game_state
| GBig : game_state
| GEqual : game_state.

Record game : Type := mkGame
  { target : i63
  ; max_attempt : nat
  ; state : game_state
  }.

(** Simplified witness states *)
Inductive guess_state : Type :=
| Retry : guess_state
| Guessed : guess_state.

Definition guess_update (target : i63)
  (g : guess_state) (α: Type) (c : CONSOLE α) (x : α) : guess_state :=
  match g,c,x with
  | Retry, Read_int _, n =>
    if (n =? target) then Guessed else Retry
  | _, _, _ => g end.

Inductive guess_caller_obligation : guess_state ->
    forall (α : Type), CONSOLE α -> Prop :=
  (* can always retry for now *)
  | retry (u : unit) (g : guess_state)
    : guess_caller_obligation g i63 (Read_int u)

  (* write 'Won !' iff the target is guessed *)
  | write_won_iff_guessed (msg : string) (g : guess_state)
                          (H : g = Guessed <-> msg = "Won !")
    : guess_caller_obligation g unit (Write msg).

Definition guess_contract (target : i63) : contract CONSOLE guess_state :=
  {| witness_update := guess_update target
   ; caller_obligation := guess_caller_obligation
   ; callee_obligation := no_callee_obligation
  |}.

(** * Proofs of guess_contract respectation by the program *)

(* always allow retry (read_int) *)
Lemma allow_retry `{Provide ix CONSOLE} (g : guess_state) (u : unit)
  : forall t : i63, pre (to_hoare (guess_contract t) (read_int u)) g.
Proof.
  intro t.
  prove impure.
  constructor.
Qed.

Lemma guess_respectful `{Provide ix CONSOLE} (g : guess_state)
    (init : g = Retry) (max_attempt : nat)
  : forall t : i63, pre (to_hoare (guess_contract t) (guess t max_attempt)) g.
Proof.
  intro t.
  induction max_attempt.
  - prove impure. constructor. ssubst. split; now intro.
  - prove impure;
    try (ssubst; constructor);
    try (unfold guess_update; rewrite equ_cond);
    ssubst; try now trivial. all: cbn.
    all: now rewrite equ_cond.
Qed.

(** * Aux functions to generate infinite flows *)
CoFixpoint rep_inf {A : Type} (n:A) : Stream A :=
  Cons n (rep_inf n).

CoFixpoint i63_inf (n : i63) : Stream i63 :=
  Cons n (i63_inf (n + 1)).

(** * Execution examples *)
Definition base_semantic := console (i63_inf 0) [].

(* Compute (eval_effect base_semantic (Read_int _)). *)
(* >> 0

Compute (exec_effect base_semantic (Write "hello world !")).
(* >> _ ["hello world !"] *)

Compute (exec_impure (console (rep_inf 10) []) (guess 10 20)).
(* >> out_flow: ["Won !"; "Guess the number:"] *)

Compute (exec_impure (console (rep_inf 10) []) (guess 30 20)).
(* >> out_flow: ["The target is greater";...] *)

Compute (exec_impure (console (nat_inf 20) []) (guess 15 10)).
>> out_flow: ["Game Over: max attempt limit exceeded";...] *)
