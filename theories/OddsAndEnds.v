(* General lemmas and definitions that don't belong anywhere *)

From mathcomp Require Import all_ssreflect.

Require Import FinMap.ordtype.

Set Implicit Arguments.
Unset Strict Implicit.
(* Import Prenex Implicits. *)
(* Unset Printing Implicit Defensive. *)

Lemma neqC {A : eqType} (x y : A) : x != y -> y != x.
Proof.
    by rewrite eq_sym.
Qed.

Lemma notin_cons {A : eqType} x y (L : seq A) : x \notin y :: L -> x != y /\ x \notin L.
Proof. by rewrite in_cons negb_or =>/andP. Qed.

(* TODO rename to notin_app or at least similarly to notin_cons (previous lemma) *)
Lemma not_in_app {A : eqType} (x : A) L L':
  x \notin L ++ L' -> x \notin L /\ x \notin L'.
Proof. by rewrite mem_cat negb_or => /andP. Qed.

(* Some lemmas about predicates (quite simple ones) *)

Lemma in_predU_l {T : eqType} (k : T) P Q : k \in P -> k \in predU P Q.
  do 2! rewrite/(_\in_).
  rewrite/predU.
  simpl=>->.
  by rewrite Bool.orb_true_l.
Qed.

Lemma in_predU_r {T : eqType}(k : T) P Q : k \in Q -> k \in predU P Q.
  do 2! rewrite/(_\in_).
  rewrite/predU.
  simpl=>->.
  by rewrite Bool.orb_true_r.
Qed.

Lemma notin_predU {T : eqType}(k : T) P Q : k \notin P -> k \notin Q -> k \notin predU P Q.
Proof.
  do !rewrite/(_\notin_)/predU/(_\in_) ; simpl.
  elim (P k)=>//.
Qed.
