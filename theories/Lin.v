From mathcomp.ssreflect Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Require Import FinMap.finmap. *)
Require Import FinMap.ordtype.

Require Import SendRec.Env.
Require Import SendRec.AtomScopes.


Inductive tp : Set :=
| C : tp
| lolly : tp -> tp -> tp
.
Notation "t -o u" := (lolly t u) (at level 67).

Fixpoint eq_tp (T T' : tp): bool :=
  match T, T' with
  | C, C => true
  | (T1 -o T1'), (T2 -o T2') => eq_tp T1 T2 && eq_tp T1' T2'
  | _, _ => false
  end
.

(* Lemma eq_imp_eq T T': eq_tp T T' -> T = T'. *)
(* Proof. *)
(*   elim T ; elim T'=>//. *)
(*   move=> T0 H0 T1 H1 T2 H2 T3 H3. *)
(*   have: (eq_tp (T2 -o T3) (T0 -o T1) = eq_tp T2 T0 && eq_tp T3 T1) by []. *)
(*   move=>->=> Hs. *)

Lemma tp_reflect: Equality.axiom eq_tp.
Proof.
(*   move=>T T'. *)
(*   apply: (iffP idP)=>[|<-]. *)

(*   elim T ; elim T' ; try constructor=>//. *)
(*   move=> T3 H3 T0 H0 T1 H1 T2 H2. *)
Admitted. (* hiding from shamer *)

Canonical tp_eqMixin := EqMixin tp_reflect.
Canonical tp_eqType := Eval hnf in EqType tp tp_eqMixin.

Module Var := AtomScope Atom.Atom.
Canonical Var_atom_eqType := EqType Var.atom Var.atom_eqMixin.
Canonical Var_atom_ordType := OrdType Var.atom Var.atom_ordMixin.
Coercion Var.Free : Var.atom >-> Var.var.
Coercion Var.Bound : nat >-> Var.var.
Canonical Var_var_eqType := EqType _ Var.var_eqMixin.

Inductive tm : Set :=
| c
| v : Var.var -> tm
| app : tm -> tm -> tm
| lam : tm -> tm
.

Fixpoint open (n : nat) (u : tm) (t : tm) : tm :=
  match t with
  | c => c
  | v x => Var.open_var v n u x
  | app t t' => app (open n u t) (open n u t')
  | lam t => lam (open (S n) u t)
  end
.

Notation "t ^ u" := (open 0 u t).

Inductive lc : tm -> Prop :=
| lc_c: lc c
| lc_var i :  (lc (v (Var.Free i)))
| lc_app t t' : lc t -> lc t' -> lc (app t t')
| lc_lam t (L : seq Var.atom): (forall a, a \notin L -> lc (t ^ (v a))) -> lc (lam t)
.

Definition body t := forall (L : seq Var.atom) a, a \notin L -> lc (t ^ (v a)).


Fixpoint subst (a : Var.atom) (u : tm) (t : tm) : tm :=
  match t with
  | c => c
  | v (Var.Free b) => if a == b then u else t
  | v _ => t
  | app t t' => app (subst a u t) (subst a u t')
  | lam t => lam (subst a u t)
  end
.

Definition ctx_entry := tp.
Definition ctx := @env Var_atom_ordType tp_eqType.

Inductive oft : forall (G : ctx), tm -> tp -> Prop :=
| t_c: oft nil c C
| t_v a T: oft (add a T nil) (v a) T
| t_app G G' t t' T T': oft G t (T -o T') -> oft G' t' T -> oft (G \:/ G') (app t t') T'
| t_lam G (L : seq Var.atom) t T T':
    (forall a, a \notin L -> oft (add a T G) (t ^ (v a)) T') ->
    oft G (lam t) (T -o T')
.

(* for now only prove the substitution lemma *)
(* Inductive red: tm -> tm -> Prop := *)
(* | r_beta t t': body t -> lc t' -> red (app (lam t) t') (t ^ t) *)
(* | r_app_1 t t' t'':  lc t'' -> red t t' -> red (app t t'') (app t' t'') *)
(* . *)

Lemma ctx_uniqness G G' t T:
  oft G t T -> oft G' t T -> G = G'.
Proof.
  move=>H1 H2. move:H1 G' H2.

  elim; intros.


  by inversion H2.

  by inversion H2.
  inversion H3.
  subst.
  have: (G0=G1).
  apply H0.



  Lemma type_uniqueness G t T T':
  oft G t T -> oft G t T' -> T=T'.
Proof.
  move=> Hoft. move:Hoft T'.
  elim.

  + move=>G' T' Hoft.
  by inversion Hoft.
  + move=> a T0 T' Hoft.
  by inversion Hoft.

  + move=>G0 G' t0 t' T0 T' T0' Hoft Hoft' Hoft''.
    admit.

  + intros.
    inversion H1 ; subst.
    have Hnotin := Var.fresh_not_in (L ++ L0).
    move:(OddsAndEnds.not_in_app Hnotin). case=> Hnot1 Hnot2.

    have:(T0=T1).


    have:(T'=T'1).
    apply: H0.

    apply Hnot1.

    move: (H4 (Var.fresh (L++L0)) Hnot2).

    admit.
    move=>->.

Lemma subst_lemma G G' t T a t' T':
  def (G \:/ G') ->
  oft G t T -> oft (add a T G') t' T' -> oft (G \:/ G') (subst a t t') T'.
Proof.
  move=> Hdef Hs H.
  move:H G Hdef Hs.
  elim.
  + by move=>_ G _ _ ; apply: t_unit.

  + move=> b Tb G Hdef Hoft.



    case: (boolP (a == b)).
    move/eqP=>->.



    rewrite/subst eq_refl.