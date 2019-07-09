(* Atoms for locally nameless *)

(* imports from ssreflect *)
(* From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype seq. *)
(* (* Set Implicit Arguments. *) *)
(* (* Unset Strict Implicit. *) *)
(* (* Unset Printing Implicit Defensive. *) *)

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq path.

Require Import FinMap.ordtype.

Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Type ATOM.

  Parameter atom : Set.
  Definition t := atom.

  (* atoms can be compared to booleans *)

  Parameter eq_atom : atom -> atom -> bool.
  Parameter eq_reflect : forall (a b : atom), ssrbool.reflect (a = b) (eq_atom a b).
  Parameter atom_eqMixin : Equality.mixin_of atom.
  Canonical atom_eqType := EqType atom atom_eqMixin.


  (* atoms can be ordered with an irreflexive order *)

  Parameter ltn : atom -> atom -> bool.
  Parameter ltn_irreflexive : forall x : atom, ltn x x = false.
  Parameter ltn_transitive : forall y x z : atom,
      ltn x y -> ltn y z -> ltn x z.
  Parameter ltn_total : forall a b : atom, [|| ltn a b, eq_atom a b | ltn b a].
  Parameter atom_ordMixin : Ordered.mixin_of atom_eqType.
  Canonical atom_ordType := OrdType atom atom_ordMixin.

  Parameter fresh : seq atom -> atom.

  Parameter fresh_not_in : forall l, (fresh l) \notin l.

  Parameter nat_of : atom -> nat.
End ATOM.

Module Atom : ATOM.

  (* begin hide *)
  Definition atom := nat.
  Definition t := atom.

  Definition eq_atom (a b : nat) : bool := ssrnat.eqn a b.

  Lemma eq_reflect a b :  ssrbool.reflect (a = b) (eq_atom a b).
  Proof.
    apply: ssrnat.eqnP.
    (* move=> a b ; apply: ssrnat.eqnP. *)
  Qed.

  Definition atom_eqMixin := EqMixin Atom.eq_reflect.
  Canonical atom_eqType := EqType atom atom_eqMixin.

  (* equality and ordered *)

  Definition ltn a b := a  < b.
  Lemma ltn_irreflexive : forall x : nat, x < x = false.
  Proof.
    intros ; apply ssrnat.ltnn.
  Qed.

  Definition ltn_transitive := ssrnat.ltn_trans.

  Lemma ltn_total : forall a b : nat, [|| a < b, a == b | b < a].
  Proof.
    move=> a b.
    rewrite/lt/eq.
    case ssrnat.ltngtP ; move=>H ; intuition ; rewrite Bool.orb_comm ; intuition.
  Qed.

  Definition atom_ordMixin : Ordered.mixin_of atom_eqType :=
    @OrdMixin
      atom_eqType
      ltn
      ltn_irreflexive
      ltn_trans
      ltn_total.
  Canonical atom_ordType := OrdType atom atom_ordMixin.
  (* Lemma silly (m n : nat) : m == n -> m = n. *)
  (*   apply: eqP. *)
  (* Qed. *)

  (* Lemma sillier p q : p || q -> p \/ q. *)
  (*   apply: orP. *)
  (* Qed. *)

  (* Lemma nat_list_max (xs : seq nat) : (* forall (xs : list nat), *) *)
  (*     { n : nat | forall x, x \in xs -> x <= n }. *)
  (* Proof. *)
  (*   elim xs=>//. *)
  (*   exists 0 ; move=>x H. *)
  (*   by inversion H. *)

  (*   move=> a l H. *)
  (*   have H':=H. *)
  (*   destruct H. *)
  (*   rename x into max_l. *)
  (*   exists (maxn max_l a). *)
  (*   move=>y Hy. *)

  (*   have Hy' := Hy. *)
  (*   rewrite in_cons in Hy. *)

  (*   apply sillier in Hy. *)
  (*   destruct Hy. *)
  (*   apply silly in H. *)
  (*   rewrite H. *)
  (*   (* not provable at this point *) *)
  (* Abort. *)

  (* Lemma atom_fresh_for_list : *)
  (*   forall (xs : list nat), { n : nat | ~ List.In n xs }. *)
  (* Proof. *)
  (*   intros xs. destruct (nat_list_max xs) as [x H]. *)
  (*   exists (S x). intros J. lapply (H (S x)). omega. trivial. *)
  (* Qed. *)

  (* Definition fresh (l : list atom) := *)
  (*   match atom_fresh_for_list l with *)
  (*     (exist   x _) => x *)
  (*   end. *)

  Fixpoint fresh' a (l : seq atom) :=
    match l with
    | [::] => a +1
    | x::xs => fresh' (maxn x a) xs
    end.

  Definition fresh l := fresh' 0 l.

  Lemma fresh_not_head a a' l : a <= a' -> fresh' a' l != a.
  Proof.
    elim: l a' => [|  a'' l IHl] a' Le_a_a'.
      by rewrite /fresh' neq_ltn addn1 ltnS orb_idl.
    by rewrite /fresh' maxnC; apply IHl; rewrite leq_max orb_idr.
  Qed.

  Lemma fresh_not_in l : fresh l \notin l.
  Proof.
    suff fresh'_not_in a : fresh' a l \notin l by apply fresh'_not_in.
    elim: l a =>  // a' l IHl a.
      by rewrite /fresh/fresh' in_cons Bool.negb_orb fresh_not_head ?(IHl (maxn a' a)) ?leq_maxl.
  Qed.

  Definition nat_of (x : atom) := x.
  (* end hide *)
End Atom.

(** We make [atom], [fresh], [fresh_not_in] and [atom_fresh_for_list] available
    without qualification. *)

Notation atom := Atom.atom.
Notation fresh := Atom.fresh.
Notation fresh_not_in := Atom.fresh_not_in.
(* Notation atom_fresh_for_list := Atom.atom_fresh_for_list. *)

Canonical atom_eqType := EqType Atom.atom Atom.atom_eqMixin.
Canonical atom_ordType := OrdType Atom.atom Atom.atom_ordMixin.
