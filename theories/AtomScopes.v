From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import FinMap.finmap.
Require Import FinMap.ordtype.

Require Import SendRec.Atom.

(* CoInductive Atom {n : nat} : Set := *)
(* | atom : atom -> Atom *)
(* . *)

(* (* Atoms inherit their equality from atoms *) *)
(* Definition eq_Atom {n} (a b : @Atom n) : bool := *)
(*   match a, b with *)
(*   | atom a, atom b => a == b *)
(*   end. *)

(* (* Lemma eq_reflect_Atom {n} a b :  ssrbool.reflect (a = b) (@eq_Atom n a b). *) *)
(* Lemma eq_reflect_Atom {n} : Equality.axiom (@eq_Atom n). *)
(* Proof. *)
(*   case => x [] y /= ; apply: (iffP eqP) ; congruence. *)
(* Qed. *)

(* Definition Atom_eqMixin {n} := EqMixin (@eq_reflect_Atom n). *)
(* Canonical Atom_eqType {n} := EqType (@Atom n) (@Atom_eqMixin n). *)

(* (* Atoms also inherit their order from atoms *) *)

(* Definition Atom_ltn {n} (a b : @Atom n) := *)
(*   let: (atom a, atom b) := (a, b) in Atom.ltn a b. *)

(* Lemma Atom_ltn_irreflexive {n} : irreflexive (@Atom_ltn n). *)
(* Proof. *)
(*   by case ; rewrite/Atom_ltn ; apply: Atom.ltn_irreflexive. *)
(* Qed. *)

(* Lemma Atom_ltn_transitive {n} : transitive (@Atom_ltn n). *)
(*   case => a [] b [] c ; rewrite/Atom_ltn ; apply: Atom.ltn_transitive. *)
(* Qed. *)

(* Lemma Atom_ltn_total {n} (a b : @Atom n): [|| Atom_ltn a b, eq_Atom a b | Atom_ltn b a]. *)
(*   case a ; case b. rewrite/Atom_ltn/eq_Atom. (* this is annoying, but it should be easy!!! why?? *) *)
(* Admitted. *)

(* Definition Atom_ordMixin {n} : Ordered.mixin_of (@Atom_eqType n) := *)
(*   @OrdMixin *)
(*     Atom_eqType *)
(*     Atom_ltn *)
(*     Atom_ltn_irreflexive *)
(*     Atom_ltn_transitive *)
(*     Atom_ltn_total. *)

(* (* Definition N1 := @Atom 1. *) *)

(* (* Definition N2 := @Atom 2. *) *)


(* (* Definition n1 : N1 := atom a. *) *)

(* (* Definition n1' : N1 := atom a. *) *)

(* (* Definition n2 : N2 := atom a. *) *)

(* (* Goal n1 = n1'. *) *)
(* (*   by []. *) *)
(* (* Qed. *) *)

(* (* Compute n1 == n1'. *) *)
(* (* Goal n1 = n2. *) (* this does not work *) *)


(* Inductive name {n} : Set := *)
(*   | fnm : @Atom n -> name *)
(*   | bnm : nat -> name *)
(* . *)

(* Definition eq_nm {n} (a b : @name n) : bool := *)
(*   match a, b with *)
(*   | fnm u, fnm s => u == s *)
(*   | bnm i, bnm j => i == j *)
(*   | _, _ => false *)
(*   end. *)

(* Lemma nm_reflect {n} : Equality.axiom (@eq_nm n). (* (a b : : reflect (a = b) (eq_nm a b). *) *)
(* Admitted. *)

(* Definition nm_eqMixin {n} := EqMixin (@nm_reflect n). *)
(* Canonical nm_eqType {n} := EqType _ (@nm_eqMixin n). *)

(* Coercion bnm : nat >-> name. *)
(* Coercion fnm : atom >-> name. *)

(* A hack to have different types of atoms taking advantage of module
   generativity *)

Module Type ATOMSCOPE.

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

  Inductive var :=
  | Free of atom (* a variable waiting to be instantiated *)
  | Bound of nat (* a bound variable *)
  .

  (* get bound variable that is free under 'k' binders *)
  Definition get_free_bound (k : nat) (v : var) : option nat :=
    match v with
    | Bound k' => if k' >= k then Some (k' - k) else None
    | _ => None
    end.

  Definition eq_var (a b : var) : bool :=
    match a, b with
    | Free a, Free b => a == b
    | Bound i, Bound j => i == j (* PeanoNat.Nat.eqb i j *)
    | _, _ => false
    end.

  Parameter var_reflect : Equality.axiom eq_var.

  Definition var_eqMixin := EqMixin var_reflect.
  Canonical var_eqType := EqType _ var_eqMixin.

  Definition open_var A (f : var -> A) (n : nat) (x : A) (y : var) : A :=
    match y with
    | Bound n' => if n == n' then x else f y
    | _ => f y
    end.

  Inductive lc_var : var -> Prop :=
  | lc_free : forall a, lc_var (Free a).
  Hint Constructors lc_var.

  Definition lcb_var v : bool :=
    match v with
    | Free _ => true
    | _ => false
    end.

  Parameter getfree_lc : forall v, get_free_bound 0 v == None -> lc_var v.
  Parameter lc_getfree : forall v, lc_var v -> get_free_bound 0 v == None.

  Parameter lc_varP : forall v, reflect (lc_var v) (lcb_var v).

End ATOMSCOPE.

Module AtomScope (A : ATOM) : ATOMSCOPE.

  Definition atom := A.atom.
  Definition t := A.t.

  (* atoms can be compared to booleans *)

  Definition eq_atom : atom -> atom -> bool := A.eq_atom.
  Definition eq_reflect : forall (a b : atom), ssrbool.reflect (a = b) (eq_atom a b) := A.eq_reflect.
  Definition atom_eqMixin : Equality.mixin_of atom := A.atom_eqMixin.
  Canonical atom_eqType := EqType atom atom_eqMixin.


  (* atoms can be ordered with an irreflexive order *)

  Definition ltn : atom -> atom -> bool := A.ltn.
  Definition ltn_irreflexive : forall x : atom, ltn x x = false := A.ltn_irreflexive.
  Definition ltn_transitive : forall y x z : atom,
      ltn x y -> ltn y z -> ltn x z := A.ltn_transitive.
  Definition ltn_total : forall a b : atom, [|| ltn a b, eq_atom a b | ltn b a] := A.ltn_total.
  Definition atom_ordMixin : Ordered.mixin_of atom_eqType := A.atom_ordMixin.
  Canonical atom_ordType := OrdType atom atom_ordMixin.

  Definition fresh : seq atom -> atom := A.fresh.

  Definition fresh_not_in : forall l, (fresh l) \notin l := A.fresh_not_in.

  Definition nat_of : atom -> nat := A.nat_of.

  Inductive var :=
  | Free of atom (* a variable waiting to be instantiated *)
  | Bound of nat (* a bound variable *)
  .

  Definition get_free_bound (k : nat) (v : var) : option nat :=
    match v with
    | Bound k' => if k' >= k then Some (k' - k) else None
    | _ => None
    end.

  Inductive lc_var : var -> Prop :=
  | lc_free : forall a, lc_var (Free a).
  Hint Constructors lc_var.

  Definition eq_var (a b : var) : bool :=
    match a, b with
    | Free a, Free b => a == b
    | Bound i, Bound j => i == j (* PeanoNat.Nat.eqb i j *)
    | _, _ => false
    end.

  Lemma var_reflect : Equality.axiom eq_var.
  Proof.
    move=>a b.
    by case b ; case a =>//= ; (try by constructor); move=> x y;
        case: eqP; constructor; congruence.
  Qed.

  Definition var_eqMixin := EqMixin var_reflect.
  Canonical var_eqType := EqType _ var_eqMixin.

  Definition open_var A (f : var -> A) (n : nat) (x : A) (y : var) : A :=
    match y with
    | Bound n' => if n == n' then x else f y
    | _ => f y
    end.

  Definition lcb_var v : bool :=
    match v with
    | Free _ => true
    | _ => false
    end.

  Lemma getfree_lc v : get_free_bound 0 v == None -> lc_var v.
  Proof. by case v. Qed.

  Lemma lc_getfree v : lc_var v -> get_free_bound 0 v == None.
  Proof. by case. Qed.

  Lemma lc_varP v : reflect (lc_var v) (lcb_var v).
  Proof. case:v=>/= x; do ! constructor; move=>F; case Eq: _ / F =>//. Qed.

End AtomScope.
