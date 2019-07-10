From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import FinMap.finmap.
Require Import FinMap.ordtype.

Require Import SendRec.Atom.

(* A module to have different types of atoms taking advantage of
   module generativity *)

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
    | Bound i, Bound j => i == j
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
    | Bound i, Bound j => i == j
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
