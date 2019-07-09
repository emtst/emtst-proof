(* The Send Receive System (REVISED). *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import FinMap.ordtype.

Require Import SendRec.AtomScopes.

Inductive sort : Set :=
  | boole : sort (* boolean expression *)
  | end_points : tp -> tp -> sort

with tp : Set :=
  | input : sort -> tp -> tp
  | output : sort -> tp -> tp
  | ch_input : tp -> tp -> tp
  | ch_output : tp -> tp -> tp
  | offer_branch : tp -> tp -> tp
  | take_branch : tp -> tp -> tp
  | ended : tp
  (* | bot : tp *) (* no longer needed *)
.

Scheme tp_sort := Induction for tp Sort Prop
  with sort_tp := Induction for sort Sort Prop. (* Minimality *)
Combined Scheme tp_sort_mutind from tp_sort, sort_tp.

Fixpoint dual (T : tp) : tp :=
  match T with
  | input s T => output s (dual T)
  | output s T => input s (dual T)
  | ch_input T T' => ch_output T (dual T')
  | ch_output T T' => ch_input T (dual T')
  | offer_branch T T' => take_branch (dual T) (dual T')
  | take_branch T T' => offer_branch (dual T) (dual T')
  | ended => ended
  end
.

Fixpoint eq_tp (T T': tp) : bool :=
  match T, T' with
  | input s T, input s' T' => eq_sort s s' && eq_tp T T'
  | output s T, output s' T' => eq_sort s s' && eq_tp T T'
  | ch_input T1 T2, ch_input T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | ch_output T1 T2, ch_output T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'

  | offer_branch T1 T2, offer_branch T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | take_branch T1 T2, take_branch T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | ended, ended => true
  | _, _ => false
  end
with eq_sort (s s' : sort) : bool :=
  match s, s' with
  | boole, boole => true
  | end_points T1 T2, end_points T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | _, _ => false
  end.

Lemma eq_imp_eq : (forall x y, eq_tp x y -> x = y) /\ forall s s', eq_sort s s' -> s = s'.
Proof.
  apply tp_sort_mutind ; intros; try destruct y  ; try destruct s'; try easy ;
  inversion H1 ; apply Bool.andb_true_iff in H3 ; destruct H3 ;
  try(move:H3 ; move/H0=>H3 ; move:H2 ; move/H=>H4 ; by rewrite H3 H4).
Qed. (* more ssreflect can make this better *)

Lemma eq_tp_refl x : eq_tp x x.
Proof.
  by elim x using tp_sort with (P:=fun x=>eq_tp x x) (P0:= fun s=>eq_sort s s)=>//;
     move=>s H t H0; simpl; rewrite H H0.
Qed.

Lemma eq_sort_refl s : eq_sort s s.
Proof.
  by elim s using sort_tp with (P:=fun x=> eq_tp x x)=>//;
     move=>x H t H0; simpl; rewrite H H0.
Qed.

Lemma eq_tpP : Equality.axiom eq_tp.
Proof.
  move=>x y.
  apply: (iffP idP)=>[|<-].
  apply eq_imp_eq.
  apply eq_tp_refl.
Qed.

Lemma eq_sortP : Equality.axiom eq_sort.
Proof.
  move=>x y.
  apply: (iffP idP)=>[|<-].
  apply eq_imp_eq.
  apply eq_sort_refl.
Qed.

Canonical tp_eqMixin := EqMixin eq_tpP.
Canonical tp_eqType := Eval hnf in EqType tp tp_eqMixin.

Canonical sort_eqMixin := EqMixin eq_sortP.
Canonical sort_eqType := Eval hnf in EqType sort sort_eqMixin.

(* CoInductive just because we don't need an induction principle *)
CoInductive polarity := Pos | Neg.

Definition eq_polarity (p p' : polarity) : bool :=
  match p, p' with
  | Pos, Pos
  | Neg, Neg => true
  | _, _ => false
  end.

Lemma polarity_reflect : Equality.axiom eq_polarity.
Proof.
    by do !case ; constructor.
Qed.

Definition polarity_eqMixin := EqMixin polarity_reflect.
Canonical polarity_eqType := EqType _ polarity_eqMixin.

(* polarities have a simple order (e.g. + < -) *)

Definition ltn_pol (p p' : polarity) : bool :=
  match p, p' with
  | Pos, Neg => true
  | _, _ => false
  end.

Lemma ltn_pol_irreflexive : irreflexive ltn_pol. (* x : ltn_pol x x = false. *)
Proof.
    by case.
Qed.

Lemma ltn_pol_transitive : transitive ltn_pol.
Proof.
  by do !case.
Qed.

Lemma ltn_pol_total (a b : polarity) : [|| ltn_pol a b, a == b | ltn_pol b a].
Proof.
  move: a b.
  case ; case => //.
Qed.

Definition polarity_ordMixin : Ordered.mixin_of polarity_eqType :=
  OrdMixin
    ltn_pol_irreflexive
    ltn_pol_transitive
    ltn_pol_total.
Canonical Structure polarity_ordType := OrdType _ polarity_ordMixin.

Definition dual_pol' (p p' : polarity) := p != p.
Definition dual_pol p := if p is Pos then Neg else Pos.

(******************************************************************************)
(**  NAMESPACES  **************************************************************)
(******************************************************************************)

Module EV := AtomScope Atom.Atom. (* Module of the atoms for expressions *)
Canonical EV_atom_eqType := EqType EV.atom EV.atom_eqMixin.
Canonical EV_atom_ordType := OrdType EV.atom EV.atom_ordMixin.
Coercion EV.Free : EV.atom >-> EV.var.
Coercion EV.Bound : nat >-> EV.var.
Canonical EV_var_eqType := EqType _ EV.var_eqMixin.

Module SC := AtomScope Atom.Atom. (* Module of the atoms for names *)
Canonical SC_atom_eqType := EqType SC.atom SC.atom_eqMixin.
Canonical SC_atom_ordType := OrdType SC.atom SC.atom_ordMixin.
Coercion SC.Free : SC.atom >-> SC.var.
Coercion SC.Bound : nat >-> SC.var.
Canonical SC_var_eqType := EqType _ SC.var_eqMixin.

Module LC := AtomScope Atom.Atom. (* Module of the atoms for channels *)
Canonical LC_atom_eqType := EqType LC.atom LC.atom_eqMixin.
Canonical LC_atom_ordType := OrdType LC.atom LC.atom_ordMixin.
Coercion  LC.Free : LC.atom >-> LC.var.
Coercion  LC.Bound : nat >-> LC.var.
Canonical LC_var_eqType := EqType _ LC.var_eqMixin.

Module CN := AtomScope Atom.Atom. (* Module of the atoms for channel name *)
Canonical CN_atom_eqType := EqType CN.atom CN.atom_eqMixin.
Canonical CN_atom_ordType := OrdType CN.atom CN.atom_ordMixin.
Coercion CN.Free : CN.atom >-> CN.var.
Coercion CN.Bound : nat >-> CN.var.
Canonical CN_var_eqType := EqType _ CN.var_eqMixin.

Notation evar := (EV.var).
Notation scvar := (SC.var).
Notation lcvar := (LC.var).
Notation cnvar := (CN.var).

(******************************************************************************)
(**  CHANNELS    **************************************************************)
(******************************************************************************)

Inductive channel :=
| Ch of (cnvar * polarity) %type (* a channel with polarity *)
| Var of lcvar.

(* these definitions explore the dual of locally closed, ie: free bound vars *)
Definition fbound_chan_c (n : nat) (c : channel) : option nat :=
  match c with
  | Var v => LC.get_free_bound n v
  | _ => None
  end.

Definition fbound_chan_k (n : nat) (c : channel) : option nat :=
  match c with
  | Ch (k, _) => CN.get_free_bound n k
  | _ => None
  end.

Definition eq_channel (a b : channel) : bool :=
  match a, b with
  | Ch (v1, p1), Ch (v2, p2) => (v1 == v2) && (p1 == p2)
  | Var v1     , Var v2      => v1 == v2
  | _          , _           => false
  end.

Lemma channel_reflect : Equality.axiom eq_channel.
Proof.
  move=> a b.
  case b ; case a =>//= ; (try by constructor); move=> x y.
  by case x=>va pa; case y=>vb pb; case CN.var_reflect; case polarity_reflect;
           move=>H; constructor; congruence.
  by case: x => [v p]; by constructor; congruence.
  by case LC.var_reflect; constructor; congruence.
Qed.

Definition channel_eqMixin := EqMixin channel_reflect.
Canonical channel_eqType := EqType _ channel_eqMixin.
Coercion Var : lcvar >-> channel.

(* Build a channel with a name and a polarity*)
Definition ch (en : CN.atom * polarity) : channel :=
  let: (k, pol) := en in Ch (CN.Free k, pol).

Notation "X ^+" := (X, Pos) (at level 70).
Notation "X ^-" := (X, Neg) (at level 70).

Definition dual_ch (k k' : channel) :=
  match k, k' with
  | Ch (a, p), Ch (b, p') => if a == b then dual_pol p == p' else false
  | _ , _ => false
  end.

Inductive exp : Set :=
  | tt
  | ff
  | V of evar
.

Definition eq_exp (e1 e2 : exp) : bool :=
  match e1, e2 with
  | tt, tt => true
  | ff, ff => true
  | V v1, V v2 => v1 == v2
  | _, _ => false
  end.

Definition fbound_exp n (e : exp) : seq nat :=
  match e with
  | V v => seq_of_opt (EV.get_free_bound n v)
  | _ => [::]
  end.

Lemma exp_reflect : Equality.axiom eq_exp.
Proof.
  move=> a b; case: a; case: b => /= //; try (by constructor); move => v1 v2.
  case EV.var_reflect=> H; constructor; congruence.
Qed.

Definition exp_eqMixin := EqMixin exp_reflect.
Canonical exp_eqType := EqType _ exp_eqMixin.

Coercion V : evar >-> exp.

(* CoInductive just because we don't need an induction principle *)
CoInductive label := left | right.

Definition eq_label (l1 l2 : label) : bool :=
  match l1, l2 with
  | left, left => true
  | right, right => true
  | _, _ => false
  end.

Lemma label_reflect : Equality.axiom eq_label.
Proof. case; case; constructor; congruence. Qed.

Definition label_eqMixin := EqMixin label_reflect.
Canonical label_eqType := EqType _ label_eqMixin.

Inductive proc : Set :=
(* request name over a bound channel with polarity and behave like proc *)
| request : scvar -> proc -> proc
| accept : scvar -> proc -> proc

| send : channel -> exp -> proc -> proc
| receive : channel -> proc -> proc

| select : channel -> label -> proc -> proc
| branch : channel -> proc -> proc -> proc

| throw : channel -> channel -> proc -> proc
| catch : channel -> proc -> proc

| ife : exp -> proc -> proc -> proc
| par : proc -> proc -> proc
| inact : proc

| nu_nm : proc -> proc (* hides a name *)
| nu_ch : proc -> proc (* hides a channel name *)

| bang : proc -> proc (* process replication *)
.
Hint Constructors proc.

Fixpoint eq_proc (p1 p2 : proc) : bool :=
  match p1, p2 with
  | request v1 p1, request v2 p2 => (v1 == v2) && eq_proc p1 p2
  | accept  v1 p1, accept  v2 p2 => (v1 == v2) && eq_proc p1 p2
  | send c1 e1 p1, send c2 e2 p2 => (c1 == c2) && (e1 == e2) && eq_proc p1 p2
  | receive c1 p1, receive c2 p2 => (c1 == c2) && eq_proc p1 p2
  | select c1 l1 p1, select c2 l2 p2 => (c1 == c2) && (l1 == l2) && eq_proc p1 p2
  | branch c1 p1 p2, branch c2 p3 p4 => (c1 == c2) && eq_proc p1 p3 && eq_proc p2 p4
  | throw c1 c2 p1, throw c3 c4 p2 => (c1 == c3) && (c2 == c4) && eq_proc p1 p2
  | catch c1 p1, catch c2 p2 => (c1 == c2) && eq_proc p1 p2
  | ife e1 p1 p2, ife e2 p3 p4 => (e1 == e2) && eq_proc p1 p3 && eq_proc p2 p4
  | par p1 p2, par p3 p4 => eq_proc p1 p3 && eq_proc p2 p4
  | inact, inact => true
  | nu_nm p1, nu_nm p2 => eq_proc p1 p2
  | nu_ch p1, nu_ch p2 => eq_proc p1 p2
  | bang p1, bang p2 => eq_proc p1 p2
  | _, _ => false
  end.

Lemma proc_reflect : Equality.axiom eq_proc.
Proof with (try constructor; try congruence).
  elim.
  + move=> v p IH; case=>/=...
    move=> v' p'; case SC.var_reflect; case IH...
  + move=> v p IH; case=>/=...
    move=> v' p'; case SC.var_reflect; case IH...
  + move=> c e p IH; case=>/=...
    move=> c' e' p'; case channel_reflect; case exp_reflect; case IH...
  + move=> c p IH; case=>/=...
    move=> c' p'; case channel_reflect; case IH...
  + move=> c e p IH; case=>/=...
    move=> c' e' p'; case channel_reflect; case label_reflect; case IH...
  + move=> c p1 IH1 p2 IH2; case=>/=...
    move=> c' p1' p2'; case channel_reflect; case IH1; case IH2...
  + move=> c1 c2 p1 IH1; case=>/=...
    move=> c1' c2'  p1'; do ! case channel_reflect; case IH1...
  + move=> c1 p1 IH1; case=>/=...
    move=> c1' p1'; do ! case channel_reflect; case IH1...
  + move=> e p1 IH1 p2 IH2; case=>/=...
    move=> e' p1' p2'; case exp_reflect; case IH1; case IH2...
  + move=> p1 IH1 p2 IH2; case=>/=...
    move=> p1' p2'; case IH1; case IH2...
  + case...
  + move=> p IH; case...
    move=> p'/=; case IH...
  + move=> p IH; case...
    move=> p'/=; case IH...
  + move=> p IH ; case ...
    move=> p'/= ; case IH...
Qed.

Definition proc_eqMixin := EqMixin proc_reflect.
Canonical proc_eqType := EqType _ proc_eqMixin.

Fixpoint depth (P : proc) :=
  match P with
  | request a P => S (depth P)
  | accept a P => S (depth P)
  | send c e P => S (depth P)
  | receive c P => S (depth P)
  | select c l P => S (depth P)
  | throw c c' P => S (depth P)
  | catch c P => S (depth P)
  | branch c P Q => S (maxn (depth P) (depth Q))
  | ife e P Q => S (maxn (depth P) (depth Q))
  | par P Q => S (maxn (depth P) (depth Q))
  | inact => O
  | nu_nm P => S (depth P)
  | nu_ch P => S (depth P)
  | bang P => S (depth P)
  end.
(* Note: Since we don't need to substitute for them in channel hiding
         we just use just nominals for them *)

(* open a bound variable with a channel *)
Definition opc (n : nat) (u : channel) (ch : channel) : channel :=
  match ch with
  | Var v => LC.open_var Var n u v
  | _ => ch
  end.

(* Open a bound variable in an expression *)
Definition ope (n : nat) (e' : exp) (e : exp) : exp :=
  match e with
  | V v => EV.open_var V n e' v
  | _ => e
  end.

(* open a bound variable with a channel *)
Definition opk (n : nat) (u : CN.var) (ch : channel) : channel :=
  match ch with
  | Ch (k, p) => Ch (CN.open_var id n u k, p)
  | _ => ch
  end.

(* open a bound named variable with channel name (SC.atom) *)
Definition opn n k a := SC.open_var id n k a.

Definition shift_ch c :=
  match c with
  | Ch (CN.Bound i, p) => Ch (CN.Bound (i.+1), p)
  | _ => c
  end.


(* Open a bound variable in a process with a channel *)
Fixpoint open_c (n : nat) (u : channel) (P : proc) : proc :=
  match P with
  | request a P => request a (open_c (S n) u P)
  | accept a P => accept a (open_c (S n) u P)
  | catch k P => catch (opc n u k) (open_c (S n) u P)
  | send k e P => send (opc n u k) e (open_c n u P)
  | receive k P => receive (opc n u k) (open_c n u P)
  | select k l P => select (opc n u k) l (open_c n u P)
  | throw k k' P => throw (opc n u k) (opc n u k') (open_c n u P)
  | branch k P Q => branch (opc n u k) (open_c n u P) (open_c n u Q)
  | ife e P Q => ife e (open_c n u P) (open_c n u Q)
  | par P Q => par (open_c n u P) (open_c n u Q)
  | nu_nm P => nu_nm (open_c n u P)
  | nu_ch P => nu_ch (open_c n (shift_ch u) P)
  | inact => inact
  | bang P => bang (open_c n u P)
  end.
Notation "{op k ~> u } t" := (open_c k u t) (at level 67) : sr_scope.

Fixpoint open_n (n : nat) (u : SC.var) (P : proc) : proc :=
  match P with
  | nu_nm P => nu_nm (open_n (S n) u P)
  | request a P => request (opn n u a) (open_n n u P)
  | accept a P => accept (opn n u a) (open_n n u P)
  | catch k P => catch k (open_n n u P)
  | send k e P => send k e (open_n n u P)
  | receive k P => receive k (open_n n u P)
  | select k l P => select k l (open_n n u P)
  | throw k k' P => throw k k' (open_n n u P)
  | branch k P Q => branch k (open_n n u P) (open_n n u Q)
  | ife e P Q => ife e (open_n n u P) (open_n n u Q)
  | par P Q => par (open_n n u P) (open_n n u Q)
  | nu_ch P => nu_ch (open_n n u P)
  | inact => inact
  | bang P => bang (open_n n u P)
  end.
Notation "{opn k ~> u } t" := (open_n k u t) (at level 67) : sr_scope.

(* Open a bound variable in a process with an expression *)
Fixpoint open_e (n : nat) (u : exp) (P : proc) : proc :=
  match P with
  | request a P => request a (open_e n u P)
  | accept a P => accept a (open_e n u P)
  | send k e P => send k (ope n u e) (open_e n u P)
  | receive k P => receive k (open_e (S n) u P)
  | select k l P => select k l (open_e n u P)
  | throw k k' P => throw k k' (open_e n u P)
  | catch k P => catch k (open_e n u P)
  | branch k P Q => branch k (open_e n u P) (open_e n u Q)
  | ife e P Q => ife (ope n u e) (open_e n u P) (open_e n u Q)
  | par P Q => par (open_e n u P) (open_e n u Q)
  | inact => inact
  | nu_nm P => nu_nm (open_e n u P)
  | nu_ch P => nu_ch (open_e n u P)
  | bang P => bang (open_e n u P)
  end.
Notation "{ope k ~> u } t" := (open_e k u t) (at level 67) : sr_scope.

Fixpoint open_k (n : nat) (ko : CN.var) (P : proc) : proc :=
  match P with
  | request a P => request a (open_k n ko P)
  | accept a P  => accept a (open_k n ko P)
  | send k e P  => send (opk n ko k) e (open_k n ko P)
  | receive k P => receive (opk n ko k) (open_k n ko P)
  | select k l P => select (opk n ko k) l (open_k n ko P)
  | throw k k' P => throw (opk n ko k) (opk n ko k') (open_k n ko P)
  | catch k P => catch (opk n ko k) (open_k n ko P)
  | branch k P Q => branch (opk n ko k) (open_k n ko P) (open_k n ko Q)
  | ife e P Q => ife e (open_k n ko P) (open_k n ko Q)
  | par P Q => par (open_k n ko P) (open_k n ko Q)
  | inact => inact
  | nu_nm P => nu_nm (open_k n ko P)
  | nu_ch P => nu_ch (open_k (S n) ko P)
  | bang P => bang (open_k n ko P)
  end.
Notation "{opk k ~> u } t" := (open_k k u t) (at level 67) : sr_scope.

Open Scope sr_scope.

Definition open_c0 P u :={op 0 ~> u} P.
Definition open_e0 P u :={ope 0~>u} P.
Definition open_n0 P u :={opn 0~>u} P.
Definition open_k0 P u :={opk 0~>u} P.

Inductive lc_ch : channel -> Prop :=
| lc_channel a pol: lc_ch (Ch (CN.Free a, pol))
| lc_free_var a: lc_ch (Var (LC.Free a)).
Hint Constructors lc_ch.

Definition lcb_ch (c : channel) : bool :=
  match c with
  | Ch (CN.Free a, pol) => true
  | Var (LC.Free a) => true
  | _ => false
  end.

Lemma freechan_lc_c c :
  (fbound_chan_c 0 c == None) && (fbound_chan_k 0 c == None) -> lc_ch c.
Proof. by case: c => [[[]]|[]]. Qed.

Lemma lc_c_freechan c :
  lc_ch c -> (fbound_chan_c 0 c == None) && (fbound_chan_k 0 c == None) .
Proof. by case. Qed.

Lemma lcb_chP : forall c, reflect (lc_ch c) (lcb_ch c).
Proof.
  case=>//; case=>//=; first case=>///=.
  by move=>a p; apply: (ReflectT _ (lc_channel a p)).
  by move=>n p; apply: ReflectF => H; case F: _ / H => //.
  by move=>a; apply: (ReflectT _ (lc_free_var a)).
  by move=>n; apply: ReflectF => H; case F: _ / H => //.
Qed.

Lemma lc_ch_ch k : lc_ch(ch k).
Proof. by case: k=> a p; apply/lcb_chP. Qed.

Inductive lc_exp : exp -> Prop :=
  | lc_tt : lc_exp tt
  | lc_ff : lc_exp ff
  | lc_vare a: lc_exp (V(EV.Free a))
.
Hint Constructors lc_exp.

Definition lcb_exp (e : exp) :=
  match e with
  | tt => true
  | ff => true
  | V (EV.Free a) => true
  | _ => false
  end.

Lemma freeexp_lc e : fbound_exp 0 e == [::] -> lc_exp e.
Proof. by case: e =>[||[]]. Qed.

Lemma lc_freeexp e : lc_exp e -> fbound_exp 0 e == [::].
Proof. by case. Qed.

Lemma lcb_expP : forall e, reflect (lc_exp e) (lcb_exp e).
Proof.
  case; [ by apply: ReflectT | by apply: ReflectT |].
  case=>[v|n]/=.
    by apply: ReflectT; apply: lc_vare.
    by apply: ReflectF; case F: _ / => //.
Qed.

(* consider a boolean function instead of this inductive def *)
Inductive lc : proc -> Prop :=
| lc_request : forall (L : seq LC.atom) a P,
    SC.lc_var a ->
    (forall x, x \notin L -> lc (open_c0 P (Var (LC.Free x)))) ->
    lc (request a P)

| lc_accept : forall (L : seq LC.atom) a P,
    SC.lc_var a ->
    (forall x, x \notin L -> lc (open_c0 P (Var (LC.Free x)))) ->
    lc (accept a P)

| lc_send : forall k e P,
    lc_ch k ->
    lc_exp e ->
    lc P ->
    lc (send k e P)

| lc_receive : forall (L : seq EV.atom) k P,
    lc_ch k ->
    (forall x, x \notin L -> lc (open_e0 P (V (EV.Free x)))) ->
    lc (receive k P)

| lc_select : forall k l P,
    lc_ch k ->
    lc P ->
    lc (select k l P)

| lc_branch : forall k P Q,
    lc_ch k ->
    lc P -> lc Q ->
    lc (branch k P Q)

| lc_throw : forall k k' P,
    lc_ch k -> lc_ch k' ->
    lc P ->
    lc (throw k k' P)

| lc_catch : forall (L : seq LC.atom) k P,
    lc_ch k ->
    (forall x, x \notin L -> lc (open_c0 P (LC.Free x))) ->
    lc (catch k P)

| lc_ife : forall e P Q,
    lc_exp e -> lc P -> lc Q ->
    lc (ife e P Q)

| lc_par : forall P Q,
    lc P -> lc Q ->
    lc (par P Q)

| lc_inact : lc inact

| lc_nu_nm : forall (L : seq SC.atom) P,
    (forall x, x \notin L -> lc (open_n0 P (SC.Free x))) ->
    lc (nu_nm P)

| lc_nu_ch : forall (L : seq CN.atom) P,
    (forall k, k \notin L -> lc (open_k0 P (CN.Free k))) ->
    lc (nu_ch P)

| lc_bang P: lc P -> lc (bang P)
.
Hint Constructors lc.

Definition body P := forall (L : seq LC.atom) x, x \notin L -> lc (open_c0 P (LC.Free x)).

(* Some properties of these definitions  *)

Lemma op_lc_core_exp e j a i u :
    i <> j ->
    ope j a e = ope i u (ope j a e) ->
    e = ope i u e.
Proof. by case: e =>//; case=>/= // n /eqP/negPf; case: ifP => // /eqP<-->. Qed.

Fixpoint get_fbound_c (n : nat) (P : proc) : seq nat :=
  match P with
  | request _ P
  | accept  _ P => get_fbound_c (S n) P
  | catch k P => seq_of_opt (fbound_chan_c n k) ++ get_fbound_c (S n) P
  | send k _ P
  | receive k P
  | select k _ P => seq_of_opt (fbound_chan_c n k) ++ get_fbound_c n P
  | throw k k' P => seq_of_opt (fbound_chan_c n k) ++
                    seq_of_opt (fbound_chan_c n k') ++ get_fbound_c n P
  | branch k P Q => seq_of_opt (fbound_chan_c n k) ++
                    get_fbound_c n P ++ get_fbound_c n Q
  | ife _ P Q
  | par P Q => get_fbound_c n P ++ get_fbound_c n Q
  | nu_nm P
  | nu_ch P => get_fbound_c n P
  | inact => [::]
  | bang P => get_fbound_c n P
  end.
Definition fbound_c := get_fbound_c 0.

Fixpoint get_fbound_n (n : nat) (P : proc) : seq nat :=
  match P with
  | nu_nm P => get_fbound_n (S n) P
  | request a P
  | accept a P => seq_of_opt (SC.get_free_bound n a)  ++ get_fbound_n n P
  | nu_ch P
  | catch _ P
  | send _ _ P
  | receive _ P
  | select _ _ P
  | throw _ _ P => get_fbound_n n P
  | branch _ P Q
  | ife _ P Q
  | par P Q => get_fbound_n n P ++ get_fbound_n n Q
  | inact => [::]
  | bang P => get_fbound_n n P
  end.
Definition fbound_n := get_fbound_n 0.

Fixpoint get_fbound_e (n : nat) (P : proc) : seq nat :=
  match P with
  | receive _ P => get_fbound_e (S n) P
  | request _ P
  | accept _ P
  | catch _ P
  | throw _ _ P
  | select _ _ P
  | nu_nm P
  | nu_ch P => get_fbound_e n P
  | par P Q
  | branch _ P Q => get_fbound_e n P ++ get_fbound_e n Q
  | send _ e P => fbound_exp n e ++ get_fbound_e n P
  | ife e P Q => fbound_exp n e ++ get_fbound_e n P ++ get_fbound_e n Q
  | inact => [::]
  | bang P => get_fbound_e n P
  end.
Definition free_e := get_fbound_e 0.

Fixpoint get_fbound_k (n : nat) (P : proc) : seq nat :=
  match P with
  | nu_ch P => get_fbound_k (S n) P
  | request _ P
  | accept  _ P => get_fbound_k n P
  | catch k P => seq_of_opt (fbound_chan_k n k) ++ get_fbound_k n P
  | send k _ P
  | receive k P
  | select k _ P => seq_of_opt (fbound_chan_k n k) ++ get_fbound_k n P
  | throw k k' P => seq_of_opt (fbound_chan_k n k) ++
                    seq_of_opt (fbound_chan_k n k') ++ get_fbound_k n P
  | branch k P Q => seq_of_opt (fbound_chan_k n k) ++
                    get_fbound_k n P ++ get_fbound_k n Q
  | ife _ P Q
  | par P Q => get_fbound_k n P ++ get_fbound_k n Q
  | nu_nm P => get_fbound_k n P
  | inact => [::]
  | bang P => get_fbound_k n P
  end.
Definition free_k := get_fbound_k 0.


Definition lcb P :=
  (fbound_c P == [::]) &&
  (free_e P == [::]) &&
  (free_k P == [::]) &&
  (fbound_n P == [::]).

Definition is_fbound_c (k : nat) (P : proc) := k \in fbound_c P.
Definition is_fbound_n (k : nat) (P : proc) := k \in fbound_n P.
Definition is_fbound_e (k : nat) (P : proc) := k \in free_e P.
Definition is_fbound_k (k : nat) (P : proc) := k \in free_k P.

Lemma fbound_c_open n (x : LC.atom) c :
  seq_of_opt (fbound_chan_c n.+1 c) = [seq k.-1 | k <- seq_of_opt (fbound_chan_c n (opc n x c))].
Proof.
  case: c => //; case=>// m /=; case: ifP; rewrite ltn_neqAle ?(rwP negPf).
  by move=>/andP-[/negPf->/=->]/=; rewrite subnS.
  rewrite negb_and=>/orP-[/negPn->//|].
  rewrite -ltnNge ltn_neqAle eq_sym =>/andP-[/negPf-Hneq].
  rewrite Hneq leqNgt /=.
  by rewrite [in if _ then _ else _]leq_eqVlt Hneq =>/negPf->.
Qed.

Lemma free_k_open n (x : CN.atom) c :
  seq_of_opt (fbound_chan_k n.+1 c) = [seq k.-1 | k <- seq_of_opt (fbound_chan_k n (opk n x c))].
Proof.
  case: c => //; case=>//; case=>// m _ /=; case: ifP; rewrite ltn_neqAle ?(rwP negPf).
  by move=>/andP-[/negPf->/=->]/=; rewrite subnS.
  rewrite negb_and=>/orP-[/negPn->//|].
  rewrite -ltnNge ltn_neqAle eq_sym =>/andP-[/negPf-Hneq].
  rewrite Hneq leqNgt /=.
  by rewrite [in if _ then _ else _]leq_eqVlt Hneq =>/negPf->.
Qed.

Lemma free_e_open n (x : EV.atom) c :
  fbound_exp n.+1 c = [seq k.-1 | k <- fbound_exp n (ope n x c)].
Proof.
  case: c => //; case=>// m /=; case: ifP; rewrite ltn_neqAle ?(rwP negPf).
  by move=>/andP-[/negPf->/=->]/=; rewrite subnS.
  rewrite negb_and=>/orP-[/negPn->//|].
  rewrite -ltnNge ltn_neqAle eq_sym =>/andP-[/negPf-Hneq].
  rewrite Hneq leqNgt /=.
  by rewrite [in if _ then _ else _]leq_eqVlt Hneq =>/negPf->.
Qed.

Lemma fbound_n_open n (x : SC.atom) c :
  seq_of_opt (SC.get_free_bound n.+1 c) =
  [seq k.-1 | k <- seq_of_opt (SC.get_free_bound n (opn n x c))].
Proof.
  case: c => // m /=; case: ifP; rewrite ltn_neqAle ?(rwP negPf).
  by move=>/andP-[/negPf->/=->]/=; rewrite subnS.
  rewrite negb_and=>/orP-[/negPn->//|].
  rewrite -ltnNge ltn_neqAle eq_sym =>/andP-[/negPf-Hneq].
  rewrite Hneq leqNgt /=.
  by rewrite [in if _ then _ else _]leq_eqVlt Hneq =>/negPf->.
Qed.

Ltac fo_by_ind P n x :=
  let IH := fresh in let IH1 := fresh in let IH2 := fresh in
  let v := fresh in let p := fresh in let e := fresh in let c := fresh in
  let c1 := fresh in let c2 := fresh in let p1 := fresh in let p2 := fresh in
  elim: P n => [ v p IH n
               | v p IH n
               | c e p IH n
               | c p IH n
               | c l p IH n
               | c p1 IH1 p2 IH2 n
               | c1 c2 p IH n
               | c p IH n
               | e p1 IH1 p2 IH2 n
               | p1 IH1 p2 IH2 n
               | n
               | p IH n
               | p IH n
               | p IH n] /= //;
    try (rewrite IH) => //;
    try (rewrite IH1) => //;
    try (rewrite IH2) => //;
    try (rewrite !map_cat) => //.

Lemma free_open_c  n p (x : LC.atom) :
  get_fbound_c n.+1 p = [seq k.-1 | k <- get_fbound_c n ({op n ~> x} p)].
Proof. fo_by_ind p n x; by rewrite !(fbound_c_open n x). Qed.

Lemma free_open_e  n p (x : EV.atom) :
  get_fbound_e n.+1 p = [seq k.-1 | k <- get_fbound_e n ({ope n ~> x} p)].
Proof. fo_by_ind p n x; by rewrite !(free_e_open n x). Qed.

Lemma free_open_n  n p (x : SC.atom) :
  get_fbound_n n.+1 p = [seq k.-1 | k <- get_fbound_n n ({opn n ~> x} p)].
Proof. fo_by_ind p n x; by rewrite !(fbound_n_open n x). Qed.

Lemma free_open_k  n p (x : CN.atom) :
  get_fbound_k n.+1 p = [seq k.-1 | k <- get_fbound_k n ({opk n ~> x} p)].
Proof.
Proof. fo_by_ind p n x; by rewrite !(free_k_open n x). Qed.

Lemma map_nil (A B : eqType) (f : A -> B) l : (map f l == [::]) = (l == [::]).
Proof. by case: l. Qed.

Ltac by_proc_induction0 P :=
  let IH := fresh in let IH1 := fresh in let IH2 := fresh in
  let v := fresh in let p := fresh in let e := fresh in let c := fresh in
  let c1 := fresh in let c2 := fresh in let p1 := fresh in let p2 := fresh in
  let n := fresh in
  elim: P => [ v p IH
             | v p IH
             | c e p IH
             | c p IH
             | c l p IH
             | c p1 IH1 p2 IH2
             | c1 c2 p IH
             | c p IH
             | e p1 IH1 p2 IH2
             | p1 IH1 p2 IH2
             |
             | p IH
             | p IH
             | p IH] // /=;
  try (rewrite IH => //);
  try (rewrite IH1 => //);
  try (rewrite IH2 => //).

Ltac by_proc_induction P k :=
  let IH := fresh in let IH1 := fresh in let IH2 := fresh in
  let v := fresh in let p := fresh in let e := fresh in let c := fresh in
  let c1 := fresh in let c2 := fresh in let p1 := fresh in let p2 := fresh in
  let n := fresh in
  elim: P k => [ v p IH n
               | v p IH n
               | c e p IH n
               | c p IH n
               | c l p IH n
               | c p1 IH1 p2 IH2 n
               | c1 c2 p IH n
               | c p IH n
               | e p1 IH1 p2 IH2 n
               | p1 IH1 p2 IH2 n
               | n
               | p IH n
               | p IH n
               | p IH n] /=;
  try (apply/eqP; rewrite eqSS; apply/eqP); try (rewrite -IH => //);
  try (rewrite -IH1 => //); try (rewrite -IH2 => //).

Ltac by_proc_induction2 P n m :=
  let IH := fresh in let IH1 := fresh in let IH2 := fresh in
  let v := fresh in let p := fresh in let e := fresh in let c := fresh in
  let c1 := fresh in let c2 := fresh in let p1 := fresh in let p2 := fresh in
  elim: P n m => [ v p IH
               | v p IH
               | c e p IH
               | c p IH
               | c l p IH
               | c p1 IH1 p2 IH2
               | c1 c2 p IH
               | c p IH
               | e p1 IH1 p2 IH2
               | p1 IH1 p2 IH2
               |
               | p IH
               | p IH
               | p IH] n m /=;
  try (rewrite -IH => //); try (rewrite -IH1 => //); try (rewrite -IH2 => //).

Lemma depth_op_ch k x P : depth P = depth ({op k ~> x} P).
Proof. by_proc_induction2 P k x; easy. Qed.
Lemma depth_opn_ch k x P : depth P = depth ({opn k ~> x} P).
Proof. by_proc_induction P k; easy. Qed.
Lemma depth_ope_ch k x P : depth P = depth ({ope k ~> x} P).
Proof. by_proc_induction P k; easy. Qed.
Lemma depth_opk_ch k x P : depth P = depth ({opk k ~> x} P).
Proof. by_proc_induction P k; easy. Qed.

Lemma cat_nil (A : eqType) (s1 s2 : seq A) :
  (s1 ++ s2 == [::]) = (s1 == [::]) && (s2 == [::]).
Proof. by case: s1. Qed.

Lemma seqofopt_nil (A : eqType) (s1 : option A) :
  (seq_of_opt s1 == [::]) = (s1 == None).
Proof. by case: s1. Qed.

(* False! Unless x not free_k *)
Lemma freechan_k_open_c i n c (x : LC.atom) :
  fbound_chan_k i c = fbound_chan_k i (opc n x c).
Proof. by case: c=>//; case=>///=m;case: ifP. Qed.

Lemma freechan_c_open_k i n c (x : CN.atom) :
  fbound_chan_c i c = fbound_chan_c i (opk n x c).
Proof. by case: c=>//; case=>///=m;case: ifP. Qed.


Lemma getfree_e_open_c x n i p : get_fbound_e i p = get_fbound_e i ({op n ~> LC.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfree_k_open_c x n i p : get_fbound_k i p = get_fbound_k i ({op n ~> LC.Free x} p).
Proof. by_proc_induction2 p n i; rewrite -?freechan_k_open_c =>//. Qed.
Lemma getfbound_n_open_c x n i p : get_fbound_n i p = get_fbound_n i ({op n ~> LC.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfbound_c_open_e x n i p : get_fbound_c i p = get_fbound_c i ({ope n ~> EV.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfree_k_open_e x n i p : get_fbound_k i p = get_fbound_k i ({ope n ~> EV.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfbound_n_open_e x n i p : get_fbound_n i p = get_fbound_n i ({ope n ~> EV.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfbound_c_open_n x n i p : get_fbound_c i p = get_fbound_c i ({opn n ~> SC.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfree_k_open_n x n i p : get_fbound_k i p = get_fbound_k i ({opn n ~> SC.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfree_e_open_n x n i p : get_fbound_e i p = get_fbound_e i ({opn n ~> SC.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfbound_c_open_k x n i p : get_fbound_c i p = get_fbound_c i ({opk n ~> CN.Free x} p).
Proof. by_proc_induction2 p n i; rewrite -?freechan_c_open_k =>//. Qed.
Lemma getfbound_n_open_k x n i p : get_fbound_n i p = get_fbound_n i ({opk n ~> CN.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.
Lemma getfree_e_open_k x n i p : get_fbound_e i p = get_fbound_e i ({opk n ~> CN.Free x} p).
Proof. by_proc_induction2 p n i; easy. Qed.

Lemma opk_opc i j n (k : CN.atom) c p :
  i \notin seq_of_opt (fbound_chan_k n c) ->
  opk (i+n) k (opc j (Ch (CN.Bound (i+n), p)) c) = opc j (ch (k, p)) c.
Proof.
  case: c =>/=// =>[[[|n0 b]]|[|n0 _]] /=//.
  + case: ifP => /= n_n0.
    - rewrite in_cons negb_or => /andP-[/negPf].
      by rewrite -(eqn_add2r n) subnK // =>->.
    - move =>_; suff: (i + n == n0) = false by move=>->.
      apply/(rwP negPf); move: n_n0 => /(rwP negPf).
      apply contra => /eqP<-; rewrite addnC.
      elim: n => [| n IH] =>//.
  + by case: ifP =>///= _; rewrite eq_refl.
Qed.

Lemma op_k_c i j (k : CN.atom) p P :
  ~~ is_fbound_k i P ->
  {opk i ~> k} ({op j ~> Ch (CN.Bound i, p)} P )= {op j ~> ch (k, p)} P.
Proof.
  rewrite /is_fbound_k/free_k.
  have: i = 0 + i by [].
  move: 0 {2 3}i => n i'; move: i' n i j.
  elim: P => [ v P IH
           | v P IH
           | c e P IH
           | c P IH
           | c l P IH
           | c P1 IH1 P2 IH2
           | c1 c2 P IH
           | c P IH
           | e P1 IH1 P2 IH2
           | P1 IH1 P2 IH2
           |
           | P IH
           | P IH
           | P IH ]  /= // i' n i j eq;
  try (rewrite !mem_cat !negb_or);
  try (move=> /andP-[nfree1 /andP-[nfree2 nfree3]]);
  try (move=> /andP-[nfree1 nfree2]);
  try (move=> nfree1);
  try (rewrite (IH i' n i) => //);
  try (rewrite (IH i' n.+1) => //);
  try (rewrite (IH1 i' n i)=> //);
  try (rewrite (IH2 i' n i)=> //);
  try (rewrite eq => //);
  try (rewrite addSn => //);
  try (rewrite addnC !opk_opc => //).
Qed.

Lemma shift_ch_lc k : lc_ch k -> shift_ch k = k.
Proof. by move/lcb_chP; case: k=>//[][[]a b]. Qed.

Lemma lcch_shift_ch x : lc_ch x -> lc_ch (shift_ch x).
Proof.
  by move=>LC; rewrite shift_ch_lc=>//=. Qed.

Lemma opk_opcC i k j c cn :
  lc_ch cn -> opk i k (opc j cn c) = opc j cn (opk i k c).
Proof. by case: c=>[[a pa]| [n|n]]/=//; case=>[a p|m]; case: ifP. Qed.

Lemma open_kcC i j k cn P :
  lc_ch cn ->
  {opk i ~> k} ({op j ~> cn} P) = {op j ~> cn} ({opk i ~> k} P).
Proof.
  elim: P i j k cn => [ v P IH
           | v P IH
           | c e P IH
           | c P IH
           | c l P IH
           | c P1 IH1 P2 IH2
           | c1 c2 P IH
           | c P IH
           | e P1 IH1 P2 IH2
           | P1 IH1 P2 IH2
           |
           | P IH
           | P IH
           | P IH ] /= // i j k cn lc_c;
  try (rewrite IH => //);
  try (rewrite IH1 => //);
  try (rewrite IH2 => //);
  try (rewrite !opk_opcC =>//);
  try (rewrite shift_ch_lc => //).
Qed.

Lemma open_k_c (k : CN.atom) p P :
  ~~ is_fbound_k 0 P ->
  open_k0 (open_c0 P (Ch (CN.Bound 0, p))) k = open_c0 P (Ch (CN.Free k, p)).
Proof. by move=> F; rewrite /open_k0/open_c0 op_k_c. Qed.

Lemma leqSS n m : n.+1 <= m.+1 -> n <= m.
Proof. by []. Qed.

Lemma lcP P : reflect (lc P) (lcb P).
Proof.
  apply: (equivP idP); split.
  (* Case <====== *)
  { have: depth P <= depth P by apply: leqnn.
    move: {2}(depth P) => n; move: n P; elim=>[|n IH] P; first by case: P.
    rewrite /lcb/free_e/fbound_c/free_k/fbound_n.
    case: P => // /= [v|v|c e|c|c l|c p'|c c'|c|e p'|p'|||] p /leqSS-d.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fn; rewrite cat_nil => /andP-[fv fn].
      move: fv; rewrite seqofopt_nil => /SC.getfree_lc-lcvar.
      apply: (lc_request (L:=[::])) =>// x n_in.
      move: fc; rewrite (free_open_c _ _ x) map_nil => fc.
      move: fe; rewrite (getfree_e_open_c x 0) => fe.
      move: fk; rewrite (getfree_k_open_c x 0) => fk.
      move: fn; rewrite (getfbound_n_open_c x 0) => fn.
      apply: IH; first by rewrite -depth_op_ch.
      by rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fn; rewrite cat_nil => /andP-[fv fn].
      move: fv; rewrite seqofopt_nil => /SC.getfree_lc-lcvar.
      apply: (lc_accept (L:=[::])) =>// x n_in.
      move: fc; rewrite (free_open_c _ _ x) map_nil => fc.
      move: fe; rewrite (getfree_e_open_c x 0) => fe.
      move: fk; rewrite (getfree_k_open_c x 0) => fk.
      move: fn; rewrite (getfbound_n_open_c x 0) => fn.
      apply: IH; first by rewrite -depth_op_ch.
      by rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite cat_nil seqofopt_nil => /andP-[fcc fc].
      move: fe; rewrite cat_nil => /andP-[/freeexp_lc-lc_e fe].
      move: fk; rewrite cat_nil seqofopt_nil => /andP-[fck fk].
      have lc_c : lc_ch c by apply: freechan_lc_c; rewrite fcc fck.
      by apply: lc_send => //; apply: IH=>//; rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite cat_nil seqofopt_nil => /andP-[fcc fc].
      move: fk; rewrite cat_nil seqofopt_nil => /andP-[fck fk].
      have lc_c : lc_ch c by apply: freechan_lc_c; rewrite fcc fck.
      apply: (lc_receive (L:=[::])) =>// x n_in.
      move: fe; rewrite (free_open_e _ _ x) map_nil => fe.
      move: fc; rewrite (getfbound_c_open_e x 0) => fc.
      move: fk; rewrite (getfree_k_open_e x 0) => fk.
      move: fn; rewrite (getfbound_n_open_e x 0) => fn.
      apply: IH; first by rewrite -depth_ope_ch.
      by rewrite /lcb fe fc fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite cat_nil seqofopt_nil => /andP-[fcc fc].
      move: fk; rewrite cat_nil seqofopt_nil => /andP-[fck fk].
      have lc_c : lc_ch c by apply: freechan_lc_c; rewrite fcc fck.
      by apply: lc_select=>//; apply: IH =>//; rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite cat_nil seqofopt_nil => /andP-[fcc fc].
      move: fk; rewrite cat_nil seqofopt_nil => /andP-[fck fk].
      have lc_c : lc_ch c by apply: freechan_lc_c; rewrite fcc fck.
      move: fc; rewrite cat_nil => /andP-[fc1 fc2].
      move: fe; rewrite cat_nil => /andP-[fe1 fe2].
      move: fk; rewrite cat_nil => /andP-[fk1 fk2].
      move: fn; rewrite cat_nil => /andP-[fn1 fn2].
      move: d; rewrite geq_max => /andP-[d d'].
      apply: lc_branch=>//; apply: IH =>//.
      by rewrite /lcb fc1 fe1 fk1 fn1.
      by rewrite /lcb fc2 fe2 fk2 fn2.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite !cat_nil !seqofopt_nil => /andP-[fcc /andP-[fcc' fc]].
      move: fk; rewrite !cat_nil !seqofopt_nil => /andP-[fck /andP-[fck' fk]].
      have lc_c : lc_ch c by apply: freechan_lc_c; rewrite fcc fck.
      have lc_c' : lc_ch c' by apply: freechan_lc_c; rewrite fcc' fck'.
      by apply: lc_throw=>//; apply: IH =>//; rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite cat_nil seqofopt_nil => /andP-[fcc fc].
      move: fk; rewrite cat_nil seqofopt_nil => /andP-[fck fk].
      have lc_c : lc_ch c by apply: freechan_lc_c; rewrite fcc fck.
      apply: (lc_catch (L:=[::]))=>// x x_notin.
      move: fc; rewrite (free_open_c _ _ x) map_nil => fc.
      move: fe; rewrite (getfree_e_open_c x 0) => fe.
      move: fk; rewrite (getfree_k_open_c x 0) => fk.
      move: fn; rewrite (getfbound_n_open_c x 0) => fn.
      apply: IH; first by rewrite -depth_op_ch.
      by rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite cat_nil => /andP-[fc fc'].
      move: fk; rewrite cat_nil => /andP-[fk fk'].
      move: fn; rewrite cat_nil => /andP-[fn fn'].
      move: fe; rewrite !cat_nil => /andP-[/freeexp_lc-lce /andP-[fe fe']].
      move: d; rewrite geq_max => /andP-[d d'].
      apply: lc_ife =>//.
      by apply: IH =>//; rewrite /lcb fc fe fk fn.
      by apply: IH =>//; rewrite /lcb fc' fe' fk' fn'.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      move: fc; rewrite cat_nil => /andP-[fc fc'].
      move: fk; rewrite cat_nil => /andP-[fk fk'].
      move: fn; rewrite cat_nil => /andP-[fn fn'].
      move: fe; rewrite cat_nil => /andP-[fe fe'].
      move: d; rewrite geq_max => /andP-[d d'].
      apply: lc_par=>//.
      by apply: IH =>//; rewrite /lcb fc fe fk fn.
      by apply: IH =>//; rewrite /lcb fc' fe' fk' fn'.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      apply: (lc_nu_nm (L:=[::])) =>// x x_notin.
      move: fn; rewrite (free_open_n _ _ x) map_nil => fn.
      move: fe; rewrite (getfree_e_open_n x 0) => fe.
      move: fk; rewrite (getfree_k_open_n x 0) => fk.
      move: fc; rewrite (getfbound_c_open_n x 0) => fc.
      apply: IH; first by rewrite -depth_opn_ch.
      by rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      apply: (lc_nu_ch (L:=[::])) =>// x x_notin.
      move: fk; rewrite (free_open_k _ _ x) map_nil => fk.
      move: fe; rewrite (getfree_e_open_k x 0) => fe.
      move: fn; rewrite (getfbound_n_open_k x 0) => fn.
      move: fc; rewrite (getfbound_c_open_k x 0) => fc.
      apply: IH; first by rewrite -depth_opk_ch.
      by rewrite /lcb fc fe fk fn.
    + move=>/andP-[/andP-[/andP-[fc fe] fk] fn].
      apply: lc_bang.
      by apply: IH ; [easy |rewrite /lcb fc fe fk fn].
  }
  (* Case ======> *)
  { rewrite /lcb/fbound_c/fbound_n/free_k/free_e.
    elim=>///=.
    Ltac subst_IH IH :=
      move: IH =>/andP-[/andP-[/andP-[/eqP->/eqP->]/eqP->]/eqP->].
    Ltac easy_lcchan lc_k :=
      move: (lc_c_freechan lc_k) => /andP-[/eqP-> /eqP->] /=.
    Ltac accreq L IH :=
      let x := fresh in
      set x:= LC.fresh L;
      rewrite (free_open_c _ _ x) map_nil cat_nil seqofopt_nil;
      rewrite SC.lc_getfree ///=;
      rewrite (getfree_e_open_c x 0) (getfbound_n_open_c x 0) (getfree_k_open_c x 0);
        by apply: IH; apply: LC.fresh_not_in.
    + move=> L a P' lc_a lc_P' IH; accreq L IH.
    + move=> L a P' lc_a lc_P' IH; accreq L IH.
    + move=> k e P0 lc_k lc_e lc_P0 IH; easy_lcchan lc_k.
      by rewrite !cat_nil lc_freeexp.
    + move=> L k P0 lc_c lc_P0 IH; easy_lcchan lc_c.
      set x:= EV.fresh L; rewrite (free_open_e _ _ x) map_nil.
      rewrite (getfbound_c_open_e x 0) (getfbound_n_open_e x 0) (getfree_k_open_e x 0).
      by apply: IH; apply: EV.fresh_not_in.
    + by move=> k _ P0 lc_k lc_P0 IH; easy_lcchan lc_k.
    + move=> k P0 Q lc_k lc_P0 IH_P0 lc_P1 IH_P1; easy_lcchan lc_k.
      by subst_IH IH_P0; subst_IH IH_P1.
    + by move=> k k' P0 lc_k lc_k' lc_P0 IH; easy_lcchan lc_k; easy_lcchan lc_k'.
    + move=> L k P0 lc_k lc_P0 IH; easy_lcchan lc_k.
      set x:= LC.fresh L; rewrite (free_open_c _ _ x) map_nil.
      rewrite (getfree_e_open_c x 0) (getfbound_n_open_c x 0) (getfree_k_open_c x 0).
      by apply: IH; apply: LC.fresh_not_in.
    + move=> e P0 Q lc_e lc_P0 H_P0 lc_Q H_Q; rewrite !cat_nil lc_freeexp // /=.
      by subst_IH H_P0; subst_IH H_Q.
    + by move=> P0 Q lc_P0 H_P0 lc_Q H_Q; subst_IH H_P0; subst_IH H_Q.
    + move=> L P0 lc_P0 IH.
      set x:= SC.fresh L; rewrite (free_open_n _ _ x) map_nil.
      rewrite (getfree_e_open_n x 0) (getfbound_c_open_n x 0) (getfree_k_open_n x 0).
      by apply: IH; apply: SC.fresh_not_in.
    + move=> L P0 lc_P0 IH.
      set x:= CN.fresh L; rewrite (free_open_k _ _ x) map_nil.
      rewrite (getfree_e_open_k x 0) (getfbound_c_open_k x 0) (getfbound_n_open_k x 0).
      by apply: IH; apply: CN.fresh_not_in.
  }
Qed.

Lemma lc_isfree_k k P : get_fbound_k 0 P == [::] -> ~~ is_fbound_k k P.
Proof. by rewrite /is_fbound_k/free_k /= =>/eqP->. Qed.

Ltac lc_getfree_k H :=
  move: H => /lcP; rewrite /lcb /= => /andP-[/andP-[_ k] _].

Lemma freechan_op_c k n c u :
  k \notin seq_of_opt (fbound_chan_c n c) -> c = opc (n + k) u c.
Proof.
  case: c => //; case => ///= m; case: ifP => /=.
  + rewrite in_cons negb_or => leq /andP-[/negPf].
    by rewrite -(eqn_add2l n) subnKC // =>->.
  + move => /(introT negPf); rewrite -ltnNge => mn _.
    have: (n + k == m) = false by elim: n m mn =>// n IH; case=>//.
    by move=>->.
Qed.

Theorem op_lc k (u : channel) P :
    lc P ->
    P = {op k ~> u} P.
Proof.
  move => /lcP/andP-[/andP-[/andP-[fc _] _] _]; move:fc; rewrite /fbound_c =>fc.
  have : k \notin get_fbound_c 0 P by move: fc => /eqP->.
  (have: k = 0 + k by []); move: fc 0 {2 3}k =>_ n k0.
  elim: P k n u =>///=.
  + move => v p IH k n u eq notin; congr request.
    by apply: (IH k.+1 n.+1)=>//; rewrite addSn -eq.
  + move => v p IH k n u eq notin; congr accept.
    by apply: (IH k.+1 n.+1 _ _ notin); rewrite addSn -eq.
  + move => c e p IH k n u eq; rewrite mem_cat negb_or => /andP-[fc notin].
    by congr send; last (by apply: (IH k n)); rewrite eq -freechan_op_c.
  + move => c p IH k n u eq; rewrite mem_cat negb_or => /andP-[fc notin].
    by congr receive; last (by apply: (IH k n)); rewrite eq -freechan_op_c.
  + move => c l p IH k n u eq; rewrite !mem_cat !negb_or => /andP-[fc notin].
    by congr select ; last (by apply: (IH k n)); rewrite eq -freechan_op_c.
  + move => c p1 IH1 p2 IH2 k n u eq;
      rewrite !mem_cat !negb_or => /andP-[fc /andP-[ninp ninp']].
      by congr branch; [ rewrite eq -freechan_op_c
                       | apply: (IH1 k n)
                       | apply: (IH2 k n) ].
  + move => c1 c2 p IH k n u eq;
      rewrite !mem_cat !negb_or => /andP-[fc /andP-[fc' ninp]].
    by congr throw; [ rewrite eq -freechan_op_c
                    | rewrite eq -freechan_op_c
                    | apply: (IH k n) ].
  + move=> c p IH k n u eq; rewrite !mem_cat !negb_or => /andP-[fc ninp].
    by congr catch; [ rewrite eq -freechan_op_c
                    | apply: (IH k.+1 n.+1) =>//; rewrite addSn -eq ].
  + move=> e p1 IH1 p2 IH2 k n u eq;
             rewrite !mem_cat !negb_or => /andP-[ninp1 ninp2].
    by congr ife; [ apply: (IH1 k n ) | apply: (IH2 k n ) ].
  + move=> p1 IH1 p2 IH2 k n u eq;
             rewrite !mem_cat !negb_or => /andP-[ninp1 ninp2].
    by congr par; [ apply: (IH1 k n ) | apply: (IH2 k n ) ].
  + by move=> p IH k n u eq nin; congr nu_nm; apply: (IH k n).
  + by move=> p IH k n u eq nin; congr nu_ch; apply: (IH k n).
  + by move => p IH k n u eq nin; congr bang; apply: (IH k n).
Qed.

Theorem opn_lc k u P :
    lc P ->
    P = {opn k ~> u} P.
Proof.
  move => /lcP/andP-[/andP-[/andP-[_ _] _] fc]; move:fc; rewrite /fbound_n =>fc.
  have : k \notin get_fbound_n 0 P by move: fc => /eqP->.
  (have: k = 0 + k by []); move: fc 0 {2 3}k =>_ n k0.
  elim: P k n u =>///=.
  + move => v p IH k n u eq; rewrite mem_cat negb_or=>/andP-[notin1 notin2].
    rewrite -(IH k n) //; congr request; move: notin1; rewrite eq.
    case: v=>///= n0; case: ifP=>/= nn0.
    - rewrite in_cons negb_or =>/andP-[neq _]; move: neq =>/negPf.
      by rewrite -(eqn_add2r n) subnK // addnC  =>->.
    - by move=>_; move: nn0; case: ifP =>///eqP<-; rewrite leq_addr.
  + move => v p IH k n u eq; rewrite mem_cat negb_or=>/andP-[notin1 notin2].
    rewrite -(IH k n) //; congr accept; move: notin1; rewrite eq.
    case: v=>///= n0; case: ifP=>/= nn0.
    - rewrite in_cons negb_or =>/andP-[neq _]; move: neq =>/negPf.
      by rewrite -(eqn_add2r n) subnK // addnC  =>->.
    - by move=>_; move: nn0; case: ifP =>///eqP<-; rewrite leq_addr.
  + by move => c e p IH k n u eq fc; congr send; apply: (IH k n).
  + by move => c p IH k n u eq fc; congr receive; apply: (IH k n).
  + by move=> c l p IH k n u eq fc; congr select; apply: (IH k n).
  + move=> c p IHp q IHq k n u eq; rewrite mem_cat negb_or=>/andP-[fc1 fc2].
    by rewrite -(IHp k n) // -(IHq k n).
  + by move => c1 c2 p IH k n u eq fc; congr throw; apply: (IH k n).
  + by move=> c p IH k n u eq fc; congr catch; apply: (IH k n).
  + move=> e p1 IH1 p2 IH2 k n u eq; rewrite mem_cat negb_or => /andP-[fc1 fc2].
    by rewrite -(IH1 k n) // -(IH2 k n).
  + move=> p1 IH1 p2 IH2 k n u eq; rewrite mem_cat negb_or => /andP-[fc1 fc2].
    by rewrite -(IH1 k n) // -(IH2 k n).
  + by move=> p IH k n u eq nin; rewrite -(IH k.+1 n.+1) // eq.
  + by move=> p IH k n u eq nin; congr nu_ch; apply: (IH k n).
  + by move=> p IH k n u eq nin; congr bang; apply: (IH k n).
Qed.

Lemma freechan_op_k k n c u :
  k \notin seq_of_opt (fbound_chan_k n c) -> c = opk (n + k) u c.
Proof.
  case: c => //; case => // m b; case: m =>///= m; case: ifP => /=.
  + rewrite in_cons negb_or => leq /andP-[/negPf].
    by rewrite -(eqn_add2l n) subnKC // =>->.
  + move => /(introT negPf); rewrite -ltnNge => mn _.
    have: (n + k == m) = false by elim: n m mn =>// n IH; case=>//.
    by move=>->.
Qed.

Lemma opk_notfree k n k0 u P :
  k = n + k0 -> k0 \notin get_fbound_k n P -> P = {opkk ~> u} P.
  elim: P k n =>///=.
  + by move => v p IH k n eq notin; congr request; apply: (IH k n).
  + by move => v p IH k n eq notin; congr accept; apply: (IH k n).
  + move => c e p IH k n eq; rewrite mem_cat negb_or => /andP-[fc notin].
    by congr send; last (by apply: (IH k n)); rewrite eq -freechan_op_k.
  + move => c p IH k n eq; rewrite mem_cat negb_or => /andP-[fc notin].
    by congr receive; last (by apply: (IH k n)); rewrite eq -freechan_op_k.
  + move => c l p IH k n eq; rewrite !mem_cat !negb_or => /andP-[fc notin].
    by congr select ; last (by apply: (IH k n)); rewrite eq -freechan_op_k.
  + move => c p1 IH1 p2 IH2 k n eq;
      rewrite !mem_cat !negb_or => /andP-[fc /andP-[ninp ninp']].
      by congr branch; [ rewrite eq -freechan_op_k
                       | apply: (IH1 k n)
                       | apply: (IH2 k n) ].
  + move => c1 c2 p IH k n eq;
      rewrite !mem_cat !negb_or => /andP-[fc /andP-[fc' ninp]].
    by congr throw; [ rewrite eq -freechan_op_k
                    | rewrite eq -freechan_op_k
                    | apply: (IH k n) ].
  + move=> c p IH k n eq; rewrite !mem_cat !negb_or => /andP-[fc ninp].
    by congr catch; [ rewrite eq -freechan_op_k
                    | apply: (IH k n) =>//; rewrite addSn -eq ].
  + move=> e p1 IH1 p2 IH2 k n eq;
             rewrite !mem_cat !negb_or => /andP-[ninp1 ninp2].
    by congr ife; [ apply: (IH1 k n ) | apply: (IH2 k n ) ].
  + move=> p1 IH1 p2 IH2 k n eq;
             rewrite !mem_cat !negb_or => /andP-[ninp1 ninp2].
    by congr par; [ apply: (IH1 k n ) | apply: (IH2 k n ) ].
  + by move=> p IH k n eq nin; congr nu_nm; apply: (IH k n).
  + move=> p IH k n eq nin; congr nu_ch.
    by apply: (IH k.+1 n.+1)=>//; rewrite addSn eq.
  + move=> p IH k n eq nin ; congr bang.
    by apply: (IH k n) =>//; rewrite addSn eq.
Qed.

(* FIXME: the theorems below are VERY similar, how can we generalise? *)
Theorem opk_lc k u P :
    lc P ->
    P = {opk k ~> u} P.
Proof.
  move => /lcP/andP-[/andP-[/andP-[_ _] fk] _]; move:fk; rewrite /free_k =>fk.
  have : k \notin get_fbound_k 0 P by move: fk => /eqP->.
  (have: k = 0 + k by []); move: fk 0 {2 3}k =>_ n k0.
  apply: opk_notfree.
Qed.

Definition subst_ch (z : LC.atom) (k' : channel) (k : channel) : channel :=
  if k == LC.Free z then k' else k.

Definition subst_exp (z : EV.atom) (u : exp) (e : exp) : exp :=
  match e with
  | V (EV.Free b) => if z == b then u else e
  | _ => e
  end.

Fixpoint subst_proc (z : LC.atom) (u : channel) (P : proc) : proc :=
  match P with
  | request a P => request a (subst_proc z u P)
  | accept a P => accept a (subst_proc z u P)
  | send k e P => send (subst_ch z u k) e (subst_proc z u P)
  | receive k P => receive (subst_ch z u k) (subst_proc z u P)
  | select k l P => select (subst_ch z u k) l (subst_proc z u P)
  | branch k P Q => branch (subst_ch z u k) (subst_proc z u P) (subst_proc z u Q)
  | throw k k' P => throw (subst_ch z u k) (subst_ch z u k') (subst_proc z u P)
  | catch k P => catch (subst_ch z u k) (subst_proc z u P)
  | ife e P Q => ife e (subst_proc z u P) (subst_proc z u Q)
  | par P Q => par (subst_proc z u P) (subst_proc z u Q)
  | inact => inact
  | nu_nm P => nu_nm (subst_proc z u P)
  | nu_ch P => nu_ch (subst_proc z u P)
  | bang P => bang (subst_proc z u P)
  end.

Definition subst_chk (z k' : CN.atom) (k : channel) : channel :=
  if k is Ch (CN.Free z', p)
  then if z == z' then Ch (CN.Free k', p)
       else k
  else k.

Fixpoint subst_prock (z : CN.atom) (u : CN.atom) (P : proc) : proc :=
  match P with
  | request a P => request a (subst_prock z u P)
  | accept a P => accept a (subst_prock z u P)
  | send k e P => send (subst_chk z u k) e (subst_prock z u P)
  | receive k P => receive (subst_chk z u k) (subst_prock z u P)
  | select k l P => select (subst_chk z u k) l (subst_prock z u P)
  | branch k P Q => branch (subst_chk z u k) (subst_prock z u P) (subst_prock z u Q)
  | throw k k' P => throw (subst_chk z u k) (subst_chk z u k') (subst_prock z u P)
  | catch k P => catch (subst_chk z u k) (subst_prock z u P)
  | ife e P Q => ife e (subst_prock z u P) (subst_prock z u Q)
  | par P Q => par (subst_prock z u P) (subst_prock z u Q)
  | inact => inact
  | nu_nm P => nu_nm (subst_prock z u P)
  | nu_ch P => nu_ch (subst_prock z u P)
  | bang P => bang (subst_prock z u P)
  end.

Fixpoint subst_ept (z : SC.atom) (u : SC.atom) (P : proc) : proc :=
  match P with
  | request a P => request (if a == SC.Free z then SC.Free u else a) (subst_ept z u P)
  | accept a P => accept (if a == SC.Free z then SC.Free u else a) (subst_ept z u P)
  | send k e P => send k e (subst_ept z u P)
  | receive k P => receive k (subst_ept z u P)
  | select k l P => select k l (subst_ept z u P)
  | branch k P Q => branch k (subst_ept z u P) (subst_ept z u Q)
  | throw k k' P => throw k k' (subst_ept z u P)
  | catch k P => catch k (subst_ept z u P)
  | ife e P Q => ife e (subst_ept z u P) (subst_ept z u Q)
  | par P Q => par (subst_ept z u P) (subst_ept z u Q)
  | inact => inact
  | nu_nm P => nu_nm (subst_ept z u P)
  | nu_ch P => nu_ch (subst_ept z u P)
  | bang P => bang (subst_ept z u P)
  end.

Fixpoint subst_proc_exp (z : EV.atom) (e : exp) (P : proc) : proc :=
  match P with
  | request a P => request a (subst_proc_exp z e P)
  | accept a P => accept a (subst_proc_exp z e P)
  | send k e' P => send k (subst_exp z e e') (subst_proc_exp z e P)
  | receive k P => receive k (subst_proc_exp z e P)
  | select k l P => select k l (subst_proc_exp z e P)
  | branch k P Q => branch k (subst_proc_exp z e P) (subst_proc_exp z e Q)
  | throw k k' P => throw k k' (subst_proc_exp z e P)
  | catch k P => catch k (subst_proc_exp z e P)
  | ife e' P Q => ife (subst_exp z e e') (subst_proc_exp z e P) (subst_proc_exp z e Q)
  | par P Q => par (subst_proc_exp z e P) (subst_proc_exp z e Q)
  | inact => inact
  | nu_nm P => nu_nm (subst_proc_exp z e P)
  | nu_ch P => nu_ch (subst_proc_exp z e P)
  | bang P => bang (subst_proc_exp z e P)
  end.

(* Notation "s[ z ~> u ]n a" := (subst_nm z u a) (at level 68) : sr_scope. *)
Notation "s[ z ~> u ]c k" := (subst_ch z u k) (at level 68) : sr_scope.
Notation "s[ z ~> u ]e e" := (subst_exp z u e) (at level 68) : sr_scope.
Notation "s[ z ~> u ]p P" := (subst_proc z u P) (at level 68) : sr_scope.
Notation "s[ z ~> e ]pe P" := (subst_proc_exp z e P) (at level 68) : sr_scope.

Lemma subst_ch_in_ch x u k:
  s[ x ~> u ]c ch k = (ch k).
Proof.
  move: k.
  by case.
Qed.

Definition fv_ch (k : channel) : seq LC.atom :=
  match k with
  | LC.Free a => [::a]
  | _ => [::]
  end.

Definition fv_exp (e : exp) : seq EV.atom :=
  match e with
    | V (EV.Free a) => [::a]
    | _ => [::]
  end.

Fixpoint fv_e (P : proc) : seq EV.atom :=
  match P with
  | request _ P
  | receive _ P
  | select _ _ P
  | throw _ _ P
  | catch _ P
  | nu_nm P
  | nu_ch P
  | bang P
  | accept _ P => fv_e P
  | send _ e P => fv_exp e ++ fv_e P
  | ife e P Q => fv_exp e ++ fv_e P ++ fv_e Q
  | branch _ P Q
  | par P Q => fv_e P ++ fv_e Q
  | inact => [::]
  end.

Fixpoint fv (P : proc) : seq LC.atom :=
  match P with
  | request a P => fv P
  | accept a P => fv P
  | send k e P => fv_ch k ++ fv P
  | receive k P => fv_ch k ++ fv P
  | select k l P => fv_ch k ++ fv P
  | branch k P Q => fv_ch k ++ fv P ++ fv Q
  | throw k k' P => fv_ch k ++ fv_ch k' ++ fv P
  | catch k P => fv_ch k ++ fv P
  | ife e P Q => fv P ++ fv Q
  | par P Q => fv P ++ fv Q
  | inact => [::]
  | nu_nm P => fv P
  | nu_ch P => fv P
  | bang P => fv P
  end.

Definition free_nm (a : SC.var) : seq SC.atom :=
  match a with
  | SC.Free v => [:: v]
  | _ => [::]
  end.

Fixpoint fn (P : proc) : seq SC.atom :=
  match P with
  | request a P
  | accept a P => free_nm a ++ fn P
  | send _ _ P
  | receive _ P
  | select _ _ P
  | throw _ _ P
  | catch _ P
  | nu_nm P
  | nu_ch P => fn P
  | branch _ P Q
  | ife _ P Q
  | par P Q => fn P ++ fn Q
  | inact => [::]
  | bang P => fn P
  end.

Definition fv_k (k : channel) : seq CN.atom :=
  match k with
  | Ch (CN.Free a, _) => [::a]
  | _ => [::]
  end.

Fixpoint freev_k (P:proc) : seq CN.atom :=
  match P with
  | request a P => freev_k P
  | accept a P => freev_k P
  | send k e P => fv_k k ++ freev_k P
  | receive k P => fv_k k ++ freev_k P
  | select k l P => fv_k k ++ freev_k P
  | branch k P Q => fv_k k ++ freev_k P ++ freev_k Q
  | throw k k' P => fv_k k ++ fv_k k' ++ freev_k P
  | catch k P => fv_k k ++ freev_k P
  | ife e P Q => freev_k P ++ freev_k Q
  | par P Q => freev_k P ++ freev_k Q
  | inact => [::]
  | nu_nm P => freev_k P
  | nu_ch P => freev_k P
  | bang P => freev_k P
  end.

Lemma in_fvk_opc k n nc c :
  k \notin fv_k nc -> (k \in fv_k (opc n nc c)) = (k \in fv_k c).
Proof. by case: c=>//; case=>///=n0; case: ifP=>// _ /negPf->. Qed.

Lemma in_fvk_shift_ch k c :
  (k \notin fv_k c) = (k \notin fv_k (shift_ch c)).
Proof. by case: c=>//[][[] p]. Qed.

Lemma freek_openc k P nc:
  k \notin fv_k nc ->
  (k \in freev_k (open_c0 P nc)) = (k \in freev_k P).
Proof.
  move=> k_nc.
  rewrite /open_c0; move: 0=> n.
  elim: P n nc k_nc
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n nc k_nc /=//;
  try (rewrite !mem_cat ?inE =>//);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !orbA =>//);
  try (rewrite !in_fvk_opc =>//);
  try (rewrite -!in_fvk_shift_ch =>//).
Qed.

Lemma freek_opene k P nc:
  (k \in freev_k (open_e0 P nc)) = (k \in freev_k P).
Proof.
  rewrite /open_e0; move: 0=> n.
  elim: P n nc
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n nc /=//;
  try (rewrite !mem_cat ?inE =>//);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !orbA =>//).
Qed.

Lemma freek_openn k P nc:
  (k \in freev_k (open_n0 P nc)) = (k \in freev_k P).
Proof.
  rewrite /open_n0; move: 0=> n.
  elim: P n nc
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n nc /=//;
  try (rewrite !mem_cat ?inE =>//);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !orbA =>//).
Qed.

Lemma fvk_opk k n nc c :
  nc != CN.Free k -> (k \in fv_k (opk n nc c)) = (k \in fv_k c).
Proof.
  case: c=>//[][[aa|an] p]/=//; case: ifP=>//; case: nc=>// a _.
  by rewrite -[CN.Free _ == _]/(a == k) in_cons eq_sym =>/negPf->.
Qed.


Lemma freek_openk k P nc:
   nc != CN.Free k ->
  (k \in freev_k (open_k0 P nc)) = (k \in freev_k P).
Proof.
  rewrite /open_k0; move: 0=> n.
  elim: P n nc
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n nc neq /=//;
  try (rewrite !mem_cat ?inE =>//);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !orbA =>//);
  try (rewrite !fvk_opk =>//).
Qed.

Lemma fv_fbv_chk n c k :
  0 \in seq_of_opt (fbound_chan_k n c) -> k \in fv_k (opk n (CN.Free k) c).
Proof.
  case: c=>//;case;case=>[a|m] p///=.
  case: ifP=>/=//Le; rewrite in_cons=>/orP-[|//].
  rewrite eq_sym subn_eq0; move=> /(conj Le)/andP.
    by rewrite -eqn_leq=>->; rewrite in_cons eq_refl.
Qed.

Lemma fv_fbv_k P k :
  0 \in free_k P -> k \in freev_k (open_k0 P (CN.Free k)).
Proof.
  rewrite /open_k0/free_k; move: {-1}0.
  elim: P
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n /=//;
  try (rewrite !mem_cat ?inE =>//);
  try (move=>/orP-[H|/orP-[H|H]]);
  try (move=>/orP-[H|H]);
  try (move=>H);
  try (rewrite (IH _ H) =>//);
  try (rewrite (IH _ H) =>//);
  try (rewrite (IH1 _ H) =>//);
  try (rewrite (IH2 _ H) =>//);
  try (rewrite (fv_fbv_chk _ H) =>//);
  try (rewrite !Bool.orb_true_r=>//).
Qed.

(* some properties of the operations *)

Lemma subst_fresh_exp : forall x a e,
    x \notin fv_exp e -> subst_exp x a e = e.
Proof.
  by move=> x e; elim=>//[][]/=//a; rewrite in_cons negb_or=>/andP-[/negPf->_].
Qed.

Lemma subst_fresh_e : forall (x : EV.atom) P a,
    x \notin fv_e P -> s[ x ~> a]pe P = P.
Proof.
  move=>x P a;
  elim: P
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] /=;
  try (rewrite !mem_cat !negb_or);
  try (move => /andP-[nin1 /andP-[nin2 nin3]]);
  try (move => /andP-[nin1 nin2]);
  try (move=>nin);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite subst_fresh_exp =>//);
  easy.
Qed.

Lemma fve_openc P k : fv_e (open_c0 P k) = fv_e P.
Proof.
  rewrite /open_c0; move:0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//).
Qed.

Lemma fve_openn P k : fv_e (open_n0 P k) = fv_e P.
Proof.
  rewrite /open_n0; move:0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//).
Qed.

Lemma fve_openk P k : fv_e (open_k0 P k) = fv_e P.
Proof.
  rewrite /open_k0; move:0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//).
Qed.

Lemma fvexp_ope e n x y :
  x \notin fv_exp y -> x \notin fv_exp e ->
  x \notin fv_exp (ope n y e).
Proof. by elim: e=>// [][]/=//m; case: ifP=>/=//; rewrite in_cons=>_/negPf->. Qed.

Lemma fve_opene P x y :
  x \notin fv_exp y -> x \notin fv_e P ->
  x \notin fv_e (open_e0 P y).
Proof.
  rewrite /open_e0; move: 0.
  elim: P
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n neq /=//;
  try (rewrite !mem_cat !negb_or);
  try (move => /andP-[nin1 /andP-[nin2 nin3]]);
  try (move => /andP-[nin1 nin2]);
  try (move => nin);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite fvexp_ope=>//).
Qed.

Lemma subst_opc x k c n : x \notin fv_ch c -> s[ x ~> k ]c opc n x c = opc n k c.
Proof.
  case: c=>[[a b]|[a|m _]]/=//; rewrite /subst_ch eq_sym.
  + by rewrite -[Var _ == _]/(x == a) in_cons negb_or => /andP-[/negPf->].
  + by case: (ifP (n == m))=>//; rewrite eq_refl.
Qed.

Lemma subst_proc_open x k P :
  lc_ch k ->
  x \notin fv P -> s[ x ~> k ]p (open_c0 P x) = {op 0 ~> k} P.
Proof.
  move=> lc_k; rewrite /open_c0; move: 0.
  elim: P
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n /=//;
  try (rewrite !mem_cat !negb_or);
  try (move => /andP-[nin1 /andP-[nin2 nin3]]);
  try (move => /andP-[nin1 nin2]);
  try (move => nin);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !shift_ch_lc=>//);
  try (rewrite !subst_opc=>//).
Qed.

Lemma subst_chk_opk x k n c :
  x \notin fv_k c -> subst_chk x k (opk n x c) = opk n k c.
Proof.
  case: c=>//; case; case=>/=[a|m] p; first by
      rewrite in_cons negb_or=>/andP-[/negPf->].
    by move=>_; case: ifP=>//; rewrite eq_refl.
Qed.

Lemma substk_openk x k P :
  x \notin freev_k P -> subst_prock x k (open_k0 P x) = open_k0 P k.
Proof.
  rewrite /open_k0; move: 0.
  elim: P
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] n /=//;
  try (rewrite !mem_cat !negb_or);
  try (move => /andP-[nin1 /andP-[nin2 nin3]]);
  try (move => /andP-[nin1 nin2]);
  try (move => nin);
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !shift_ch_lc=>//);
  try (rewrite !subst_chk_opk=>//).
Qed.

Lemma openc_subst_ept a a' k P :
  open_c0 (subst_ept a a' P) k = subst_ept a a' (open_c0 P k).
Proof.
  rewrite /open_c0; move: 0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//).
Qed.

Lemma opene_subst_ept a a' k P :
  open_e0 (subst_ept a a' P) k = subst_ept a a' (open_e0 P k).
Proof.
  rewrite /open_e0; move: 0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//).
Qed.

Lemma openk_subst_ept a a' k P :
  open_k0 (subst_ept a a' P) k = subst_ept a a' (open_k0 P k).
Proof.
  rewrite /open_k0; move: 0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//).
Qed.

Lemma openn_subst_ept a a' k P :
  k != a ->
  open_n0 (subst_ept a a' P) k = subst_ept a a' (open_n0 P k).
Proof.
  move=> k_a; rewrite /open_n0; move: 0.
  elim: P k k_a
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k k_a n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (case: ifP=>[/eqP->|]/=; first (by rewrite eq_refl);
    case: v=>/=[a0->|n0]//; case: ifP=>[/eqP->|];
    first (by rewrite -[SC.Free _ == _]/(k == a) (negPf k_a));
    move=>_-> //).
Qed.


Lemma opk_substk (a a' : CN.atom) k n c :
  k != a ->
  opk n k (subst_chk a a' c) = subst_chk a a' (opk n k c).
Proof.
  by case: c=>//[][[ka|kn] kp]/=; case: ifP=>// _; rewrite eq_sym=>/negPf->.
Qed.

Lemma openk_substk a a' k P :
  k != a ->
  open_k0 (subst_prock a a' P) k = subst_prock a a' (open_k0 P k).
Proof.
  move=> k_a; rewrite /open_k0; move: 0.
  elim: P k k_a
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k k_a n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !opk_substk=>//).
Qed.

Lemma opene_substk a a' k P :
  open_e0 (subst_prock a a' P) k = subst_prock a a' (open_e0 P k).
Proof.
  rewrite /open_e0; move: 0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !opk_substk=>//).
Qed.

Lemma openn_substk a a' k P :
  open_n0 (subst_prock a a' P) k = subst_prock a a' (open_n0 P k).
Proof.
  rewrite /open_n0; move: 0.
  elim: P k
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !opk_substk=>//).
Qed.

Lemma opc_substk (a a' : CN.atom) k n c :
  a \notin fv_k k ->
  opc n k (subst_chk a a' c) = subst_chk a a' (opc n k c).
Proof.
  case: c=>[[[ka|kn] kp]|cn]/=//; first by case: ifP.
  case: cn=>//m/=; case: ifP=>//; case: k=>//[][[kb|km] pb]///=.
  by rewrite in_cons negb_or =>_ /andP-[/negPf->].
Qed.

Lemma openc_substk a a' k P :
  a \notin fv_k k ->
  open_c0 (subst_prock a a' P) k = subst_prock a a' (open_c0 P k).
Proof.
  move=> k_a; rewrite /open_c0; move: 0.
  elim: P k k_a
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] k k_a n /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !opc_substk=>//).
  move: k k_a => {IH} {n} {p} {a'}. (*FIXME: define as lemma*)
  by do ! case=>//.
Qed.

Lemma substchk_same k c : subst_chk k k c = c.
Proof.
  by move: c; do ! case=>//; move=>/= a b; case: ifP=>[/eqP->|].
Qed.

Lemma substk_same k P : subst_prock k k P = P.
Proof.
  elim: P
  => [ v p IH
     | v p IH
     | c e p IH
     | c p IH
     | c l p IH
     | c p1 IH1 p2 IH2
     | c1 c2 p IH
     | c p IH
     | e p1 IH1 p2 IH2
     | p1 IH1 p2 IH2
     |
     | p IH
     | p IH
     | p IH] /=//;
  try (rewrite IH =>//);
  try (rewrite IH1 =>//);
  try (rewrite IH2 =>//);
  try (rewrite !substchk_same=>//).
Qed.

Fixpoint cotype (t : tp) : tp :=
  match t with
  | input s t => output s (cotype t)
  | output s t => output s (cotype t)
  | ch_input t t' => ch_output t (cotype t')
  | ch_output t t' => ch_input t (cotype t')
  | offer_branch t t' => take_branch (cotype t) (cotype t')
  | take_branch t t' => offer_branch (cotype t) (cotype t')
  | end_proc => end_proc
  end
.

(* structural congruence *)

Reserved Notation "P === Q" (at level 70).
Inductive congruent : proc -> proc -> Set :=
| c_refl P: P === P (* replaces alpha because LN has alpha equivalence built in *)
| c_inact P : (par inact P) === P
| c_comm P Q: (par P Q) === (par Q P)
| c_asoc P Q R: (par (par P Q) R) === (par P (par Q R))
| c_nu_nm P Q: lc Q -> (par (nu_nm P) Q) === (nu_nm (par P Q))
| c_nu_ch P Q: lc Q -> (par (nu_ch P) Q) === (nu_ch (par P Q))
| c_nu_nm_inact : nu_nm inact === inact
| c_nu_ch_inact : nu_ch inact === inact
| c_bang P : bang P === par P (bang P)
where "P === Q" := (congruent P Q).
(* other congruence rules when I have the simpler version of recursion *)
(* we may need to add *)

(* reductions *)

Reserved Notation "P --> Q" (at level 70).
Inductive red : proc -> proc -> Prop :=
| r_link P Q a:
    lc (accept a P) -> lc (request a Q) ->
    (par (accept a P) (request a Q)) -->
        (* consider using open and close to not refer to the 0 db index *)
        (nu_ch (par (open_c0 P (Ch (CN.Bound 0, Pos))) (open_c0 Q (Ch (CN.Bound 0, Neg)))))

| r_com (k : CN.atom) p pd e P Q:
    lc P -> body Q -> dual_pol p == pd -> (* use open_e instead of ope *)
    (par (send (ch (k, p)) e P) (receive (ch (k, pd)) Q)) --> (par P ({ope 0 ~> e} Q))

| r_pass (k : CN.atom) p pd k' P Q:
    lc P -> body Q -> dual_pol p == pd -> (* use openk insted op *)
    (par (throw (ch (k, p)) k' P) (catch (ch (k, pd)) Q)) --> (par P ({op 0 ~> k'} Q))

| r_cong P P' Q Q' :
    lc P -> lc Q ->
    P === P' ->
    P' --> Q' ->
    Q' === Q ->
    P --> Q

| r_scop_nm P P':
    (forall (L : seq SC.atom) x,
        x \notin L -> (open_n0 P (SC.Free x)) --> (open_n0 P' (SC.Free x))) ->
    nu_nm P --> nu_nm P'

| r_scop_ch P P':
    (forall (L : seq CN.atom) k,
        k \notin L -> (open_k0 P (CN.Free k)) --> (open_k0 P' (CN.Free k))) ->
    nu_ch P --> nu_ch P'

| r_par P P' Q:
    lc Q ->
    P --> P' ->
    par P Q --> par P' Q

| r_sel_l k kd P Pl Pr:
    lc P -> lc Pl -> lc Pr -> dual_ch k kd ->
    par (select k left P) (branch kd Pl Pr) --> par P Pl

| r_sel_r k kd P Pl Pr:
    lc P -> lc Pl -> lc Pr -> dual_ch k kd ->
    par (select k right P) (branch kd Pl Pr) --> par P Pr

| r_if_tt P Q: ife tt P Q --> P
| r_if_ff P Q: ife ff P Q -->  Q
where "P --> Q" := (red P Q).

Reserved Notation "P -->* Q" (at level 70).
Inductive red_st : proc -> proc -> Prop :=
| r_done P : P -->* P
| r_step P Q R: P --> Q -> Q -->* R -> P -->* R
where "P -->* Q" := (red_st P Q).