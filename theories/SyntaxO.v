(* The Send Receive System. *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import SendRec.Atom.

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
  | bot : tp
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
  | bot => bot
  end
.

Lemma dual_is_dual t : dual (dual t) = t.
  elim t=>// ; rewrite/dual ; move=>//; rewrite-/dual ;
    do ? (move=> s t0 =>->) ;
    do ? (move=> t0 R' t1 =>->) ;
    rewrite ?R' ;
   easy.
Qed.

Lemma double_dual t: t = dual(dual t).
Proof.
  elim t=>//; rewrite/dual=>//; rewrite-/dual ; congruence.
Qed.

Fixpoint eq_tp (T T': tp) : bool :=
  match T, T' with
  | input s T, input s' T' => eq_sort s s' && eq_tp T T'
  | output s T, output s' T' => eq_sort s s' && eq_tp T T'
  | ch_input T1 T2, ch_input T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | ch_output T1 T2, ch_output T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'

  | offer_branch T1 T2, offer_branch T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | take_branch T1 T2, take_branch T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | ended, ended => true
  | bot, bot => true
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
Qed.

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

Inductive name : Set :=
  | fnm : atom -> name
  | bnm : nat -> name
.

Coercion bnm : nat >-> name.
Coercion fnm : atom >-> name.

(* atoms are not a separate set from names *)
Definition channel := name.

Inductive exp : Set :=
  | tt
  | ff
  | var : name -> exp
.

(* CoInductive just because we don't need an induction principle *)
CoInductive label : Set := left | right.

Inductive proc : Set :=
(* request name over a bound channel with polarity and behave like proc *)
| request : name -> proc -> proc
| accept : name -> proc -> proc

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
| nu_ch : proc -> proc (* hides a channel *)

| bang : proc -> proc (* process replication *)
.
Hint Constructors proc.

(* Notation "k ![ e ] ; P" := (send k e P) (at level 67). *)
(* Notation "k ?() `in P" := (receive k P) (at level 67). *)

(* Open a bound variable in a name *)
Definition orn (n : nat) (u : name) (nm : name) : name :=
  match nm with
    | fnm k => fnm k
    | bnm i => if n == i then u else bnm i
  end.

(* Open a bound variable in an expression *)
Definition oe (n : nat) (e' : exp) (e : exp) : exp :=
  match e with
    | var (bnm i) => if n == i then e' else e
    | _ => e
  end.

Fixpoint op_with_nm (n : nat) (u : name) (P : proc) : proc :=
  match P with
  | request a P => request (orn n u a) (op_with_nm (S n) u P)
  | accept a P => accept (orn n u a) (op_with_nm (S n) u P)
  | send k e P => send (orn n u k) e (op_with_nm n u P)
  | receive k P => receive (orn n u k) (op_with_nm (S n) u P)
  | select k l P => select (orn n u k) l (op_with_nm n u P)
  | throw k k' P => throw (orn n u k) (orn n u k') (op_with_nm n u P)
  | catch k P => catch (orn n u k) (op_with_nm (S n) u P)
  | branch k P Q => branch (orn n u k) (op_with_nm n u P) (op_with_nm n u Q)
  | ife e P Q => ife e (op_with_nm n u P) (op_with_nm n u Q)
  | par P Q => par (op_with_nm n u P) (op_with_nm n u Q)
  | inact => inact
  | nu_nm P => nu_nm (op_with_nm (S n) u P)
  | nu_ch P => nu_ch (op_with_nm (S n) u P)
  | bang P => (op_with_nm n u P)
  end.

Fixpoint op_with_exp (n : nat) (u : exp) (P : proc) : proc :=
  match P with
  | request a P => request a (op_with_exp (S n) u P)
  | accept a P => accept a (op_with_exp (S n) u P)
  | send k e P => send k (oe n u e) (op_with_exp n u P)
  | receive k P => receive k (op_with_exp (S n) u P)
  | select k l P => select k l (op_with_exp n u P)
  | throw k k' P => throw k k' (op_with_exp n u P)
  | catch k P => catch k (op_with_exp (S n) u P)
  | branch k P Q => branch k (op_with_exp n u P) (op_with_exp n u Q)
  | ife e P Q => ife (oe n u e) (op_with_exp n u P) (op_with_exp n u Q)
  | par P Q => par (op_with_exp n u P) (op_with_exp n u Q)
  | inact => inact
  | nu_nm P => nu_nm (op_with_exp (S n) u P)
  | nu_ch P => nu_ch (op_with_exp (S n) u P)
  | bang P => bang (op_with_exp n u P)
  end.

Notation "{op k ~> u } t" := (op_with_nm k u t) (at level 67) : sr_scope.
Notation "{ope k ~> e } t" := (op_with_exp k e t) (at level 67) : sr_scope.
Open Scope sr_scope.

Definition open P u :={op 0~>u} P.
Definition opene P u :={ope 0~>u} P.

Inductive lc_nm : name -> Prop :=
  | lc_name x: lc_nm (fnm x)
.

Hint Constructors lc_nm.

Inductive lc_exp : exp -> Prop :=
  | lc_tt : lc_exp tt
  | lc_ff : lc_exp ff
  | lc_var x of lc_nm x: lc_exp (var x)
.

Hint Constructors lc_exp.

(* consider a boolean function instead of this inductive def *)
Inductive lc : proc -> Prop :=
| lc_request : forall (L : seq atom) a P,
    lc_nm a ->
    (forall x, x \notin L -> lc (open P x)) ->
    lc (request a P)

| lc_accept : forall (L : seq atom) a P,
    lc_nm a ->
    (forall x, x \notin L -> lc (open P x)) ->
    lc (accept a P)

| lc_send : forall k e P,
    lc_nm k ->
    lc_exp e ->
    lc P ->
    lc (send k e P)

| lc_receive : forall (L : seq atom) k P,
    lc_nm k ->
    (forall x, x \notin L -> lc (opene P (var x))) ->
    lc (receive k P)

| lc_select : forall k l P,
    lc_nm k ->
    lc P ->
    lc (select k l P)

| lc_branch : forall k P Q,
    lc_nm k ->
    lc P -> lc Q ->
    lc (branch k P Q)

| lc_throw : forall k k' P,
    lc_nm k -> lc_nm k' ->
    lc P ->
    lc (throw k k' P)

| lc_catch : forall (L : seq atom) k P,
    lc_nm k ->
    (forall x, x \notin L -> lc (open P x)) ->
    lc (catch k P)

| lc_ife : forall e P Q,
    lc_exp e -> lc P -> lc Q ->
    lc (ife e P Q)

| lc_par : forall P Q,
    lc P -> lc Q ->
    lc (par P Q)

| lc_inact : lc inact

| lc_nu_nm : forall (L : seq atom) P,
    (forall x, x \notin L -> lc (open P x)) ->
    lc (nu_nm P)

| lc_nu_ch : forall (L : seq atom) P,
    (forall x, x \notin L -> lc (open P x)) ->
    lc (nu_ch P)
| lc_bang P : lc P -> lc (bang P)
.
Hint Constructors lc.

Definition body P := forall (L : seq atom) x, x \notin L -> lc (open P x).
(* substitutions *) (* substitute free atom z by channel u in ... *)
Definition subst_ch (z : atom) (u : channel) (k : channel) : channel :=
  match k with
  | fnm k' => if z == k' then u else k
  | _ => k
  end.

Definition subst_exp (x : atom) (e' : exp) (e : exp) : exp :=
  match e with
    | var (fnm y) => if x == y then e' else e
    | _ => e
  end.

(* consider removing this as it is not an operation for the original system *)
Fixpoint subst_proc (z : atom) (u : channel) (P : proc) : proc :=
  match P with
  | request a P => request (subst_ch z u a) (subst_proc z u P)
  | accept a P => accept (subst_ch z u a) (subst_proc z u P)
  | send k e P => send (subst_ch z u k) e (* (subst_exp z u e) *) (subst_proc z u P)
  | receive k P => receive (subst_ch z u k) (subst_proc z u P)
  | select k l P => select (subst_ch z u k) l (subst_proc z u P)
  | branch k P Q => branch (subst_ch z u k) (subst_proc z u P) (subst_proc z u Q)
  | throw k k' P => throw (subst_ch z u k) (subst_ch z u k') (subst_proc z u P)
  | catch k P => catch (subst_ch z u k) (subst_proc z u P)
  | ife e P Q => ife e (* (subst_exp z u e) *) (subst_proc z u P) (subst_proc z u Q)
  | par P Q => par (subst_proc z u P) (subst_proc z u Q)
  | inact => inact
  | nu_nm P => nu_nm (subst_proc z u P)
  | nu_ch P => nu_ch (subst_proc z u P)
  | bang P => bang (subst_proc z u P)
  end.

Fixpoint subst_proc_exp (z : atom) (e : exp) (P : proc) : proc :=
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

Notation "s[ z ~> u ]p P" := (subst_proc z u P) (at level 68) : sr_scope.
Notation "s[ z ~> u ]pe P" := (subst_proc_exp z u P) (at level 68) : sr_scope.

(* free variables *)

Definition fv_nm (a : name) : seq atom :=
  match a with
  | fnm x => [:: x]
  | _ => [::]
end.

Definition fv_exp (e : exp) : seq atom :=
  match e with
    | tt => [::]
    | ff => [::]
    | var a => fv_nm a
  end.

Fixpoint fv (P : proc) : seq atom :=
  match P with
  | request a P => fv_nm a ++ fv P
  | accept a P => fv_nm a ++ fv P
  | send k e P => fv_nm k ++ fv_exp e ++ fv P
  | receive k P => fv_nm k ++ fv P
  | select k l P => fv_nm k ++ fv P
  | branch k P Q => fv_nm k ++ fv P ++ fv Q
  | throw k k' P => fv_nm k ++ fv_nm k' ++ fv P
  | catch k P => fv_nm k ++ fv P
  | ife e P Q => fv_exp e ++ fv P ++ fv Q
  | par P Q => fv P ++ fv Q
  | inact => [::]
  | nu_nm P => fv P
  | nu_ch P => fv P
  | bang P => fv P
  end.

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

(* just to show properties of substitution and locally closedness *)

Lemma subst_lc_nm : forall (x : atom) a b,
    lc_nm b ->
    lc_nm a ->
    lc_nm (subst_ch x a b).
Proof.
  intros.
  induction H ; simpl ; auto.
  destruct (x == x0) ; easy.
Qed.

(* structural congruence *)

Reserved Notation "P === Q" (at level 70).
Inductive congruent : proc -> proc -> Set :=
| c_refl P : P === P (* replaces alpha because LN has alpha equivalence built in *)
| c_inact P : (par inact P) === P
| c_comm P Q: (par P Q) === (par Q P)
| c_asoc P Q R: (par (par P Q) R) === (par P (par Q R))
| c_nu_nm P Q: (par (nu_nm P) Q) === (nu_nm (par P Q))
| c_nu_ch P Q: (par (nu_ch P) Q) === (nu_ch (par P Q))
| c_nu_nm_inact : nu_nm inact === inact
| c_nu_ch_inact : nu_ch inact === inact
| c_bang P : bang P === par P (bang P)
where "P === Q" := (congruent P Q).
(* other congruence rules when I have the simpler version of recursion *)

(* reductions *)

Reserved Notation "P --> Q" (at level 70).
Inductive red : proc -> proc -> Prop :=
| r_link P Q a:
    body P -> body Q ->
    (par (accept a P) (accept a Q)) -->
        (nu_nm (par P Q))

| r_com k e P Q:
    lc P -> body Q ->
    (par (send k e P) (receive k Q)) --> (par P (opene Q e))

| r_pass k k' P Q:
    lc P -> body Q ->
    (par (throw k k' P) (catch k Q)) --> (par P (open Q k')) (* <-- k' is not like on the paper *)

| r_cong P P' Q Q' :
    lc P -> lc Q ->
    P === P' ->
    P' --> Q' ->
    Q' === Q ->
    P --> Q

| r_scop_nm P P':
    (forall (L : seq atom) x, x \notin L -> (open P x) --> (open P' x)) ->
    nu_nm P --> nu_nm P'

| r_scop_ch P P':
    (forall (L : seq atom) k, k \notin L -> (open P k) --> (open P' k)) ->
    nu_ch P --> nu_ch P'

| r_par P P' Q:
    lc Q ->
    P --> P' ->
    par P Q --> par P' Q

| r_sel_l k P Pl Pr:
    lc P -> lc Pl -> lc Pr ->
    par (select k left P) (branch k Pl Pr) --> par P Pl

| r_sel_r k P Pl Pr:
    lc P -> lc Pl -> lc Pr ->
    par (select k right P) (branch k Pl Pr) --> par P Pr

(* for now I will add these rules *)

| r_done P: P --> P
| r_tran P Q R: P --> Q -> Q --> R -> P --> R

where "P --> Q" := (red P Q).
