From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import FinMap.finmap.
Require Import FinMap.ordtype.

Require Import SendRec.Atom.
Require Import SendRec.SyntaxO.
Require Import SendRec.Env.

Require Import SendRec.OddsAndEnds.

Definition sort_env := @env atom_ordType sort_eqType.
Definition tp_env := @env atom_ordType tp_eqType.

(* Properties of typings *)

(* lift dual to option *)
Definition option_dual (d : option tp) : option tp :=
  match d with
  | None => None
  | Some T => Some (dual T)
  end.

Inductive compatible : forall (E1 E2 : tp_env), Prop :=
| compatible_disj E1 E2: disjoint E1 E2 -> compatible E1 E2
| compatible_add E1 E2 k t: compatible E1 E2 -> compatible (add k t E1) (add k (dual t) E2)
.
Hint Constructors compatible.

Definition compatible_nil : compatible nil nil.
  apply compatible_disj.
  apply disjoint_nil.
Defined.

Lemma compatibleC E1 E2 : compatible E1 E2 -> compatible E2 E1.
  elim=>//.
  move=> E0 E3.
  rewrite disjointC.
  apply compatible_disj.
  move=> E0 E3 k t D. (* D1 D2. *)
  move/compatible_add.
  move=>H.
  have H':= H k (dual t).
  move:H'.
  by rewrite dual_is_dual.
Qed.

Definition compose (E1 E2 : tp_env) : tp_env :=
  if (E1, E2) is (Def f1, Def f2) then
    let: (f1, f12, f2) := spl f1 f2 in
    Def (fcat f1 (fcat (fmap_map (fun _ => bot) f12) f2))
  else
    undef_env.

Notation "A 'o' B" := (compose A B) (at level 60, right associativity).  (* : env_scope. *)

Lemma compose_undef D:
  D o undef_env = undef_env.
Proof.
  elim D=>//.
Qed.

Lemma composeC D D': D o D' = D' o D.
Proof.
  elim D=>// ; elim D'=>// f f'.
  (* DISJOINTNESSS *)
  have: all_disj (spl f f') by apply: disj_spl.
  move=>/andP-[/andP-[di dd] id].
  have dmi :
    disj (diff f' f) (fmap_map (fun _ : tp_eqType => bot) (intersect f f'))
    by rewrite /disj supp_map -/(disj _ _) disjC.
  have mid :
    disj (fmap_map (fun _ : tp_eqType => bot) (intersect f f')) (diff f f')
    by rewrite /disj supp_map -/(disj _ _) disjC.
  have dmid :
    disj (fcat (diff f' f)
               (fmap_map (fun _ : tp_eqType => bot) (intersect f f')))
         (diff f f')
    by rewrite disjC disj_fcat dd Bool.andb_true_l /disj supp_map.
  have eq_supp :
    supp (intersect f' f) == supp (intersect f f')
    by rewrite (supp_intersect f' f).
  (* END DISJOINTNESSS *)
  rewrite /compose/spl.
  rewrite (fmap_const_eq bot eq_supp).
    by rewrite -fcatA // fcatC // [fcat (diff f' f) _]fcatC.
Qed.

(* some properties of compatible environments and of defined envirnments *)
Lemma compatible_hd k t t' E1 E2:
  def (add k t E1) -> def (add k t' E2) -> t == dual t'
  -> compatible E1 E2 -> compatible (add k t E1) (add k t' E2).
Proof.
  elim: E1; elim: E2 => // => f f0.
  move=>D1 D2.
  move/eqP=>R. rewrite R.
  move/compatible_add.
  move=>H.
  have H':= H k (dual t'). move:H'.
  by rewrite dual_is_dual.
Qed.

Lemma compatible_swap_left k k' s t E1 E2:
  def (add k t (add k' s E1)) -> def E2 -> (* we may not need/want these*)
  compatible (add k t (add k' s E1)) E2 ->
  compatible (add k' s (add k t E1)) E2.
Proof. by rewrite add_swap. Qed.

Module Env_examples.
  Parameter k k' : atom.

  Definition tpsend := input boole bot.
  Definition tprecv := dual tpsend.
  Definition tpin := ch_input tpsend bot.
  Definition tpout := dual tpin.

  Definition E1 := add k tpout (add k' tpsend nil).
  Axiom def_E1 : def E1.
  Definition E2 := add k tpin (add k' tprecv nil).
  Axiom def_E2 : def E2.
  Definition E3 := add k' tprecv (add k tpin nil).
  Axiom def_E3 : def E3.

  Goal compatible E1 E2.
    rewrite/E1/E2.
    apply: compatible_hd.
    - exact: def_E1.
    - exact: def_E2.
    - by [].
    - apply: compatible_hd.
      + apply: def_nested.
        by apply def_E1.
      + apply: def_nested.
        by apply def_E2.
      + by [].
      + by apply compatible_nil.
  Qed.

  Goal compatible E1 E3.
    rewrite/E1/E3.
    apply: compatible_swap_left.
    - rewrite add_swap.
      apply: def_E1.
    - apply: def_E3.
    - apply: compatible_hd.
      + rewrite add_swap.
      + apply: def_E1.
      + apply: def_E3.
      + by [].

    + apply: compatible_hd.
      * apply: def_nested.
        rewrite add_swap.
        move:def_E1.
        apply.
      * apply: def_nested.
        rewrite add_swap.
        by apply def_E2.
      * by [].
      * by apply compatible_nil.
  Qed.
End Env_examples.

Definition completed (D : tp_env) : Prop := forall a, a \in dom D -> binds a ended D.

Theorem completed_nil : completed nil.
Proof.
    by [].
Qed.

Theorem completed_top : forall a D,
    completed D -> def (add a ended D) ->
    completed (add a ended D).
Proof.
  move=>a D H Hdef. move: H.
  rewrite/completed => H1 a' H2.
  destruct (a == a') eqn: Haa'.
  {
    move:Haa' Hdef H2.
    move/eqP=>->.
    move=>Hdef H2.
    apply binds_top_add.
    apply Hdef.
  }
  {
    have H:= H1 a'.
    have H': binds a' ended D.
    {
      apply H.
      move:H2.
      rewrite/add/dom. simpl.
      move: Hdef.
      elim D=>// f Hdef.
      rewrite/look.

      move: Hdef.
      rewrite def_addb => /andP-[_ /negPf->].

      simpl.
      rewrite supp_ins.
      rewrite/predU.
      simpl.
      do 2!rewrite/(_\in_).
      simpl.
        by rewrite eq_sym Haa' Bool.orb_false_l.
    }
    move:H'.
    rewrite/binds.
    move/eqP=><-.

    apply look_add_deep.
    move: Haa'.
    by rewrite/(_!=_)=>->.
    by apply Hdef.
  }
Qed. (* TODO: why is this soo long? *)

Lemma completed_singleton k : completed (add k ended nil).
Proof.
    by apply completed_top.
Qed.

(* misc lemmas *)

Lemma add_in_dom_undef k T (E : tp_env): k \in dom E -> add k T E = undef_env.
Proof.
    by case: E =>// f; rewrite /add/look =>->.
Qed.

Lemma add_undef_in_dom K (V : eqType) k T (f : finMap K V) :
  add k T (Def f) = undef_env -> k \in supp f.
Proof. by rewrite /add /look; case: suppP =>// ->. Qed.

Lemma compose_add_undef k T T' D D':
  add k T D == undef_env -> add k T' (D o D') = undef_env.
Proof.
  case: D; case: D' => // f f' /eqP/add_undef_in_dom-k_in_f'.
  have dd :
    disj (fmap_map (fun _ : tp => bot) (intersect f' f)) (diff f f')
    by rewrite /disj supp_map supp_intersect -/(disj _ _)
               disjC disj_diff_intersect.
  rewrite /compose/spl/=; apply add_in_dom_undef; rewrite -fcatA // /dom.
  rewrite supp_fcat; apply in_predU_l; rewrite supp_fcat supp_map !supp_fbk.
    by rewrite [k \in _]/in_mem /= !mem_filter k_in_f'; case: (k \in supp f).
Qed.

Lemma compose_top k T T' D D':
  (add k T D) o (add k T' D') = add k bot (D o D').
Proof.
  case: D => // f; case: D' => [| f']; first by rewrite !compose_undef.
  case: (suppP k f) => [v /eqP/in_supp_fnd|/eqP/notin_supp_fnd/negPf] fnd_k_f;
                         first by rewrite (@compose_add_undef k T) // add_in_dom_undef //.
  case: (suppP k f') => [v /eqP/in_supp_fnd|/eqP/notin_supp_fnd/negPf] fnd_k_f';
                          first by rewrite [in RHS]composeC [in LHS]composeC
                                           (@compose_add_undef k T') // add_in_dom_undef //.
  rewrite /add /= fnd_k_f fnd_k_f' !supp_fcat !inE !supp_fcat !inE supp_map
          !in_supp_diff !in_supp_isect fnd_k_f fnd_k_f' /= /compose/=; congr Def.
  move: fnd_k_f fnd_k_f' => /(rwP negPf)/fnd_supp-fnd_k_f /(rwP negPf)/fnd_supp-fnd_k_f'.
  rewrite !diff_ins ?intersect_ins ?fmap_map_ins ?fcat_inss ?fcat_sins //;
          apply: notin_supp_fnd; apply/eqP => //.
    by rewrite fnd_diff fnd_k_f.
Qed.

Lemma compose_nil : nil o nil == nil.
    by [].
Qed.


Inductive oft_exp (G : sort_env) : exp -> sort -> Prop :=
| t_tt : oft_exp G tt boole
| t_ff : oft_exp G ff boole
| t_var : forall x (S : sort),
    binds x S G ->
    oft_exp G (var (fnm x)) S
.

Inductive oft : sort_env -> proc -> tp_env -> Prop :=
| t_request : forall (L : seq atom) G a P D T t,
    binds a (end_points T t) G ->
    (forall k, k \notin L ->
    oft G (open P k) (add k t D)) ->
    oft G (request a P) D

| t_accept : forall (L : seq atom) G a P D T t,
    binds a (end_points T t) G ->
    (forall k, k \notin L ->
    oft G (open P k) (add k T D)) ->
    oft G (accept a P) D

| t_send : forall G k e P D S T,
    oft_exp G e S ->
    oft G P (add k T D) ->
    oft G (send k e P) (add k (output S T) D)

| t_receive : forall (L : seq atom) G k P D S T,
    (forall x, x \notin L ->
          oft (add x S G) P (add k T D)) ->
    oft G (receive k P) (add k (input S T) D)

| t_select_l : forall G k P D T T',
    oft G P (add k T D) ->
    oft G (select k left P) (add k (take_branch T T') D)

| t_select_r : forall G k P D T T',
    oft G P (add k T' D) ->
    oft G (select k right P) (add k (take_branch T T') D)

| t_branch : forall G k P Q D T T',
    oft G P (add k T D) ->
    oft G Q (add k T' D) ->
    oft G (branch k P Q) (add k (offer_branch T T') D)

| t_throw : forall G (k k' : atom) P D T T',
    oft G P (add k T' D) ->
    oft G (throw k k' P) (add k (ch_output T T') (add k' T D))

| t_catch : forall (L : seq atom) G k P D T T',
    (forall k',
        k' \notin L ->
        oft G (open P k') (add k' T (add k T' D))) ->
    oft G (catch k P) (add k (ch_input T T') D)

| t_ife : forall G e P Q D,
    oft_exp G e boole ->
    oft G P D ->
    oft G Q D ->
    oft G (ife e P Q) D

| t_par : forall G P Q D1 D2,
    oft G P D1 ->
    oft G Q D2 ->
    compatible D1 D2 ->
    oft G (par P Q) (D1 o D2)

| t_inact : forall G D,
    completed D ->
    oft G inact D

| t_nu_nm : forall (L : seq atom) G s P D, (* one needs to choose the right sort *)
    (forall x, x \notin L ->
    oft (add x s G) (open P x) D) ->
    oft G (nu_nm P) D

| t_nu_ch : forall (L : seq atom) G P D,
    (forall x, x \notin L ->
    oft G (open P x) (add x bot D)) ->
    oft G (nu_ch P) D

| t_bot G k D : (* this should be P not inact but it is easier this way *)
    oft G inact (add k ended D) ->
    oft G inact (add k bot D)

| t_bang G P D:
    completed D ->
    oft G P nil -> oft G (bang P) D
.

Section CounterExample.
  Parameter k k' : atom.
  Parameter Hdiff : k != k'.
  Parameter P Q : proc.

  Definition counter :=
    par (throw k k' inact) (catch k (receive 0 (send k' tt inact))).

  Definition reduced := receive k' (send k' tt inact).

  (* Definition tpsend := input boole bot. *)
  Definition tpsend := input boole ended.

  Definition tprecv := dual tpsend.

  (* Definition tpin := ch_input tpsend bot. *)
  Definition tpin := ch_input tpsend ended.
  Definition tpout := dual tpin.

  Goal lc counter.
    apply lc_par ;
      [apply lc_throw ;
       [apply lc_name | apply lc_name | apply lc_inact]
      | idtac].

    - {apply: lc_catch=>//.
       move=>k'' Hk''. rewrite/open;simpl.
       {apply: lc_receive=>//.
        move=>y Hy. rewrite/open;simpl.
        {apply: lc_send =>//.
         }}}
      Unshelve.
      exact [::].
      exact [::].
  Qed.


  Definition D1 := add k tpout (add k' tpsend  nil).
  Definition D2 := add k tpin (add k' tprecv  nil).
  Definition D := D1 o D2. (* add k bot (add k' bot nil). *)

  Lemma defD : def D.
  Proof.
    rewrite/D!compose_top.

    apply def_add ; split ; last by [].
    {
      have H: def(add k' bot nil) by [].
      apply add_in_dom in H.
      rewrite dom_add' ; last by [].
      rewrite dom_add' in H ; last by [].
      simpl. rewrite/supp/finmap.nil. simpl.
      rewrite/(_\notin_)/(_\in_).
      simpl.
      rewrite Bool.orb_false_r.
      by apply Hdiff.
    }
  Qed.

  Lemma defD' : def (add k' bot (add k bot nil)).
  Proof.
    rewrite add_swap.
    move: defD.
    rewrite/D!compose_top.
    by move:compose_nil=>/eqP=>->.
  Qed.

  Lemma dom_nil : dom (nil : tp_env) = [::].
    by [].
  Qed.

  Lemma compatibleD1D2 : compatible D1 D2.
    do !apply compatible_add ; apply: compatible_nil.
  Qed.

  Goal oft nil counter D.
    rewrite/counter/D.
    apply: t_par.
    - apply: t_throw.
      + by apply: t_inact ; apply: completed_singleton.

    - rewrite/D2.
      apply t_catch with (L := dom (add k ended (add k' ended nil))) => k'' Hk''.
      rewrite/open=>/=.
      apply: t_receive=> x Hx.
      rewrite [add k ended (add k' tprecv nil)] add_swap.
      rewrite [add k'' ended (add k' tprecv _)] add_swap.
      apply t_send.

      + by apply t_tt.

      + apply: t_inact.
        do!apply: completed_top.
        apply completed_nil.
        by apply singleton_def.

        apply def_add.
        split ; last apply singleton_def.
        apply: notin_dom_def ; first by [].
        move: Hk'' ; rewrite notin_add.
        by move/andP; case.
        apply def_add.
        split ; last by apply: singleton_def.
        rewrite notin_add //.
        by rewrite Hdiff Bool.andb_true_l.
        by apply: singleton_def.

        have:def (add k'' ended (add k ended nil)).
        {
          move: Hk''. rewrite add_swap notin_add.
          move/andP. case => hdiff'' hnotin''.
          apply def_add.
          split ; [ easy | apply singleton_def].
          apply def_add.
          split.
          rewrite notin_add/=; last easy.
          rewrite Bool.andb_true_r.
          by apply neqC; apply Hdiff.
          by apply singleton_def.
        }
        move=>Hdef.
        apply def_add.
        split ; last easy.
        rewrite !notin_add/=; try easy.
        have: k' != k''.
        {
          apply neqC.
          move: Hk''. rewrite add_swap notin_add.
          by move/andP ; case.
          apply def_add.
          split ; last by apply singleton_def.
          rewrite notin_add/= ; last easy.
          rewrite Bool.andb_true_r.
          by apply neqC; apply Hdiff.
        }
        have: k' != k by apply neqC ; rewrite Hdiff.
        by move=>->=>->.

        by apply compatibleD1D2.
        Unshelve.
        exact [::].
  Qed.

  Goal (counter --> reduced).
    rewrite/counter/reduced.
    apply: r_tran.
    apply: r_pass.
    by constructor.
    rewrite/body/open=>//.
    move=> L x Hx.
    apply: lc_receive.
    by [].
    move=> y Hy.
    rewrite/body/open=>//.
    apply: lc_send=>//.
    rewrite/open;simpl.
    apply: r_tran.
    apply: r_cong.
    repeat constructor.
    apply: lc_receive =>//.
    move=> z Hz.
    rewrite/body/open=>//.
    apply: lc_send=>//.
    2:{
      apply: c_inact.
    }
    2:{
      apply: r_done.
    }
    2:{
      apply: c_refl.
    }

    apply: lc_receive=>//.
    move=> x Hx.
    rewrite/body/open=>//.
    apply: lc_send=>//.
    apply: r_done.
    Unshelve. (* for all the Ls we did not constrain *)
    exact [::]. exact [::]. exact [::].
  Qed.

  Goal oft nil reduced D.
    rewrite/reduced/D/D1/D2.
    (* apply: t_receive.
       it fails k' cannot be bot and input *)
  Abort.

  (* Here we reason by inversion until we can show that bot and input
     cannot be equal and we show the contradiction *)
  Lemma oft_reduced : ~ oft nil reduced D.
    rewrite/reduced/D.
    move=>H.
    inversion H; subst.
    move:H. rewrite/D1/D2=>H.
    inversion H ; subst.
    move:H6.
    rewrite !compose_top add_swap.
    move/eqP=>Heq.
    apply eq_hd in Heq.
    congruence.
    move:Heq. move/eqP=>->.
    move:compose_nil. move/eqP=>->.
    apply defD'.
  Qed.

End CounterExample.
