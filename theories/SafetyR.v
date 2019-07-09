From mathcomp.ssreflect Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FinMap.finmap.
Require Import FinMap.ordtype.

Require Import SendRec.OddsAndEnds.
Require Import SendRec.AtomScopes.
Require Import SendRec.SyntaxR.
Require Import SendRec.Env.
Require Import SendRec.TypesR.

Definition balanced (D : tp_env) :=
  def D /\
  forall k T T' p pd,
    p == dual_pol pd ->
    binds (ke (k, p)) T D ->
    binds (ke (k, pd)) T' D ->
    T == dual T'.

Lemma balanced_def (D : tp_env) : balanced D -> def D.
Proof.
  rewrite/balanced. intuition.
Qed.

(* this lemma is a target for an indom but with binds *)
Lemma add_balanced k p pd T T' D:
  p == dual_pol pd ->
  balanced (add (ke (k, p)) T (add (ke (k, pd)) T' D)) -> T == dual T'.
Proof.
  move=>Hd Hb.
  (* have Hdef : def (add (ce (k, p)) T (add (ce (k, pd)) T' D)) by apply: balanced_def. *)
  move: Hb.
  rewrite/balanced.
  case.
  move=> Hdef H.
  apply: H.
  apply: Hd.
  apply: binds_top_add.
  assumption.
  apply: add_binds=>//.
  apply:binds_top_add.
  by apply def_nested in Hdef.
  rewrite/(_!=_)/ce.

  have Hd' : p != pd by apply: pol_dual_noteq.
  by rewrite -[ke _ == ke _]/((k, pd) == (k, p))
             xpair_eqE eq_refl eq_sym (negPf Hd').
Qed.

(* FIXME: refactor below *)
Lemma balanced_add k p pd T T' D :
  balanced (add (ke (k, p)) T (add (ke (k, pd)) T' D)) ->
  (p = dual_pol pd) /\ (T = dual T') /\ balanced D.
Proof.
  move => [Hdef Hbal].
  move: (def_nested Hdef) => Hdef'; move: (def_nested Hdef') => Hdef''.
  have pDual: p == dual_pol pd.
  - move: Hdef; rewrite !def_add dom_add // !inE negb_or=> [][/andP-[]].
    rewrite -[ke _ == _]/((k,p) == (k, pd)) xpair_eqE negb_and eq_refl /=.
    by case: p Hbal; case: pd Hdef'.
  move: (Hbal k T T' p pd pDual).
  rewrite /binds look_add// eq_refl add_swap look_add//; last by rewrite add_swap.
  move: pDual; rewrite eq_refl => /eqP-> /(_ is_true_true)/(_ is_true_true)/eqP->.
  do ! split =>//.
  move=> k' T0 T'0 p0 pd0 pdual Hbinds1 Hbinds2.
  have neq: k' != k.
  - move: Hdef Hbinds1; rewrite !def_add dom_add// !inE negb_or.
    move=>[/andP-[neq Ni1] [Ni2 _]]; move: Ni1 Ni2; rewrite /binds.
    case: in_domP =>///look_not_some-Hlook1 _.
    case: in_domP =>///look_not_some-Hlook2 _ Hlook3.
    apply: contraT; rewrite negbK=>/eqP-eq; move: eq Hlook1 Hlook2 Hlook3=>->.
    move: neq; rewrite -[ke _ == _]/((k,p)==(k,pd)) xpair_eqE negb_and eq_refl/=.
    case: p Hbal=> _ Neq Rw1; case: p0 pdual Neq=> _; rewrite ?Rw1//.
    case: pd Hdef'=> _ // _ Rw2; rewrite ?Rw2//.
    case: pd Hdef'=> _ // _ Rw2; rewrite ?Rw2//.
  apply: (Hbal k' _ _ _ _ pdual).
  rewrite /binds !look_addb.
  rewrite -[ke _ == _]/((k',p0) == (k,p)) xpair_eqE (negPf neq) /= Hdef Hdef'.
  rewrite -[ke _ == _]/((k',p0) == (k,pd)) xpair_eqE (negPf neq) /=.
  apply: Hbinds1.
  rewrite /binds !look_addb.
  rewrite -[ke _ == _]/((k',pd0) == (k,p)) xpair_eqE (negPf neq) /= Hdef Hdef'.
  rewrite -[ke _ == _]/((k',pd0) == (k,pd)) xpair_eqE (negPf neq) /=.
  apply: Hbinds2.
Qed.

Lemma balanced_next k p pd T T' D :
  balanced (add (ke (k, p)) T (add (ke (k, pd)) T' D)) ->
  balanced D.
Proof. by move=> /balanced_add => [][] _ [] _ . Qed.

Lemma pol_noteq_dual p pd : p != pd -> p = dual_pol pd.
Proof. by case: p; case: pd. Qed.


Lemma dualK T : dual (dual T) = T.
Proof.
  elim: T=>//=.
  + by move=> s t IH; rewrite IH.
  + by move=> s t IH; rewrite IH.
  + by move=> t _ t0 IH; rewrite IH.
  + by move=> t _ t0 IH; rewrite IH.
  + by move=> t IH1 t0 IH2; rewrite IH1 IH2.
  + by move=> t IH1 t0 IH2; rewrite IH1 IH2.
Qed.

Lemma add_dual_bal k p T D :
  def (add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D)) ->
  balanced D ->
  balanced (add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D)).
Proof.
  move=> Hdef; rewrite /balanced => [][] _ Hbal; split => // k0 T0 T0' p0 pd.
  case: (boolP (k0 == k)) => [/eqP-> {k0} /eqP->{p0}|].
  + case: (boolP (pd == p)) =>[/eqP->|].
    - move=> /(binds_next _).
      rewrite -[ke _ == _]/((k, dual_pol p) == (k, p)) xpair_eqE negb_and eq_refl.
      rewrite (pol_dual_noteq (eq_refl _)) =>/= /(_ is_true_true).
      move: (def_addG (def_nested Hdef)) => Hdef'.
      move => /(binds_top_addE (Hdef' T0))->.
      by move => /(binds_top_addE (def_addG Hdef T0'))->.
    - move =>/pol_noteq_dual->; rewrite dual_polK.
      move=>/(binds_top_addE (def_addG Hdef T0))<-.
      move=>/(binds_next _).
      rewrite ke_eqE negb_and eq_refl (pol_dual_noteq (eq_refl _)).
      move=>/(_ is_true_true)/(binds_top_addE (def_addG (def_nested Hdef) _))->.
      by rewrite dualK.
  + move=> keq /eqP->.
    do 2 (move=>/(binds_next _); rewrite ke_eqE negb_and keq =>/(_ is_true_true)).
    move=>/(Hbal _ _ _ _ _ (eq_refl _))-{Hbal}Hbal.
    do 2 (move=>/(binds_next _); rewrite ke_eqE negb_and keq =>/(_ is_true_true)).
    by move=>/(Hbal _)-{Hbal}Hbal.
Qed.

CoInductive rlbl :=
| lch of CN.atom
| lsel of CN.atom * label
| none
.

Ltac eval_open_k := rewrite !/open_k0 /= -!/(open_k0 _ _).

Lemma ke_inj x y : (ke x == ke y) = (x == y).
Proof. by rewrite -[ke _ == _]/(x == y). Qed.

Lemma ke_posneg_neq x y : (ke (x, Pos) == ke (y, Neg)) = false.
Proof. by rewrite ke_inj xpair_eqE andbC. Qed.

(* ad-hoc tactic to avoid repetition *)
Ltac in_out p p0 pd pd0 d0 k0k Eq DD D_p_pd :=
  let pd0 := fresh in
  let t := fresh in
  let f := fresh in
  let ppd := fresh in
  let p0p := fresh in
  let neq := fresh in
  let d0pd := fresh in
  move: k0k Eq =>-> Eq _;
  (have: p0 <> d0
    by move=>pd0;move:pd0 Eq DD=>-><-/def_add-[f /add_in_dom-t];move:t f =>->);
  (have : p0 = p by
     move: Eq; case: (boolP (p0 == p)) => [/eqP|]-ppd; first (by rewrite ppd);
      (have: p0 = pd by move: DD D_p_pd ppd => _ /eqP->; case: p0; case: p);
      move=>->; rewrite [in RHS](add_swap);
      move: DD; rewrite [in def _](add_swap) => DD;
        by move => /eqP; rewrite eq_sym; move=>/eqP/(def_add_cancel DD) []
    );
  move=>p0p; move: p0p Eq=>-> Eq neq;
  (have d0pd: d0 = pd
    by move: D_p_pd neq; case: p Eq DD =>_ _ /eqP->/eqP; case: pd; case: d0);
  move: d0pd Eq=>-> /eqP; rewrite eq_sym=>/eqP.

Lemma na_free_inj a a' : SC.Free a = SC.Free a' -> a = a'.
Proof. by move=>/eqP; rewrite -[SC.Free _ == _]/(a == a') => /eqP. Qed.

Lemma balanced_union D1 D2 : balanced (D1 \:/ D2) -> balanced D1 /\ balanced D2.
Proof.
  rewrite unionC /balanced => [][Def]; move: (union_def Def) => [Def1 Def2].
  rewrite Def1 Def2 /binds => H.
  do ! split=>//.
  + move=> k T T' p pd dpd pD1 pdD1.
    apply: (H k T T' p pd dpd).
    - rewrite look_union Def; move: pD1; case: domP=>[v|]->//.
      rewrite look_union Def; move: pdD1; case: domP=>[v|]->//.
  + move=> k T T' p pd dpd pD pdD.
    move: Def; rewrite unionC=>Def.
    apply: (H k T T' p pd dpd).
    - rewrite unionC look_union Def; move: pD; case: domP=>[v|]->//.
    - rewrite unionC look_union Def; move: pdD; case: domP=>[v|]->//.
Qed.

Lemma infv_indom_k G P D :
  oft G P D -> forall k, k \in freev_k P -> k \in ch_dom D.
Proof.
  move=> Hoft; move: (oft_def Hoft) => Def; move: Hoft Def.
  induction_oft=> Def k; rewrite ?mem_cat // => H.
  + move: (LC.fresh _) (LC.fresh_not_in (va_dom D ++ L)) => x.
    rewrite !mem_cat !negb_or => /andP-[/notin_vadom_dom-x_D x_L].
    move: (def_add_assumption (dual t) x_D Def) => Def_xD.
    move: Ih => /(_ (ce x) x_L Def_xD k).
    rewrite freek_openc // => /(_ H)/in_chdom_dom-[p].
    by rewrite in_add ///= => /in_dom_chdom.
  + move: (LC.fresh _) (LC.fresh_not_in (va_dom D ++ L)) => x.
    rewrite !mem_cat !negb_or => /andP-[/notin_vadom_dom-x_D x_L].
    move: (def_add_assumption t x_D Def) => Def_xD.
    move: Ih => /(_ (ce x) x_L Def_xD k).
    rewrite freek_openc // => /(_ H)/in_chdom_dom-[p].
    by rewrite in_add ///= => /in_dom_chdom.
  + move: H=>/orP-[].
    - case: kt OftP Ih Def =>//[][ka kp] OftP Ih Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP Ih Def => <-{ka} OftP Ih Def.
      by apply/(in_dom_chdom (p:=kp)); rewrite in_add // eq_refl.
    - move: (def_diff_value T Def) => /Ih-{Ih}/(_ k)-Ih.
      move=>/Ih=>{Ih}/in_chdom_dom-[p] Ih.
      by apply/(in_dom_chdom (p:=p)); rewrite -(dom_diff_eq kt T).
  + move: H=>/orP-[].
    - case: kt OftP Ih Def =>//[][ka kp] OftP Ih Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP Ih Def => <-{ka} OftP Ih Def.
      by apply/(in_dom_chdom (p:=kp)); rewrite in_add // eq_refl.
    - move: (def_diff_value T Def)
              =>/Ih-{Ih}/(_ (EV.fresh _) (EV.fresh_not_in _) k).
      rewrite freek_opene => Ih /Ih{Ih}/in_chdom_dom-[p] Ih.
      by apply/(in_dom_chdom (p:=p)); rewrite -(dom_diff_eq kt T).
  + move: H=>/orP-[].
    - case: k0 OftP Ih Def =>//[][ka kp] OftP Ih Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP Ih Def => <-{ka} OftP Ih Def.
      by apply/(in_dom_chdom (p:=kp)); rewrite in_add // eq_refl.
    - move: (def_diff_value T Def)
              =>/Ih-{Ih}/(_ k)-Ih/Ih/in_chdom_dom-[p] {Ih}Ih.
      by apply/(in_dom_chdom (p:=p)); rewrite -(dom_diff_eq k0 T).
  + move: H=>/orP-[].
    - case: k0 OftP Ih Def =>//[][ka kp] OftP Ih Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP Ih Def => <-{ka} OftP Ih Def.
      by apply/(in_dom_chdom (p:=kp)); rewrite in_add // eq_refl.
    - move: (def_diff_value T' Def)
              =>/Ih-{Ih}/(_ k)-Ih/Ih/in_chdom_dom-[p] {Ih}Ih.
      by apply/(in_dom_chdom (p:=p)); rewrite -(dom_diff_eq k0 T').
  + move: H=>/orP-[|/orP-[|]].
    - case: k0 OftP IhP OftQ IhQ Def =>//[][ka kp] OftP IhP OftQ IhQ Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP IhP OftQ IhQ Def => <-{ka} OftP IhP OftQ IhQ Def.
      by apply/(in_dom_chdom (p:=kp)); rewrite in_add // eq_refl.
    - move=>/(IhP (def_diff_value T Def) k)-{IhP}/in_chdom_dom-[p] IhP.
      by apply/(in_dom_chdom (p:=p)); rewrite -(dom_diff_eq k0 T).
    - move=>/(IhQ (def_diff_value T' Def) k)-{IhQ}/in_chdom_dom-[p] IhQ.
      by apply/(in_dom_chdom (p:=p)); rewrite -(dom_diff_eq k0 T').
  + move: H=>/orP-[|/orP-[|]] {Def_kk'D}.
    - case: k0 OftP Ih Def =>//[][ka kp] OftP Ih Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP Ih Def => <-{ka} OftP Ih Def.
      by apply/(in_dom_chdom (p:=kp)); rewrite in_add // eq_refl.
    - case: k1 OftP Ih Def =>//[][ka kp] OftP Ih Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP Ih Def => <-{ka} OftP Ih Def.
      move: Def; rewrite def_addb =>/andP-[Def1 Def2].
      by apply/(in_dom_chdom (p:=kp));rewrite in_addb orbC Def2 in_add// eq_refl.
    - have Def' : def (add k0 T' D) by
          move: Def; rewrite add_swap => /def_nested/(def_diff_value T').
      move=>/(Ih Def')/in_chdom_dom-[p] {Ih}Ih.
      apply/(in_dom_chdom (p:=p)); move: Def; rewrite def_addb =>/andP-[Def0 Def1].
      rewrite in_addb Def1/= Def0 /=; rewrite !in_addb (def_nested Def0)/=.
      move: Def1; rewrite in_addb negb_and negb_or negb_and.
      move: Def0; rewrite def_addb (def_nested Def')=>/andP-[_->]/=/andP-[H0 H1].
      move: Ih; rewrite in_addb H1 (def_nested Def') /= =>/orP-[|]->//.
      by rewrite !Bool.orb_true_r.
  + move: H=>/orP-[|].
    - case: k0 OftP Ih Def =>//[][ka kp] OftP Ih Def /=.
      rewrite in_cons orbC /= => /eqP-Eq.
      move: Eq OftP Ih Def => <-{ka} OftP Ih Def.
      by apply/(in_dom_chdom (p:=kp)); rewrite in_add // eq_refl.
    - move: (LC.fresh _) (LC.fresh_not_in (va_dom D ++ L)) => x.
      rewrite !mem_cat !negb_or => /andP-[/notin_vadom_dom-x_D x_L].
      move: (oft_def (OftP (ce x) x_L)) => Def'.
      have k_x: k \notin fv_k x by [].
      move: (Ih (ce x) x_L Def' k)=> /=.
      rewrite freek_openc // =>{Ih}Ih/Ih{Ih}/in_chdom_dom-[p] Ih.
      apply/(in_dom_chdom (p:=p)); move: Ih.
      rewrite in_addb -[ke _ == ce _]/(false)/=.
      by move: Def'; rewrite def_addb =>/andP-[->->]/=; rewrite !in_addb.
  + move: H=>/orP-[|]H.
    - by apply: IhP.
    - by apply: IhQ.
  + move: H=>/orP-[|].
    - move=>/(IhP (proj1 (union_def Def)) k)-{IhP}/in_chdom_dom-[p] IhP.
      by apply/(in_dom_chdom (p:=p)); rewrite dom_union Def IhP.
    - move=>/(IhQ (proj2 (union_def Def)) k)-{IhQ}/in_chdom_dom-[p] IhQ.
      by apply/(in_dom_chdom (p:=p)); rewrite dom_union Def IhQ orbC.
  + move: (Ih (SC.fresh _) (SC.fresh_not_in _) Def k).
    by rewrite freek_openn =>{Ih}/(_ H)Ih.
  + move: (CN.fresh _) (CN.fresh_not_in (k::L))=> ki.
    rewrite in_cons negb_or=>/andP-[kik ki_L].
    move: (oft_def (OftP ki ki_L)) => Def'; move: (Ih ki ki_L Def' k).
    rewrite freek_openk // =>/(_ H)-{Ih}/in_chdom_dom-[p].
    move: Def'; rewrite def_addb=>/andP-[H1 H2].
    rewrite in_addb H2 H1 /= ke_eqE eq_sym (negPf kik)/=.
    move: H1; rewrite def_addb=>/andP-[H1 {H2}H2].
    rewrite in_addb H2 H1 /= ke_eqE eq_sym (negPf kik)/= => Ih.
    by apply/(in_dom_chdom (p:=p)).
  + by apply: Ih.
  (* + by apply: Ih. *)
  + have: k\in ch_dom nil.
    by apply: Ih.
    move/in_chdom_dom=>[].
    easy.
Qed.

Definition comm (l : label) (t : tp) : tp :=
  match t with
  | input _ T => T
  | output _ T => T
  | ch_input _ T => T
  | ch_output _ T => T
  | offer_branch Tl Tr =>
    match l with
    | left => Tl
    | right => Tr
    end
  | take_branch Tl Tr =>
    match l with
    | left => Tl
    | right => Tr
    end
  | ended => t
  end.

Lemma dual_comm l T : dual (comm l T) = comm l (dual T).
Proof. by case: T=>//T T'; case: l. Qed.

Reserved Notation "D ~~> E" (at level 60).
Inductive typ_red : tp_env -> tp_env -> Prop :=
| tred_none D : D ~~> D
| tred_head l D k p T :
    add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D) ~~>
        add (ke (k, p)) (comm l T) (add (ke (k, dual_pol p)) (comm l (dual T)) D)
| tred_next D D' k p T :
    D ~~> D' ->
    add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D) ~~>
        add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D')
where "D ~~> E" := (typ_red D E).

Derive Inversion typred_inv with (forall D E, D ~~> E) Sort Prop.

Lemma typred_def D D' :
  D ~~> D' -> def D = def D' /\ forall k, (k \in dom D) = (k \in dom D').
Proof.
  elim=>{D}{D'}//.
  + move=>D k0 p T l; split; first by rewrite !def_addb !in_addb.
    move=> k.
    by do ! rewrite !in_addb !def_addb.
  + move=> D D' k0 p T DD' []-IhD Ih_k.
    do ! rewrite ?def_addb ?in_addb ?negb_and ?negb_or.
    do ! rewrite  !IhD !Ih_k; split=>//.
    move=> k; move: IhD; case: D DD' Ih_k; case: D' =>// f f' _.
    rewrite /dom => Ih _; rewrite /add/look/dom/upd.
    case: suppP=>[v /eqP/in_supp_fnd|/eqP/notin_supp_fnd];
                   first by rewrite Ih =>->/=.
    rewrite Ih => /negPf->; rewrite !supp_ins !inE ke_eqE eq_refl /=.
    rewrite (negPf (pol_dual_noteq _))/=; last by rewrite dual_polK.
    case: suppP=>[v /eqP/in_supp_fnd|/eqP/notin_supp_fnd];
                   first by rewrite Ih=>->.
    rewrite Ih => /negPf->.
    by do ! rewrite !supp_ins !inE; rewrite Ih.
Qed.

Lemma typred_bal D D' : D ~~> D' -> balanced D -> balanced D'.
Proof.
  elim=>{D}{D'}//.
  + move=> D k p T l Bal.
    move: (balanced_def Bal) (balanced_next Bal)=>{Bal}HDef Bal.
    move: (def_nested HDef) => Def'.
    rewrite -dual_comm; apply: add_dual_bal => //.
    by move: HDef; do ! rewrite ?def_addb ?in_addb ?negb_and ?negb_or.
  + move=> D D' k p T DD' Ih Bal.
    move: (balanced_def Bal) (balanced_next Bal)=>{Bal}HDef Bal.
    move: (typred_def DD') => [Def Dom].
    apply: add_dual_bal; first by
        move: HDef; do ! rewrite ?def_addb ?in_addb ?negb_and ?negb_or ?Def ?Dom.
    by apply: Ih.
Qed.

Lemma typred_undef D : undef_env ~~> D -> D = undef_env.
Proof. by move=>/typred_def-/=[]; case: D. Qed.

Lemma tred_step_add k p T D D' :
  balanced D ->
  add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D) ~~> D' ->
  exists T' D'',
    D' = add (ke (k, p)) T' (add (ke (k, dual_pol p)) (dual T') D'').
Proof.
  move => Bal; case: (boolP (def D'));
            last by case: D'=>// _ _; exists T, undef_env.
  move => defD' Hstep; move: (typred_def Hstep).
  rewrite defD' -/(is_true _)=>[][Def1 Hdom].
  move: Bal => /(add_dual_bal Def1)/(typred_bal Hstep)=>{Hstep}[][DefD' BD'].
  move: BD'; rewrite /binds=> BD'.
  move: (def_nested Def1) => Def2; move: (def_nested Def2) => Def3.
  have : (ke (k, p)) \in dom D'
    by move: (Hdom (ke (k, p))); rewrite in_add // eq_refl.
  have : (ke (k, dual_pol p)) \in dom D'
    by move: (Hdom (ke (k, dual_pol p)));
    rewrite in_add// ke_eqE eq_refl (negPf (dualpol_neql _))/= in_add// eq_refl.
  move=>/in_domP-[T2 /eqP-H1] /in_domP-[T1 /eqP-H2].
  move: (BD' k T1 T2 p (dual_pol p)) =>{BD'}.
  rewrite dual_polK eq_refl =>/(_ is_true_true H2 H1) => /eqP-T21.
  have {T21}T21: T2 = dual T1 by rewrite T21 dualK.
  move: T21 H1 H2 =>-> H1 H2{T2}{DefD'}{Def1}{Def2}{Def3}{D}{T}{Hdom}.
  exists T1, (rem (ke (k, p)) (rem (ke (k, dual_pol p)) D')).
  by rewrite -rem_add ?add_rem_id // ke_eqE eq_refl negb_and dualpol_neql.
Qed.

Lemma typred_dom D D' : D ~~> D' -> dom D' =i dom D.
Proof.
  elim=>//{D}{D'}.
  + by move=> l D k p T x; rewrite !in_addb !def_addb.
  + move=> D D' k p T DD' IH x.
    by rewrite !in_addb !def_addb !IH !(proj1 (typred_def DD')).
Qed.

(*
Ltac rw_impl :=
  match goal with
  | [ |- (is_true (?L || ?R)) -> _] => move=>/orP-[|]; rw_impl
  | [ |- (is_true (?L && ?R)) -> _] => move=>/andP-[]; rw_impl
  | [ |- is_true (?k == ?k) -> _ ] => move=> _; rw_impl
  | [ |- is_true (?k != ?k) -> _ ] => rewrite eq_refl
  | [ |- is_true (?k == dual_pol ?k) -> _ ] => rewrite (negPf (dualpol_neqr k)); rw_impl
  | [ |- is_true (dual_pol ?k == ?k) -> _ ] => rewrite (negPf (dualpol_neql k)); rw_impl
  | [ |- is_true (_ \notin _) -> _ ] => first [move=>->; rw_impl | move=>/negPf->; rw_impl | move=>_; rw_impl]
  | [ |- (is_true (~~ ?L)) -> _ ] => first[move=>->; rw_impl | move=>/negPf->; rw_impl|move=>_; rw_impl]
  | [ |- (?L = false) -> _ ] => first [move=>->|move=> _; rw_impl]
  | [ |- is_true (_ \in _) -> _ ] => first [move=>-> | move=>_]; rw_impl
  | [ |- _ ] => idtac
  end.
*)


Lemma tred_step_rem k p D D' :
  D ~~> D' ->
  rem (ke (k, p)) (rem (ke (k, dual_pol p)) D)
      ~~> (rem (ke (k, p)) (rem (ke (k, dual_pol p)) D')).
Proof.
  case: (boolP (def D));
    last by case: D=>/=// _ /typred_undef->/=; apply: tred_none.
  move=> Def Hstep; move: (proj1 (typred_def Hstep)); rewrite Def.
  move=>/eqP; rewrite eq_sym => /eqP; rewrite -/(is_true _) => Def'.
  elim: Hstep Def Def'.
  + by move=> D0 _ _; apply: tred_none.
  + move=> l D0 k0 p0 T Def1 Def2.
    have Def_p0: forall T, def (add (ke (k0, p0)) T D0) by
        move=> T0; move: Def1; rewrite add_swap=>/def_nested/def_diff_value.
    have Def_dp0: forall T, def (add (ke (k0, dual_pol p0)) T D0) by
        move=>T0; move: Def1=>/def_nested/def_diff_value.
    move: (def_nested (Def_p0 T)) Def2 => Def0 _.
    have {Def1}Def1: forall T T',
        def (add (ke (k0, p0)) T (add (ke (k0, dual_pol p0)) T' D0)).
      move=> T0 T'; rewrite def_addb Def_dp0 in_addb Def0 negb_and !negbK
                            ke_eqE eq_refl negb_or /= dualpol_neqr.
      by move: (Def_p0 T); rewrite def_addb orbC=>/andP-[_->].
    case: (boolP (k == k0)) => kk0.
    - move: kk0 Def1 Def_p0 Def_dp0; move=>/eqP<-{k0}; case: (boolP (p == p0)).
      * move=> /eqP<-{p0} Def1 Def2 Def3; rewrite rem_add; last by
            rewrite ke_eqE negb_and eq_refl dualpol_neqr.
        rewrite -!rem_add_id //.
        rewrite rem_add; last by
            rewrite ke_eqE negb_and eq_refl dualpol_neqr.
        by rewrite -!rem_add_id //; apply: tred_none.
      * move=> /pol_noteq_dual->; rewrite dual_polK => Def1 Def2 Def3.
        by rewrite -!rem_add_id //; apply: tred_none.
    - have neq : forall p1 p2, ke (k0, p1) != ke (k, p2) by
          move=>p1 p2; rewrite ke_eqE eq_sym negb_and kk0.
      rewrite !rem_add //.
      by apply: tred_head.
  + move=> {D}{D'} D D' k0 p0 T Hstep IH Def1 Def2.
    have: forall T, def (add (ke (k0, p0)) T D) by
        move=> T0; move: Def1; rewrite add_swap=>/def_nested/def_diff_value.
    have: forall T, def (add (ke (k0, dual_pol p0)) T D) by
        move=>T0; move: Def1=>/def_nested/def_diff_value.
    have: forall T, def (add (ke (k0, p0)) T D') by
        move=> T0; move: Def2; rewrite add_swap=>/def_nested/def_diff_value.
    have: forall T, def (add (ke (k0, dual_pol p0)) T D') by
        move=>T0; move: Def2=>/def_nested/def_diff_value.
    case: (boolP (k == k0)) => kk0.
    - move: kk0 Def1 Def2; move=>/eqP<-{k0}; case: (boolP (p == p0)).
      * move=> /eqP<-{p0} Def1 Def2; rewrite rem_add; last by
            rewrite ke_eqE negb_and eq_refl dualpol_neqr.
        move=> Def3 Def4 Def5 Def6; rewrite -!rem_add_id //.
        rewrite rem_add; last by
            rewrite ke_eqE negb_and eq_refl dualpol_neqr.
        by rewrite -!rem_add_id.
      * move=> /pol_noteq_dual->; rewrite dual_polK => Def1 Def2 Df3 Df4 Df5 Df6.
        by rewrite -!rem_add_id //.
    - have neq : forall p1 p2, ke (k0, p1) != ke (k, p2) by
          move=>p1 p2; rewrite ke_eqE eq_sym negb_and kk0.
      move=> Df1 Df2 Df3 Df4.
      rewrite !rem_add //; apply: tred_next; apply: IH.
      by apply: (def_nested (def_nested Def1)).
      by apply: (def_nested (def_nested Def2)).
Qed.


Lemma step_union_l D1 D1' D2 :
  D1 ~~> D1' -> (D1 \:/ D2) ~~> (D1' \:/ D2).
Proof.
  elim=>{D1} {D1'}.
  + by move=> D; apply: tred_none.
  + by move=> l D k p T; rewrite !add_union; apply: tred_head.
  + by move=> D D' k p T DD' IH; rewrite !add_union; apply: tred_next.
Qed.

Lemma tred_step_tail k p T T' D D' :
  def (add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D)) ->
  add (ke (k, p)) T (add (ke (k, dual_pol p)) (dual T) D)
      ~~> (add (ke (k, p)) T' (add (ke (k, dual_pol p)) (dual T') D')) ->
  D ~~> D'.
Proof.
  move=> Hdef Hstep.
  move: (typred_def Hstep) =>[]; rewrite Hdef =>/eqP; rewrite eq_sym=>/eqP.
  rewrite -/(is_true _) => Hdef' _ ; move: Hstep.
  move=>/(tred_step_rem k p).
  rewrite rem_add; last by
      rewrite ke_eqE negb_and eq_refl dualpol_neqr.
  have Df1: forall T, def (add (ke (k, p)) T D) by
        move=> T0; move: Hdef; rewrite add_swap=>/def_nested/def_diff_value.
  have Df2: forall T, def (add (ke (k, dual_pol p)) T D) by
        move=>T0; move: Hdef =>/def_nested/def_diff_value.
  have Df1': forall T, def (add (ke (k, p)) T D') by
        move=> T0; move: Hdef'; rewrite add_swap=>/def_nested/def_diff_value.
  have Df2': forall T, def (add (ke (k, dual_pol p)) T D') by
        move=>T0; move: Hdef' =>/def_nested/def_diff_value.
  rewrite -!rem_add_id //.
  rewrite rem_add; last by
      rewrite ke_eqE negb_and eq_refl dualpol_neqr.
  by rewrite -!rem_add_id.
Qed.

Theorem CongruencePreservesOft G P Q D :
  P === Q -> oft G P D -> oft G Q D.
Proof.
  elim=>{P}{Q}//.
  + move=> P /oft_par_inv []D1 []D2 []Hdef []<- []Oinact Oq.
    elim/oft_inv: Oinact =>// Oinact G0 D0 cD1 dG _{G0} _ _{D0}.
    by apply: Weakening.
  + move=> P Q /oft_par_inv []D1 []D2 []Hdef []<- []Op Oq.
    by rewrite unionC; apply: t_par =>//; rewrite unionC.
  + move=> P Q R /oft_par_inv []D1 []D2 []Hdef []<- []Opq Or.
    move: Opq Hdef => /oft_par_inv []D11 []D12 []Hdef'[]<- []Op Oq.
    rewrite -unionA => Hdef; move: (union_def Hdef) => []-Hdef0 Hdef1.
    by do ! apply: t_par=>//.
  + move=> P Q lcQ /oft_par_inv []D1 []D2 []Hdef []<- []Op Oq.
    elim/oft_inv: Op =>// _ L G0 S P1 D0 OP _{G0} []EqP1.
    move: EqP1 OP=>->{P1} OP _{D0}.
    apply (t_nu_nm (L:=na_dom G ++ L) (s:=S))=> x; rewrite mem_cat negb_or.
    move=>/andP-[/notin_nadom_dom-xG x_L]; rewrite /open_n0 /= -!/(open_n0 _ _).
    apply: t_par=>//; first by apply: OP.
    rewrite /open_n0 -opn_lc //; apply: wkn_ctx_oft =>//.
    by rewrite def_addb (oft_def_ctx Oq) xG.
  + move=> P Q lcQ /oft_par_inv []D1 []D2 []Hdef []<- []Op Oq.
    elim/oft_inv: Op =>//[ _ G0 P1 D0 T L Op _{G0} []EqP1 _{D0}
                         | _ G0 P1 D0 Op _{G0} []EqP1 _{D0}];
      move: EqP1 Op =>->{P1} Op.
    - apply: (t_nu_ch (L:=ch_dom D2 ++ L) (T:=T)) => ki.
      rewrite -!add_union mem_cat negb_or=>/andP-[/notin_chdom_dom-kiD2 ki_L].
      rewrite /open_k0 /=; apply t_par; first by apply: Op.
      by rewrite -opk_lc.
      move: (oft_def (Op ki ki_L)).
      by rewrite !add_union !def_addb !in_addb !dom_union Hdef !(negPf (kiD2 _))
                 !Bool.orb_false_r !ke_eqE eq_refl -[Pos == Neg]/(false)
                 !Bool.andb_false_r (proj1 (union_def Hdef))/=.
    - by apply: (t_nu_ch'); apply: t_par.
  + elim/oft_inv=>// _ L G0 S P D0 Op _{G0} []EqP _{D0}.
    move: EqP Op=>-> Op.
    move: (SC.fresh _) (SC.fresh_not_in (na_dom G ++ L)) => k.
    rewrite mem_cat negb_or =>/andP-[k_G k_L].
    move: (Op k k_L); rewrite /open_n0 -(opn_lc _ _ lc_inact).
    elim/oft_inv =>// _ G0 D0 cD /def_nested-dG _{G0} _ _{D0}.
    apply: t_inact =>//.
  + elim/oft_inv=>// _.
    - move=> G0 P1 D0 T L Op _{G0} []EqP _{D0}.
      move: (CN.fresh _) (CN.fresh_not_in L) => ki ki_L.
      move: EqP Op=>-> /(_ ki ki_L).
      rewrite /open_k0 -(opk_lc _ _ lc_inact).
      elim/oft_inv =>// _ G0 D0 cD dG _{G0} _ _{D0}.
      apply: t_inact=>//.
      move: (proj1 cD) => Def1; move: (def_nested (def_nested Def1)) => Def2.
      move: Def1; rewrite !def_addb !in_addb !ke_eqE eq_refl /=
                  -[Pos == Neg]/(false) Def2 /= negb_and negbK =>/andP-[knD].
      rewrite (negPf knD) /= => kpD.
      split => // a a_D.
      move: cD=>/proj2=>/(_ a); rewrite !in_addb !def_addb !a_D.
      rewrite !ke_eqE !eq_refl /= -[Pos == Neg]/(false) !(in_dom_def a_D) /=
              !negb_and !negbK !(negPf knD) !(negPf kpD) !Bool.orb_true_r
              !Bool.andb_true_r  /= => /(_ is_true_true).
      rewrite/binds !look_addb !def_addb !in_addb knD Def2 ke_eqE eq_refl kpD/=.
      have: a != ke (ki, Pos)
        by apply: contraT; rewrite negbK=>/eqP-eq; move: eq a_D kpD=>->->.
      have: a != ke (ki, Neg)
        by apply: contraT; rewrite negbK=>/eqP-eq; move: eq a_D knD=>->->.
      by move=>/negPf->/negPf->.
    - move=> G0 P1 D0 Op _{G0} []EqP _{D0}.
      by move: EqP Op=>->.
  + move=>P. elim/oft_inv=>//.
    move=>HH G0 P1 D0 Comp HHH Eq1 Eq2 Eq3.
    inversion Eq2 ; subst.
    rewrite [D]union_nil.
    (* apply: t_par ; first easy. *)
    auto.
    (***)
    apply: t_par.
    move:HHH.
    move/Weakening=>H.
    have: oft G P (D \:/ nil).
    apply: H=>//.
    by move:HH=>/oft_def; rewrite -union_nil.
    by rewrite -union_nil.
    (***)
    apply: t_bang=>/=.
    easy.
    easy.
    by move:HH=>/oft_def; rewrite -union_nil.
Qed.

Theorem SubjectReductionStep G P Q D:
  oft G P D -> balanced D -> P --> Q -> exists D', D ~~> D' /\ oft G Q D'.
Proof.
  move=> Op bD PQ; elim: PQ G D Op bD => {P} {Q}.
  + move=> P Q a lcp lcq G D Hoft balD.
    move: Hoft balD => /oft_par_inv []D1 []D2 []Hdef []<-{D} []Op Oq balD.
    move: Op Oq lcp lcq=>
    /oft_acc_inv []Lpc []Lpk []t []a' []->{a} []B Op Oq lcp lcq.
    move: Oq B lcp lcq =>
    /oft_req_inv []Lqc []Lqk []t' []a []/na_free_inj->{a'} []B' Oq B lcp lcq.
    move: B' (UniquenessBind B B') Oq => _ []<- _ Oq.
    exists (D1 \:/ D2); split => //; first by apply: tred_none.
    apply: t_nu_ch => ki kiF; eval_open_k; do 2 (rewrite unionC -add_union).
    rewrite open_k_c; last by apply/lc_isfree_k; lc_getfree_k lcp.
    rewrite open_k_c; last by apply/lc_isfree_k; lc_getfree_k lcq.
    apply: t_par;
      [ move: (Op (ke (ki, Pos)))=>/={Op}Op; apply: Op; inst_notin_cat kiF
      | move: (Oq (ke (ki, Neg)))=>/={Oq}Oq; apply: Oq; inst_notin_cat kiF
      | have kiF' : ki \notin ch_dom (union D1 D2) by inst_notin kiF
      ].
    move: (notin_chdom_dom Neg kiF') (notin_chdom_dom Pos kiF') => kn kp.
    move: (def_add_assumption (dual t) kn Hdef) => def_add_k.
    do 2 (rewrite add_union unionC); rewrite !def_add notin_add //.
    by do ! split => //; apply/andP; split =>//; rewrite ke_posneg_neq.
  + move=> k p pd e P Q Lcp Bq Dp G D Opar.
    move: Opar => /oft_par_inv  [] D1 [] D2 [] Hdef [] <- [] Os Or.
    move: Os Hdef => /oft_send_inv-[]k' []S []T []D'0 []/eqP.
    rewrite chanofentry_ch=>/eqP-> {k'} []-> []Oe OP Hdef.
    move: Or Hdef=> /oft_receive_inv-[]k'' []S' []T' []D'1 []/eqP.
    rewrite chanofentry_ch=>/eqP-> {k''} []-> []L OQ Hdef.
    move: Dp; rewrite eq_sym => dual_p_pd Bd.
    have: balanced (add (ke (k, p )) (output S  T ) D'0 \:/
                    add (ke (k, pd)) (input  S' T') D'1) by  apply: Bd.
    (do 2 rewrite unionC add_union) => /(add_balanced dual_p_pd)/=-/eqP-[]ES T'T.
    move: ES T'T Bd OQ Hdef =>->-> Bd OQ Hdef.
    move: pd dual_p_pd OQ Hdef Bd => pd /eqP-> OQ {pd}.
    (do 2 rewrite unionC add_union); rewrite add_swap => Hdef /balanced_next-Bd.
    have Hdef': def (add (ke (k, p)) T
                         (add (ke (k, dual_pol p)) (dual T) (D'0 \:/ D'1)))
      by move: Hdef; rewrite !def_addb (dom_diff_eq _ _ (input S (dual T))) //.
    exists ( add (ke (k, p)) T D'0 \:/
                 add (ke (k, dual_pol p)) (dual T) D'1).
    split=>//; first by
        rewrite add_union [in D'0 \:/ add _ _ _](unionC)
                add_union [in D'1 \:/ _](unionC); apply: (tred_head left).
    apply: t_par =>//; last by do 2 rewrite add_union unionC.
    move: (EV.fresh_not_in ((fv_exp e ++ fv_e Q) ++L)).
    set x := EV.fresh ((fv_exp e ++ fv_e Q) ++L).
    rewrite !mem_cat !negb_or => /andP-[/andP-[x_fve x_fvQ] x_fvL].
    move: (OQ x x_fvL) => {OQ} OQ.
    move: (oft_def_ctx OQ) => defG; move: (binds_top_add defG) OQ => bindsG.
    move: (wkn_ctx_oft_exp Oe defG) => {Oe} Oe.
    move=>/(ExpressionReplacement bindsG Oe).
    rewrite (subst_exp_open_e e x_fvQ) /open_e0.
    by apply: str_ctx_oft_proc; apply: fve_opene.
  + move=> k p pd k' P Q LcP BQ /eqP<-{pd} G D.
    move=> /oft_par_inv  [] D1 [] D2 [] Hdef [] <- [] Os; move: Os Hdef.
    move=>/oft_throw_inv []k0 []k1 []T []T' []D0 []/eqP-ch1 []<-.
    move: ch1; rewrite chanofentry_ch=>/eqP-> {k0} []-> []Hd Ho Hdef Oq.
    move: Oq Hdef=> /oft_catch_inv-[]k0 []D3 []T0 []T0' []/eqP.
    rewrite chanofentry_ch=>/eqP->[]->[]L[]L' Ho'.
    rewrite add_union unionC add_union unionC add_union => Hdef Hbal.
    move: (balanced_next Hbal) => Hbal'; move: Hbal.
    move=> /add_balanced; rewrite dual_polK =>/(_ (eq_refl p))/=/eqP-[eq1 eq2].
    have {eq2}eq2: dual T' = T0' by rewrite eq2 dualK.
    move: eq1 eq2 Ho' Hdef =><-<-{T0}{T0'} Ho' Hdef.
    exists (add (ke (k, p)) T'
                (add (ke (k, dual_pol p)) (dual T')
                     (add k1 T (D0 \:/ D3)))).
    have Hdef' : def (add (ke (k, p)) T'
                          (add (ke (k, dual_pol p)) (dual T')
                               (add k1 T (D0 \:/ D3))))
      by move: Hdef; rewrite !def_addb !(dom_diff_eq _ _ T).
    split; first by apply: (tred_head left).
    rewrite unionC -add_union -add_union add_swap unionC -add_union.
    apply: t_par =>//;
      last by rewrite add_swap add_union unionC !add_union unionC //.
    move: (LC.fresh _) (LC.fresh_not_in (L ++ fv Q ++ va_dom D3))=> x.
    rewrite !mem_cat !negb_or => /andP-[HL /andP-[x_free x_D3]].
    move: (Ho' (ce x) HL)=>{Ho'}/=Ho'.
    have Hd'': def (add (ce x) T (add (ke (k, dual_pol p)) (dual T') D3))
      by apply: (oft_def Ho').
    rewrite -(subst_add (c:=ce x))//.
    rewrite -(subst_proc_open (x:=x) (lc_chanofentry _))//.
    apply ChannelReplacement =>//.
    rewrite subst_add // add_swap.
    by move: Hdef' => /def_nested; rewrite unionC -!add_union => /union_def-[].
  + move=> P P' Q Q' LcP LcQ PP' P'Q' IH Q'Q G D OP BD.
    move: OP => /(CongruencePreservesOft PP')=> Op.
    move: IH => /(_ G D Op BD) => [][D'][DD']OQ.
    exists D'; split=>//.
    by apply: (CongruencePreservesOft Q'Q).
  + move=> P P' Hstep IH G D OP bD.
    elim/oft_inv : OP => // _ L G0 T P1 D0 Hoft _ {G0} []-PP1 _ {D0};
                           move: PP1 Hoft =>-> {P1} Hoft.
    move: (SC.fresh _) (SC.fresh_not_in (fn P' ++ na_dom G ++ L)) =>x.
    rewrite !mem_cat !negb_or => /andP-[x_fn /andP-[/notin_nadom_dom-x_G x_L]].
    case: (IH L x x_L _ _ (Hoft _ x_L) bD) => D' []bD' Hoft'.
    exists D'; split=>//.
    apply: (t_nu_nm (L:=na_dom G ++ L) (s:=T)) => x'.
    rewrite mem_cat negb_or => /andP-[/notin_nadom_dom-x'G x'L].
    rewrite -(subst_add (c:=ne x));
      last by rewrite def_addb x_G (def_nested (oft_def_ctx Hoft')).
    rewrite -(subst_open_n _ x_fn).
    apply: EndpointReplacement=>//.
    rewrite subst_add //; last by apply: (oft_def_ctx Hoft').
    by rewrite def_addb x'G (def_nested (oft_def_ctx Hoft')).
  + move=> P P' Hstep IH G D OP bD.
    elim/oft_inv: OP => // _.
    - move=> G0 P1 D0 T L OP1 _{G0} []EqP1 _{D0}; move: EqP1 OP1=>->{P1} OP.
      move: (CN.fresh _) (CN.fresh_not_in (freev_k P' ++ ch_dom D ++ L)) => k.
      rewrite !mem_cat !negb_or => /andP-[k_P' /andP-[/notin_chdom_dom-k_D k_L]].
      move: (OP k k_L) (Hstep L k k_L) => {OP}OP {Hstep}Hstep.
      move: (oft_def OP) => Hd.
      move: (IH L k k_L G _ OP) => /(_ (add_dual_bal Hd bD))-[D'] [bD'] Hoft.
      move: (tred_step_add bD bD') =>[T' [D'' Eq]].
      move: Eq Hoft bD'=>->/=Hoft bD'{D'}.
      have Hd': def (add (ke (k, Pos)) T' (add (ke (k, Neg)) (dual T') D''))
        by move: (typred_def bD')=>[<-_].
      exists D''; split; first by apply: (tred_step_tail Hd bD').
      apply: (t_nu_ch (L:=ch_dom D'' ++ k::L) (T:=T')) => ki.
      rewrite mem_cat in_cons !negb_or => /andP-[/notin_chdom_dom-ki_D /andP-[kik ki_L]].
      have Hd0 : def (add (ke (k, Pos)) T' (add (ke (ki, Neg)) (dual T') D'')).
        rewrite def_addb in_addb ke_eqE eq_sym (negPf kik)
                def_addb ki_D (def_nested (def_nested Hd')) /=.
        by move: Hd'; rewrite add_swap !def_addb=>/andP-[/andP-[_ ->]].
      rewrite -(subst_add (c:= ke (k, Pos))) //.
      rewrite add_swap -(subst_add (c:= ke (k, Neg))); last by rewrite add_swap.
      rewrite -/(subst_k_env _ _ _) add_swap -(substk_openk (x:=k)) //.
      apply: ChannelNameReplacement=>//.
      rewrite /subst_k_env add_swap subst_add add_swap // subst_add //.
      by rewrite def_addb (def_nested Hd0) /= in_addb ki_D /= negb_or negb_and
                 ke_eqE eq_refl orbC /= ki_D.
    - move=>G0 P1 D0 OP1 _{G0} [EqP1 EqD0].
      move: (CN.fresh _) (CN.fresh_not_in (ch_dom D)) => k kf.
      move: (IH (ch_dom D) k kf G D)=>{IH}IH.
      move: EqP1 OP1=>->{P1}OP {EqD0}{D0}.
      move: (oft_lc OP)  => lc_P.
      move: OP; rewrite (opk_lc 0 (CN.Free k) lc_P) => Hoft.
      move: (IH Hoft bD); rewrite /open_k0 => []{IH}[D' [DD' IH]].
      move: kf=>/notin_chdom_dom-k_free.
      move: (k_free Pos) (k_free Neg); rewrite -!(typred_dom DD')=>fp fn.
      have k_fresh_D: k \notin ch_dom D' by
        apply:contraT; rewrite negbK=>F; move:F fp fn=>/in_chdom_dom=>[][[->|->]].
      have k_fresh_P' : k \notin freev_k (open_k0 P' k) by
          apply: contraT; rewrite negbK=>kP';
            move: (infv_indom_k IH kP') k_fresh_D=>->.
      move: k_fresh_P' => /(contra (fv_fbv_k _)) => k_fresh_P'.
      move: IH; rewrite -(opk_notfree _ _ k_fresh_P') // =>IH.
      by exists D'; split=>//; apply: t_nu_ch'.
  + move=>P P' Q lcq PP' IH G D Opar bD.
    elim/oft_inv: Opar => // _ G0 P1 Q0 D1 D2 OP1 OQ0 Hdef _{G0} []-EqP EqQ.
    move: EqP EqQ OP1 OQ0=>->-> OP OQ{P1}{Q0} Eq.
    move: Eq bD=><- {D}bD; move: (balanced_union bD)=>[bD1 _].
    case: (IH G D1 OP bD1)=> D1' [bD1' OP'].
    exists (D1' \:/ D2).
    split; first by apply: step_union_l.
    apply: t_par=>//; rewrite -(proj1 (typred_def (step_union_l _ bD1'))).
    by apply: (proj1 bD).
  + move=>k kd P Pl Pr lcp lc_Pl lc_Pr dual_ch G D Op bD.
    elim/oft_inv: Op => // _.
    move=> G0 P1 Q D1 D2 OP1 OQ Hdef _ {G0} []EqP1 EqQ EqD.
    move: EqP1 EqQ EqD OP1 OQ bD =>->-><- OP{P1} OQ{Q} bD.
    elim/oft_inv: OP => // _.
    move=> G0 k0 P1 D0 T T' OP1 _ {G0} []Eqk EqP1 EqD1.
    move: Eqk EqP1 EqD1 dual_ch OQ Hdef bD OP1
              =><--><-{k}{P1}{D1} dual_ch OQ Hdef bD OP.
    elim/oft_inv: OQ => // _.
    move=>G0 k P1 Q D1 T0 T0' OP1 OQ _{G0} [] kk0 P1Pl QPr EqD2.
    move: kk0 P1Pl QPr EqD2 dual_ch OP1 OQ Hdef bD
              =><-{kd}->{P1}->{Q}<-{D2} dch OPl OQr Hdef bD.
    move: dch; case: k0 OP Hdef bD=>//[][ka ap]/=.
    case: k OPl OQr =>//[][kb bp]/=; case: ifP=>//.
    rewrite -[CN.Free _ == _]/(ka == kb) =>/eqP-> OPl OQr OP Hdef bD /eqP-Eq.
    move: Eq OPl OQr Hdef bD =><-{bp} OPl OQr Hdef.
    rewrite add_union [in D0 \:/ add _ _ _](unionC) add_union unionC.
    move=>/balanced_add/= =>[][_ [][EqT EqT'] bD].
    have{EqT}EqT: T0 = dual T by rewrite EqT dualK.
    have{EqT'}EqT': T0' = dual T' by rewrite EqT' dualK.
    move: EqT EqT' OPl OQr Hdef=>->->{T0}{T0'} OPl OQr Hdef.
    exists (add (inr (kb, ap)) T (add (inr (kb, dual_pol ap)) (dual T) (D0 \:/ D1))).
    split; first by apply (tred_head left).
    rewrite unionC -add_union unionC -add_union.
    apply: t_par=>//.
    rewrite add_union unionC add_union unionC; move: Hdef.
    by rewrite add_union unionC add_union unionC !def_addb !in_addb.
  + move=>k kd P Pl Pr lcp lc_Pl lc_Pr dual_ch G D Op bD.
    elim/oft_inv: Op => // _.
    move=> G0 P1 Q D1 D2 OP1 OQ Hdef _ {G0} []EqP1 EqQ EqD.
    move: EqP1 EqQ EqD OP1 OQ bD =>->-><- OP{P1} OQ{Q} bD.
    elim/oft_inv: OP => // _.
    move=> G0 k0 P1 D0 T T' OP1 _ {G0} []Eqk EqP1 EqD1.
    move: Eqk EqP1 EqD1 dual_ch OQ Hdef bD OP1
              =><--><-{k}{P1}{D1} dual_ch OQ Hdef bD OP.
    elim/oft_inv: OQ => // _.
    move=>G0 k P1 Q D1 T0 T0' OP1 OQ _{G0} [] kk0 P1Pl QPr EqD2.
    move: kk0 P1Pl QPr EqD2 dual_ch OP1 OQ Hdef bD
              =><-{kd}->{P1}->{Q}<-{D2} dch OPl OQr Hdef bD.
    move: dch; case: k0 OP Hdef bD=>//[][ka ap]/=.
    case: k OPl OQr =>//[][kb bp]/=; case: ifP=>//.
    rewrite -[CN.Free _ == _]/(ka == kb) =>/eqP-> OPl OQr OP Hdef bD /eqP-Eq.
    move: Eq OPl OQr Hdef bD =><-{bp} OPl OQr Hdef.
    rewrite add_union [in D0 \:/ add _ _ _](unionC) add_union unionC.
    move=>/balanced_add/= =>[][_ [][EqT EqT'] bD].
    have{EqT}EqT: T0 = dual T by rewrite EqT dualK.
    have{EqT'}EqT': T0' = dual T' by rewrite EqT' dualK.
    move: EqT EqT' OPl OQr Hdef=>->->{T0}{T0'} OPl OQr Hdef.
    exists (add (inr (kb, ap)) T' (add (inr (kb, dual_pol ap)) (dual T') (D0 \:/ D1))).
    split; first by apply (tred_head right).
    rewrite unionC -add_union unionC -add_union.
    apply: t_par=>//.
    rewrite add_union unionC add_union unionC; move: Hdef.
    by rewrite add_union unionC add_union unionC !def_addb !in_addb.
  + move=> P Q G D Ho balD.
    by exists D; split; first (by apply: tred_none); move: Ho=>/oft_ife_inv-[].
  + move=> P Q G D Ho balD.
    by exists D; split; first (by apply: tred_none); move: Ho=>/oft_ife_inv-[].
Qed.

Theorem SubjectReduction G P Q D:
  oft G P D -> balanced D -> P -->* Q -> exists D', balanced D' /\ oft G Q D'.
Proof.
  move => Hoft bD PQ; elim: PQ D bD Hoft => {P} {Q} P.
  + by move=> D bD Hoft; exists D.
  + move=> Q R Step QR IH D bD Hoft.
    move: (SubjectReductionStep Hoft bD Step) => []D' []bD' Hoft'.
    by move: (IH D' (typred_bal bD' bD) Hoft').
Qed.

Print Assumptions SubjectReduction.