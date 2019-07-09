From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import FinMap.finmap.
Require Import FinMap.ordtype.

Require Import SendRec.Atom.
Require Import SendRec.OddsAndEnds.

Section Environment.
  Context (K : ordType).
  Context (V : eqType).

  Inductive env := Undef | Def of {finMap K -> V}.
  Definition nil : env := Def (finmap.nil K V).
  Definition undef_env : env := Undef.

  (* equality of environments *)
  Definition env_eq (E1 E2 : env) :=
    match E1, E2 with
    | Def els1, Def els2 => els1 == els2
    | Undef, Undef => true
    |_, _ => false
    end.

  Lemma env_eqP : Equality.axiom env_eq.
  Proof.
    move=> E1 E2 ; rewrite/env_eq.
    elim E1 ; elim E2 ; try (move=>f;apply: reflectF;discriminate).
    - by apply: ReflectT.
    - move=>f ; apply: ReflectF ; discriminate.
    - move=>f.
      apply: ReflectF.
      discriminate.
    - move=>f f0.
      case: eqP.
      + by move=>eq;rewrite eq; apply: ReflectT.
      + move=>eq ; apply: ReflectF.
        congruence.
  Qed.

  Canonical Structure env_eqMixin := EqMixin env_eqP.
  Canonical Structure env_eqType := EqType (env) env_eqMixin.

  (* important definitions and operations *)
  Definition def E := if E is Def _ then true else false.
  Definition undef E := E == Undef.

  Definition upd x t E :=
    if E is Def els then Def (ins x t els) else Undef.

  Definition look x E :=
    if E is Def els then fnd x els else None.

  Definition dom (D : env) :=
    if D is Def els then
      supp els
    else [::].

  Definition add x t E :=
    if x \in dom E then Undef else upd x t E.

  Definition rem x E :=
    if E is Def els then Def(finmap.rem x els) else Undef.

  Definition dom_pred (D : env) : pred K := mem (dom D).

  Lemma in_domP x D : reflect (exists v, look x D = Some v) (x \in dom D).
  Proof.
    case: D => [|f]/=.
    + by apply: ReflectF; move => [].
    + case: suppP => [v|]->.
      - by apply: ReflectT; exists v.
      - by apply: ReflectF; move=>[].
  Qed.


  Lemma look_not_some x D : ~ (exists v, look x D = Some v) -> look x D = None.
  Proof.
    case: D=>//f /=; case: (suppP x f)=>[v|]-> //.
    by move=> H; exfalso; apply: H; exists v.
  Qed.

  Inductive look_spec x D : bool -> Prop :=
  | look_some v : look x D = Some v -> look_spec x D true
  | look_none : look x D = None -> look_spec x D false.

  Lemma domP x D : look_spec x D (x \in dom D).
  Proof.
    case: in_domP=>[|/look_not_some].
    + move=>[v]; apply: look_some.
    + apply: look_none.
  Qed.

  (* Properties of defined environments *)
  Lemma look_add a T D: def (add a T D) -> look a (add a T D) = Some T.
  Proof.
    elim D=>// f.
    rewrite/def/add/look/upd/dom.
    case: (suppP a f)=>//.
    rewrite fnd_ins eq_refl=>//.
  Qed.

  Lemma look_add_deep a a' T D: a != a' -> def (add a T D) -> look a' (add a T D) == look a' D.
  Proof.
    elim D=>// f Hd.
    rewrite/def/add/look/dom.
    case: (suppP a f)=>//.
    rewrite/upd=>_.
    rewrite fnd_ins.
      by rewrite ifN_eq ; [trivial | apply neqC].
  Qed.

  Lemma env_eq_look' k D D':
    def D -> D == D' -> look k D == look k D'.
  Proof.
    by move=>Hdef/eqP=>->.
  Qed.
  Lemma env_eq_look k D D':
    def D -> D == D' -> look k D = look k D'.
  Proof.
    by move=>Hdef/eqP=>->.
  Qed.

  Lemma env_eq_def D D':
    def D -> D == D' -> def D'.
  Proof.
    move=>Hdef.
    rewrite eq_sym.
    by move/eqP=>->.
  Qed.

  Lemma eq_hd k t t' D D':
    def (add k t D) -> add k t D == add k t' D' -> t = t'.
  Proof.
    move=>Hdef Heq.
    have Hdef':= env_eq_def Hdef Heq. (* this is not as pretty as it should be *)
    move:Heq.
    move/env_eq_look.
    move=>Hs.
    have HH := Hs k Hdef.
    move:HH.
    by (repeat rewrite look_add) ; first congruence ; try easy.
  Qed.

  Lemma singleton_def k v : def (add k v nil).
  Proof.
    by rewrite/def/add.
  Qed.

  Lemma in_dom_def a' D: a' \in dom D -> def D.
  Proof.
    elim D=>//.
  Qed.

  Lemma dom_add k v (E : env) : def (add k v E) ->
                                dom (add k v E) =i predU (pred1 k) (mem (dom E)).
  Proof.
    case: E=>// f.
    rewrite /add/dom.
    case: (suppP k f) ; first by intuition.
    by rewrite/upd=>_ Htrivial; apply: supp_ins.
  Qed.

  (* this proof may be missing the point, it should be simpler *)
  Theorem add_in_dom x t E: def(add x t E) <-> x \in dom (add x t E).
  Proof.
    split.
    {
      move=>H.
      rewrite dom_add.
      - pose (x\in (pred1 x)).
        rewrite/in_mem;simpl.
        by apply: predU1l.
      - easy.
    }
    by apply in_dom_def.
  Qed.

  Lemma rem_add_id k' v' D : def (add k' v' D) -> D = rem k' (add k' v' D).
  Proof.
    case: D =>// f; rewrite /add/dom/upd/rem; case: (suppP k' f)=>// /eqP-fnd_k.
    move=> _; congr Def; rewrite rem_ins eq_refl rem_supp //.
    by apply notin_supp_fnd.
  Qed.

  Lemma eq_rem k D D' :
    D = D' -> rem k D = rem k D'.
  Proof. by move=>->. Qed.

  Lemma eq_add k t D D' :
    def (add k t D) ->
    add k t D = add k t D' -> D = D'.
  Proof.
    move=> Def Eq; have Def':def (add k t D') by rewrite -Eq.
    move: Eq => /(eq_rem k); rewrite -!rem_add_id //.
  Qed.

  Lemma rem_add k k' v D : k != k' -> rem k' (add k v D) = add k v (rem k' D).
  Proof.
    move=> kk'; case: D =>// f; rewrite /add/upd/rem/dom supp_rem !inE kk'/=.
    by case: suppP =>// _; congr Def;rewrite ins_rem (negPf kk').
  Qed.

  Lemma add_rem_id x v E : look x E == Some v -> add x v (rem x E) = E.
  Proof.
    case: E=>//f; rewrite/look/rem/add/dom supp_rem !inE eq_refl/= =>H.
    congr Def; rewrite ins_rem eq_refl.
    elim/fmap_ind': f H =>// k v' f path_k_f IH.
    rewrite ins_ins; case: ifP=>[/eqP->|].
    + by rewrite fnd_ins eq_refl -[Some _ == _]/(v' == v) =>/eqP->.
    + by rewrite fnd_ins =>-> H; rewrite IH.
  Qed.

  Lemma in_dom_rem c c' D :
    c \in dom (rem c' D) = (c != c') && (c \in dom D).
  Proof.
    case: D=>/=; first by rewrite andbC.
      by move=> f /=; rewrite supp_rem !inE.
  Qed.

  Lemma in_dom_add c c' T D :
    c \in dom (add c' T D) = def (add c' T D) && ((c == c') || (c \in dom D)).
  Proof.
    case: D=>// f; rewrite /add/look/upd/dom.
    by case: suppP=>[v'|]//H; rewrite supp_ins !inE/=.
  Qed.

  Lemma in_dom_upd c c' T D :
    c \in dom (upd c' T D) = def D && (c == c') || (c \in dom D).
  Proof.
    case: D=>/=//f; rewrite /add/look/upd/dom /=.
    by rewrite supp_ins !inE.
  Qed.

  Lemma def_nested a t E: def (add a t E) -> def E.
  Proof.
    by elim: E ; easy.
  Qed.

  Lemma def_diff_value (x : K) (t t' : V) E: def (add x t E) -> def (add x t' E).
  Proof.
    case: E => // f; rewrite /add /look /upd/dom.
    case: (suppP x f)=>//.
  Qed.


  (* Lemma in_add_undef k t E: k \in dom(E) -> undef(add k t E). *)
  (* Proof. *)
  (*   elim E=>// f. *)
  (*   rewrite/undef/add/look/dom => Hk. *)
  (*   by elim (fnd_supp_in Hk) => x => ->. *)
  (* Qed. *)

  (* Lemma in_add_undef' k t E: def E -> undef (add k t E) -> k \in dom E. *)
  (* Proof. *)
  (*   elim E=>// f. *)
  (*   rewrite/def/undef/add=>_. *)
  (*   destruct (look k (Def f)) eqn: Hlook=>//. *)
  (*   move:Hlook. *)
  (*   rewrite/look/dom=>// Hfind _ . *)
  (*   apply:in_supp_fnd. *)
  (*   by rewrite Hfind. *)
  (* Qed. *)

  Lemma in_add_undef k t E: def E -> undef (add k t E) <-> k \in dom E.
  Proof.
    elim E=>// f.
    split.
    {
      move:H.
      rewrite/def/undef/add/dom=>_.
      case: (suppP k f)=>//.
    }
    {
      rewrite/undef/add/look/dom/upd => Hk.
      case: (suppP k f)=>//.
      by elim (fnd_supp_in Hk) => x => ->.
    }
  Qed.

  (* Maybe we want to choose this one over the previous formulation *)
  (* Lemma in_add_undef' k t E: def E /\ undef (add k t E) <-> k \in dom E. *)
  (* Proof. *)
  (*   elim E=>//. *)
  (*   rewrite/def/dom in_nil. *)
  (*   by split ; [case | congruence]. *)
  (*   move=>f. *)
  (*   split. *)
  (*   { *)
  (*     case=>//. *)
  (*     (* move:H. *) *)
  (*     rewrite/def/undef/add=>_. *)
  (*     destruct (look k (Def f)) eqn: Hlook=>//. *)
  (*     move:Hlook. *)
  (*     rewrite/look/dom=>// Hfind _ . *)
  (*     apply:in_supp_fnd. *)
  (*     by rewrite Hfind. *)
  (*   } *)
  (*   { *)
  (*     rewrite/undef/add/look/dom => Hk. *)
  (*     by elim (fnd_supp_in Hk) => x => ->. *)
  (*   } *)
  (* Qed. *)

  Lemma add_twice k t t' E : undef(add k t (add k t' E)).
  Proof.
    rewrite/undef.
    destruct (add k t' E) eqn: A1 =>//.
    have Hd: def(add k t' E) by rewrite A1. move:Hd.
    move/add_in_dom/in_add_undef.
    rewrite A1.
    apply.
    by [].
  Qed.

  Lemma def_add_twice k k' t t' E : def(add k t (add k' t' E)) -> k != k'.
  Proof.
    move=> Df; apply: contraT; rewrite negbK => /eqP-eq; move: eq Df =>->.
    by move: (add_twice k' t t' E)=>/eqP->.
  Qed.

  Lemma rem_swap k k' E:
    rem k (rem k' E) = rem k' (rem k E).
  Proof.
    case: E=>//f; rewrite /rem; congr Def.
    by rewrite rem_rem; case: ifP=>[/eqP->|]//; rewrite rem_rem eq_refl.
  Qed.

  Lemma add_swap k k' t s E:
    add k t (add k' s E) = add k' s (add k t E).
  Proof.
    case: E=>// f.
    rewrite /add !fun_if /= !in_nil !supp_ins !inE.
    case: (suppP k f)=>[v|]fnd_k_f; case: (suppP k' f)=>[v'|]fnd_k_f'=>//.
    + by rewrite orbC.
    + by rewrite orbC.
    + rewrite !Bool.orb_false_r; case: ifP; rewrite eq_sym=>H; rewrite H //.
      by congr Def; rewrite ins_ins H.
  Qed.

  Theorem dom_nested a b t E : def (add b t E) -> a \in dom E -> a \in dom (add b t E).
  Proof.
    elim: E ; try easy.
    rewrite/add/dom.
    move => f.
    case: (suppP b f)=>[v|]// _ _; rewrite /upd => H.
    by rewrite supp_ins inE H orbC.
  Qed.

  Definition ckey : K * V -> K := key.
  (* a lemma about finmaps *)
  Definition sorted_filter_by_pred s (p : pred K) :
    sorted ord (map key s) -> sorted ord (map key (filter (preim ckey p) s)).
  Proof.
    move=>H ; rewrite -filter_map path.sorted_filter //.
    by apply: trans.
  Defined.

  Definition filter_by_key (pr : pred K) (E: env) : env :=
    if E is Def els then
      let: FinMap s' p' := els
      in Def (@FinMap _ _ (filter (preim ckey pr) s') (@sorted_filter_by_pred s' pr p'))
    else Undef.

  Lemma filter_by_key_nil (pr : pred K) : filter_by_key pr nil == nil.
  Proof.
    rewrite/filter_by_key/nil/finmap.nil=>//.
  Qed.

  Definition partition_by_key (pr : pred K) (E: env) : env * env :=
    (filter_by_key pr E, filter_by_key (predC pr) E).

  Fixpoint map_on_keys' (f : K -> K) (s : seq (K * V)) : finMap K V :=
    if s is (k, v)::s'
    then ins (f k)  v (map_on_keys' f s')
    else finmap.nil K V.

  Definition map_on_keys (f : K -> K) (E : env) : env :=
    if E is Def els
    then Def (map_on_keys' f (seq_of els))
    else Undef.

  Lemma filter_preserves_def E p : def E -> def (filter_by_key p E).
  Abort. (* desired property, prove if actually needed *)

  Definition intersection (E1 E2 : env) : env :=
    if (E1, E2) is (Def f1, Def f2) then Def (intersect f1 f2) else Undef.

  Definition difference (E1 E2 : env) : env :=
    if (E1, E2) is (Def f1, Def f2) then Def (diff f1 f2) else Undef.

  (* if the environments are disjoint, if one or both are undefined they are not disjoint *)
  Definition disjoint (E1 E2 : env) : bool :=
    if (E1, E2) is (Def els, Def els') then disj els els' else false.

  Lemma disjoint_nil : disjoint nil nil.
  Proof.
    rewrite/disjoint/nil ; apply disj_nil.
  Qed.

  Definition union (E1 E2 : env) : env :=
    if (E1, E2) is (Def els, Def els')
    then if disj els els' then Def (fcat els els')
         else Undef
    else Undef.

  Notation "A --- B" := (difference A B)  (at level 80, right associativity). (* : env_scope. *)
  Notation "A /:\ B" := (intersection A B) (at level 80, right associativity). (* : env_scope. *)
  Notation "A \:/ B" := (union A B) (at level 80, right associativity). (* : env_scope. *)


  Lemma unionC : commutative union.
  Proof.
    move=> A B.
    elim A; elim B=>//fa fb.

    rewrite/commutative/union=>//.
    rewrite disjC.
    destruct (disj fa fb) eqn:Hd; try easy.
    by rewrite fcatC ; [ easy | rewrite disjC].
  Qed.

  Lemma union_undef E: (E \:/ undef_env) = undef_env.
  Proof.
    elim E=>//.

  Qed.

  Lemma unionA : associative union.
  Proof.
    move=> A B C.
    elim A; elim B ; elim C=>//fa fb.
    by do !(try rewrite unionC; try rewrite union_undef).

    move=>fc.

    rewrite/union=>//.
    destruct (disj fb fa) eqn: Hba=>//.
    destruct (disj fc fb) eqn: Hcb=>//.
    destruct (disj fc (fcat fb fa)) eqn: Hdcba=>//.
    destruct (disj (fcat fc fb) fa) eqn: Hdcba'=>//.

    rewrite fcatA ; easy.

    move: Hdcba Hdcba'.
    rewrite disj_fcat.
    move/andP.
    case.

    rewrite [disj (fcat fc fb) fa]disjC disj_fcat.
    rewrite Bool.andb_false_iff.
    move=>Hcb' Hca.
    case ; rewrite disjC
    ; [move:Hca | move:Hba] ; move=>-> ; easy.

    rewrite [disj (fcat fc fb) fa]disjC disj_fcat [disj fa fb]disjC Hba.
    move:Hdcba.
    rewrite disj_fcat.
    rewrite Bool.andb_false_iff.
    case.
    congruence.
    rewrite disjC=>->.
    rewrite/andb=>//.
    by rewrite disj_fcat Hcb=>//.

    destruct (disj fc fb) eqn: Hcb ; try easy.
    by rewrite disjC disj_fcat [disj fa fb]disjC Hba Bool.andb_false_r.
  Qed.

  Lemma disjointC : commutative disjoint.
  Proof.
    move=> A B.
    elim A ; elim B =>// fa fb.
    by rewrite/disjoint disjC.
  Qed.

  Lemma union_nil D : D = (D \:/ nil).
  Proof.
    elim D=>// f ; rewrite/union=>/=.
      by rewrite disj_nil fcats0.
  Qed.

  Lemma disjoint_union_def E1 E2:
    disjoint E1 E2 = def(E1 \:/ E2).
  Proof.
    elim E1 ; elim E2=>// f' f.
    by rewrite /disjoint/union; case: ifP.
  Qed.

  Lemma disjoint_wkn E1 E2 E3: disjoint E1 (E2 \:/ E3) -> disjoint E1 E2.
  Proof.
    elim E1=>// ; elim E2=>// ; elim E3 =>//f1 f2 f3.

    rewrite/disjoint/union=>//.
    elim (disj f2 f1) ; try easy.
    rewrite disj_fcat.
    move/andP.
    easy.
  Qed.

  Lemma disjoint_diff_inter D D' :
    def D -> def D' -> disjoint (D---D') (D /:\ D').
  Proof. by case: D; case: D' => // f1 f2 _ _; apply: disj_diff_intersect. Qed.

  Lemma union_def E1 E2: def (E1 \:/ E2) -> def E1 /\ def E2.
  Proof.
    elim E1 ; elim E2=>//.
  Qed.

  Lemma disjoint_union_3 E1 E2 E3:
    disjoint E1 E2 /\ disjoint E2 E3 /\ disjoint E1 E3 <-> def(E1 \:/ E2 \:/ E3).
  Proof.
    elim E1=>// ; elim E2=>// ; elim E3 =>// ; try (rewrite/disjoint ; simpl ; easy).
    move=>f1 f2 f3.
    split.
    { (* -> *)

      rewrite /disjoint/union.
      case=>H1.
      case=>H2 H3.
      rewrite H2.
      by rewrite disj_fcat H1 H3/andb.
    }
    { (* <- *)
      (* rewrite/union/disjoint. *)
      move=>H.
      split.
      move:H.
      rewrite -disjoint_union_def.
      by move/disjoint_wkn.

      split.
      apply union_def in H.
      case H.
      by move=>_; rewrite disjoint_union_def.
      rewrite unionA unionC unionA [(Def f1 \:/ Def f3)]unionC in H.
      apply union_def in H.
      case H.
      by rewrite disjoint_union_def.
    }
  Qed.

  Lemma disjoint_diff_comm D D' :
    def D -> def D' -> disjoint (D---D') (D' --- D).
  Proof. by case D; case D' => // f f' _ _; apply disj_diff_comm. Qed.

  Lemma diff_nil A: def A -> (nil --- A) == nil.
    case: A => // f; rewrite/nil/difference/filter_by_key=>//.
  Qed.

  Definition split (E1 E2 : env) : env * env * env :=
    (E1 --- E2, E1 /:\ E2, E2 --- E1).

  Definition update_all_with (v : V) (E : env) : env :=
    if E is Def els
    then Def (fmap_map (fun _ => v) els)
    else Undef.

  Definition binds a T (D : env) : bool :=
    (look a D) == Some T.

  Lemma binds_add a b T T' D:
    binds a T D -> def (add b T' D) ->
    binds a T (add b T' D).
  Proof.
    case: D => // f; rewrite /binds /add /upd /look/dom.
    case: (suppP b f) => [v|] fnd_b //.
    rewrite fnd_ins => fnd_a _.
    by case: ifP =>/eqP-cmp_a_b //; move: cmp_a_b fnd_b fnd_a =>->->.
  Qed.

  Lemma add_binds a b T T' D:
    binds a T D -> a!=b -> def (add b T' D) -> binds a T (add b T' D).
  Proof.
    case: D => // f; rewrite /binds /add /look /upd/dom => /eqP-fnd_a.
    case: (suppP b f) => [v|]_ /negbTE-ab _ //.
    by rewrite fnd_ins ab fnd_a.
  Qed.

  Lemma binds_next x y S S' G:
    y != x ->
    binds y S' (add x S G) ->
    binds y S' G.
  Proof.
    rewrite /binds; case: G =>// f; rewrite /add/look/upd/dom.
    by case: (suppP x f) =>[v|]_// /negPf-neq; rewrite fnd_ins neq.
  Qed.

  Theorem UniquenessBind a T T' D:
    binds a T D -> binds a T' D -> T = T'.
  Proof.
    rewrite/binds.
    move/eqP=>->/eqP.
    congruence.
  Qed.


  Lemma binds_top_add a T D:
    def (add a T D) ->
    binds a T (add a T D).
  Proof.
    case:D =>// f; rewrite/binds/add/look/dom;
      case: (suppP a f)=>[T'|]Hrw //.
    by rewrite /upd fnd_ins (eq_refl a).
  Qed.

  Lemma binds_top_addE a T T' D:
    def (add a T D) ->
    binds a T (add a T' D) ->
    T = T'.
  Proof.
    case:D =>// f; rewrite/binds/add/look/dom;
      case: (suppP a f)=>[T''|]Hrw //.
    by rewrite /upd fnd_ins eq_refl -[Some _ == _]/(T' == T) eq_sym => _ /eqP.
  Qed.

  Lemma binds_def a T D:
    binds a T D -> def D.
  Proof.
    elim D ; by [].
  Qed.

  Definition isin a (D : env) : bool :=
    if look a D is Some _ then true else false.

  (* Inductive ind_isin: K -> env -> Prop := *)
  (* | Cheating k D : isin k D = true -> ind_isin k D *)
  (* . *)

  Lemma isin_reflect k D : reflect (k \in dom D) (isin k D).
  Proof.
    case D.
    { (* undef *)
      constructor.
      have H := in_nil k.
      by intuition.
    }
    {
      move=>f //=.
      rewrite/isin/look.
        by case: suppP ; intros ;  rewrite e ; constructor.
    }
  Qed.

  (* first overloaded lemma *)
  Section Indom.
    Structure tagged_env := Tag{untag :> env}.

    Definition deeper_tag := Tag.
    Canonical Structure here_tag h := deeper_tag h.

    Definition invariant a (E : tagged_env) :=
      def E -> a \in dom (untag E).

    Structure find (a : K) :=
      Form { env_of :> tagged_env
             ; _ : invariant a env_of
         }.

    Lemma found_pf a t E : invariant a (here_tag (add a t E)).
    Proof.
      rewrite/invariant ; apply add_in_dom.
    Qed.

    Canonical Structure atom_found a t D :=
      @Form a (here_tag (add a t D)) (@found_pf a t D).

    Lemma deeper_pf a b s (f : find a) :
      invariant a (deeper_tag (add b s (untag (deeper_tag (untag (env_of f)))))).
      case: f=> [[E]].
      rewrite/invariant /= => H D.
      apply: dom_nested.
      - easy.
      - apply: H.
        apply: def_nested.
          by apply:D.
    Qed.

    Canonical Structure search_deeper a b s (f : find a) :=
      @Form a (deeper_tag (add b s (untag (env_of f)))) (@deeper_pf a b s f).

    (* main lemma *)
    Lemma indom (a : K)(b: K) (f : find a) :def f -> a \in (dom f).
    Proof.
        by case: f=>[[i]]; apply.
    Qed.

    Example ex1 a s b t (E : env):
      def(add b s (add a t E)) ->
      if a \in dom(add b s (add a t E)) then 1==1 else 1==0.
    Proof.
      move=>H.
        by rewrite indom.
    Qed.

    Example ex2 a t (E: env): def (add a t E) -> if a \in dom(add a t E) then 1==1 else 1==0.
    Proof.
      move=>H.
        by rewrite indom.
    Qed.

    Example ex3 a s b t c (E: env):
      def (add b s (add a t E)) ->
      if c \in dom(add b s (add a t E)) then 1==1 else 1==0.
    Proof.
      move=>H.
      (* by rewrite indom. *) (* this fails because c is not really there *)
    Abort.
  End Indom.

  Lemma def_add k t E:
    def (add k t E) <-> k \notin dom E /\ def E.
  Proof.
    split.
    { (* -> direction *)
      case: E=>// f.
    - rewrite/add/look/dom.
      by case: suppP.
    }
    { (* <- direction *)
      case.
      case E=>// f.
      by rewrite/add/look/dom/upd=>// /negPf-> _.
    }
  Qed.

  Lemma def_addb : forall (k : K) (t : V) (E : env),
      def (add k t E) = def E && (k \notin dom E).
  Proof.
    move => k t E; move: (def_add k t E).
    case: (boolP (def (add k t E)))=>_.
    + by move=>/proj1/(_ is_true_true)=>[][->->].
    + move=>/proj2; case: (boolP (k \notin dom E))=>_; last by rewrite andbC.
        by case: (boolP (def E))=>// _ /(_ (conj is_true_true is_true_true)).
  Qed.

  Lemma look_addb a b T (D : env) : look a (add b T D)
                                    = if def (add b T D)
                                      then if a == b then Some T else look a D
                                      else None.
  Proof.
    case: D=>// f;rewrite /add/dom def_addb andbC /=; case: suppP =>[v|]-H ///=.
    by apply: fnd_ins.
  Qed.

  (* convenience form of def_add *)
  Lemma def_add_assumption k T D:
    k \notin dom D -> def D -> def (add k T D).
  Proof.
    move=> H H'.
    by apply def_add.
  Qed.

  Lemma in_dom_add_diff k k' t E:
    k \in dom E -> def (add k' t E) -> k \in dom (add k' t E).
  Proof.
    move=>Hk Hdef.
    rewrite dom_add=>//.
    apply in_predU_r.
    by apply Hk.
  Qed.

  Lemma def_add_cancel k v v' E E' :
    def (add k v E) -> add k v E = add k v' E' -> v = v' /\ E = E'.
  Proof.
    case: E =>// f; case: E' =>[|f']; rewrite /add /=.
    + by case: suppP.
    + case: suppP => // Hf _; case: suppP => // Hf' [] ins_eq.
      move: (cancel_ins' ins_eq)=>eq; move: eq ins_eq=>->ins_eq; split=>//.
      congr Def; move: Hf Hf' => /eqP/notin_supp_fnd-Hf /eqP/notin_supp_fnd-Hf'.
      by apply: (cancel_ins Hf Hf' ins_eq).
  Qed.

  Lemma notin_dom_def k k' t E:
    k \notin dom E -> k != k' -> def (add k' t E) -> k \notin dom (add k' t E).
  Proof.
    move=> Hk Hkk' Hdef.
    rewrite dom_add ; last easy.
    by apply notin_predU; [rewrite/(_\notin_)/pred1=>// | apply Hk].
  Qed.

  Lemma in_addb x k v D :
    x \in dom (add k v D)
          = (k \notin dom D) && (def D && (x == k) || (x \in dom D)).
  Proof.
    rewrite /add; case: (domP k D)=>[v'|]_/=//.
    by case: D=>//f; rewrite /add/upd/dom supp_ins !inE.
  Qed.

  Lemma in_add k k' t E:
    def (add k' t E) ->
    k \in dom (add k' t E) = (k == k') || (k \in dom E).
  Proof.
    case E=>// f H.
    destruct (k \in dom (Def f)) eqn:Hk.
    {
      rewrite Bool.orb_true_r.
      by apply in_dom_add_diff.
    }
    {
      rewrite Bool.orb_false_r.
      destruct (k'==k) eqn:Hk' ; move:Hk' H.
      move/eqP=>->.
      rewrite eq_refl.
      by apply add_in_dom.

      move=> Hkk' H.
      rewrite eq_sym Hkk'.
      apply Bool.negb_true_iff in Hk.
      apply Bool.negb_true_iff in Hkk'.
      apply Bool.negb_true_iff.
      apply neqC in Hkk'.
      by apply notin_dom_def.
    }
  Qed.

  Lemma dom_add' k t E : def(add k t E) -> dom (add k t E) =i k :: dom E.
  Proof.
    move=>H k'.
    destruct (k'==k) eqn:Hk ; move:Hk.
    {
      move=>/eqP=>->.
      rewrite in_cons eq_refl.
      by rewrite indom ; easy. (* yay! I used this *)
    }
    {
      move=> Hdiff.
      rewrite in_add ; last easy.
      by rewrite in_cons.
    }
  Qed.

  Lemma dom_diff_eq (k : K) (v : V) v' D : dom (add k v D) = dom (add k v' D).
  Proof.
    case: D =>// f; rewrite /add/look/upd/dom; case: suppP =>[v0|]_//.
    rewrite /supp; case: f => l /= _; elim: l => // [[k' v'']] l IH /=.
    by case: (totalP k k') =>//; rewrite !map_cons IH.
  Qed.

  Lemma notin_add k k' T D:
    def (add k' T D) -> k \notin dom (add k' T D) = ((k != k') && (k \notin dom D)).
  Proof. by case D=>// f Hdef; rewrite in_add // negb_or. Qed.

  (* DC: FIXME: To finmap *)
  Lemma fnd_disj_none k (f f' : {finMap K -> V}) :
    (k \in supp f) -> disj f f' -> k \notin supp f'.
  Proof. by move => k_in_f /allP-H; apply/H. Qed.

  Lemma add_union k T D D':
    ((add k T D) \:/ D') = (add k T (D \:/ D')).
  Proof.
    case: D => // f; case: D' => [| f']; first by rewrite !union_undef.
    rewrite /add /upd /union /look/dom.
    case: suppP =>[v|]/eqP-fnd_k_f.
    + case: ifP => //; case: ifP =>// disj_f_f'.
      by rewrite supp_fcat inE/= (in_supp_fnd (s:=v)).
    + case: ifP; rewrite disjC disj_ins disjC.
      - move=>/andP-[k_nin_f' ->]; rewrite supp_fcat inE/=.
        move: fnd_k_f =>/notin_supp_fnd/negPf->.
        by rewrite (negPf k_nin_f') fcat_inss.
      - case: ifP; case: ifP =>// => disj_f_f'.
        rewrite Bool.andb_true_r => /negP/negP.
        by rewrite supp_fcat inE/= negb_or => /andP-[_ ->].
  Qed.

  Lemma dom_union D1 D2 k :
    (k \in dom (D1 \:/ D2)) =
    def (D1 \:/ D2) && ((k \in dom D1) || (k \in dom D2)).
  Proof.
    case: D1=>//f1; case: D2=>// f2; rewrite /union; case: ifP=>// _/=.
    by rewrite supp_fcat !inE.
  Qed.

  Lemma dom_update_all_with T D : dom (update_all_with T D) =i dom D.
  Proof. by case D =>// f /=; rewrite supp_map. Qed.

  Lemma notin_add_applied k k' T D:
    def (add k' T D) -> k \notin dom (add k' T D) -> (k != k') && (k \notin dom D).
  Proof. by move=>Hdef; rewrite notin_add. Qed.

  Definition subst_env c c' D :=
    match look c D with
    | Some T => add c' T (rem c D)
    | None => D
    end.

  Lemma subst_envK c D : subst_env c c D = D.
  Proof.
    case: D=>//f; rewrite /subst_env/look/add/rem/upd/dom supp_rem !inE eq_refl /=.
    case: (suppP c f)=>[v|] H; rewrite H //.
    rewrite ins_rem eq_refl; congr Def; move: H.
    (* FIXME: lift as lemma to finmap.v *)
    elim/fmap_ind': f =>// k v' f path_k IH.
    rewrite fnd_ins ins_ins; case: ifP=>//; first by move=> /eqP-> []->.
      by move=> _ fnd_c; rewrite IH.
  Qed.

  Lemma neq_add_substC x y z T D :
    x != y -> add x T (subst_env y z D) = subst_env y z (add x T D).
  Proof.
    case: D =>// f neq; rewrite /subst_env look_addb def_addb andbC /dom/look.
    rewrite eq_sym (negPf neq); case: suppP =>[v|]-H //.
    + rewrite /def/andb/negb; case: (suppP y f) =>[v'|]-H'; rewrite H'.
      by rewrite add_swap -rem_add // [add x _ _]/add/dom (in_supp_fnd (introT eqP H)).
      by rewrite [add x _ _]/add/dom (in_supp_fnd (introT eqP H)).
    + rewrite /def/negb/andb rem_add //.
      case: (suppP y f) =>[v'|]-H'; rewrite H' //.
      by rewrite add_swap.
  Qed.

  Lemma look_rem x k D : look x (rem k D) = if x == k then None else look x D.
  Proof.
    case: D=>/=; first by case: ifP.
    move=> f; by apply: fnd_rem.
  Qed.

  Lemma upd_rem_absorv x T D :
    upd x T (rem x D) = upd x T D.
  Proof.
    case: D=>// f; rewrite /rem/upd; congr Def.
    by rewrite ins_rem eq_refl.
  Qed.

  Lemma add_rem_absorv x T D :
    x \notin dom D -> add x T (rem x D) = add x T D.
  Proof.
    rewrite /add in_dom_rem eq_refl /= =>/negPf->.
    by rewrite upd_rem_absorv.
  Qed.

  Lemma look_some_in x v D : look x D = Some v -> x \in dom D.
  Proof. by move => /(ex_intro _ v)/in_domP. Qed.

  Lemma look_none_in x D : look x D = None -> x \notin dom D.
  Proof. by case: domP=>[v|]->. Qed.

  Lemma rem_substC x y z D :
    y != x -> z != x ->
    subst_env y z (rem x D) = rem x (subst_env y z D).
  Proof.
    rewrite /subst_env look_rem eq_sym=>/negPf->.
    case:(domP y D )=>[v|]H; rewrite H // => xz.
    by rewrite rem_swap -rem_add.
  Qed.

  Lemma eq_add_substC x y T D :
    def (add x T D) ->
    add y T (subst_env x y D) = subst_env x y (add x T D).
  Proof.
    case: D=>//f Df; rewrite /subst_env; rewrite look_add /look=>//.
    have c1f: x \notin supp f by move: Df; rewrite def_addb=>/andP-[].
    by rewrite (fnd_supp c1f) -rem_add_id.
  Qed.

  Lemma subst_addC x y z T D :
    def (add z T D) ->
    add (if z == x then y else z) T (subst_env x y D)
    = subst_env x y (add z T D).
  Proof.
    case: (boolP (x == z)) =>[/eqP->|].
    + by rewrite eq_refl; apply: eq_add_substC.
    + by rewrite eq_sym=>neq Df; rewrite (negPf neq); apply neq_add_substC.
  Qed.

  Lemma subst_add c c' T D :
    def (add c T D) -> subst_env c c' (add c T D) = add c' T D.
  Proof.
    case: (boolP (c' == c))=>[/eqP->|]; first by rewrite subst_envK.
    move=> neq H; case: D H=>//f; rewrite /add/dom; case: suppP => [v|]-H//_.
    rewrite /upd/subst_env/look fnd_ins eq_refl /rem rem_ins eq_refl /add/dom/upd.
     by rewrite supp_rem !inE neq /= rem_supp //; apply/notin_supp_fnd/eqP.
  Qed.

  Lemma def_addG k T D : def (add k T D) -> forall T', def (add k T' D).
  Proof. by move=> Df T'; apply: def_diff_value; apply: Df. Qed.

  Lemma def_subst_nested c c' D : def (subst_env c c' D) -> def D.
  Proof. by case: D. Qed.

  Lemma def_subst_dom c c' D :
    def D ->
    def (subst_env c c' D) =
    (c \notin dom D) || ((c \in dom D) && (c' \notin (dom (rem c D)))).
  Proof.
    case:D =>//f; rewrite /subst_env/look => _.
    by case: (suppP c f)=>[v|]-H; rewrite H// def_addb andbC /=.
  Qed.

  Lemma binds_subst k k0 k1 v D :
    def (subst_env k0 k1 D) ->
    binds k v D ->
    binds (if k == k0 then k1 else k) v (subst_env k0 k1 D).
  Proof.
    case: (boolP (k0 == k1))=>[/eqP->|neq];
      first by case: ifP=>[/eqP->|]=>//; rewrite subst_envK.
    case: D=>// f; rewrite /binds/subst_env/look/rem/add/upd/dom supp_rem !inE.
    rewrite eq_sym neq /=.
    case: (suppP k0 f)=>[v0|] E0; rewrite E0=>//.
    + case: suppP => [v1|]-E1 // _ .
      case: ifP=> [/eqP->|neq1]; first by rewrite fnd_ins eq_refl -E0.
      rewrite fnd_ins; case: ifP=>[/eqP->|]; first by rewrite E1.
      by rewrite fnd_rem neq1.
    + by move=> _; case: ifP=>[/eqP->|]; first by rewrite E0.
  Qed.

  Lemma def_subst c c' D :
    c' != c -> def D -> def (subst_env c c' D) ->
    (c \notin dom D) || ((c \in dom D) && (c' \notin dom D)).
  Proof. by move=>eq Df; rewrite def_subst_dom // in_dom_rem // eq negb_and. Qed.

  Lemma def_next k T D : def D -> k \notin dom D -> def (add k T D).
  Proof. by rewrite def_addb=>->->. Qed.

  Lemma look_subst x c c' D :
    def (subst_env c c' D) ->
    look x (subst_env c c' D) = if c \in dom D then if x == c' then look c D
                                                    else look x (rem c D)
                                else look x D.
  Proof.
    case: D =>//f; rewrite /subst_env/look/rem.
    case: (suppP c f) => [v|] H; rewrite H // fnd_rem.
    rewrite /add/rem/dom supp_rem !inE andbC.
    case: suppP =>[v'|] H'/=.
    - case: ifP=>///(rwP negPf); rewrite negbK=>/eqP-> _.
      by rewrite fnd_ins fnd_rem; case: ifP=>//->.
    - by rewrite fnd_ins fnd_rem.
  Qed.

  Lemma look_union x D1 D2 : look x (D1 \:/ D2) = if def (D1 \:/ D2)
                                                  then if x \in dom D2
                                                       then look x D2
                                                       else look x D1
                                                  else None.
  Proof.
    rewrite /look /union; case: D1=>// f1; case: D2=>//f2; case: ifP=>///=_.
    by rewrite fnd_fcat.
  Qed.

  Lemma in_dom_subst x c c' D :
    x \in dom (subst_env c c' D) ->
          ((c \in dom D) && ((x == c') ||
                             ((x != c') && (x \in dom (rem c D)))))
          || ((c \notin dom D) && (x \in dom D)).
  Proof.
    move=>H.
    have Df: def (subst_env c c' D) by move: H; case: (subst_env c c' D).
    move/in_domP: H => [v]; rewrite look_subst //; do ! case: ifP=>///=.
    + by move=> _ _ /(ex_intro _ v)/in_domP->.
    + by move=>_ /(ex_intro _ v)/in_domP->.
  Qed.

  Inductive def_spec D : bool -> Prop :=
  | def_some f : D = Def f -> def_spec D true
  | def_none : D = Undef -> def_spec D false.

  Lemma defP D : def_spec D (def D).
  Proof. by case: D =>[|v]; [apply: def_none|apply: (def_some (f:=v))]. Qed.

  Lemma def_rem k D : def (rem k D) = def D.
  Proof. by case: D. Qed.

  Definition can_subst k k' D :=
    (k == k') || (k \notin dom D) || (k' \notin dom D).

  Lemma can_substK k D : can_subst k k D.
  Proof. by rewrite /can_subst eq_refl. Qed.

  Definition can_add k D := k \notin dom D.

  Lemma def_substb k k' D :
    def (subst_env k k' D) =
    def D && can_subst k k' D.
  Proof.
    rewrite /can_subst.
    case: (boolP (k == k'))=>[/eqP->|]; first by rewrite subst_envK andbC.
    move=> neq; rewrite /subst_env/=; case: domP=>[v|]H; rewrite H/=;
      last by rewrite andbC.
    by rewrite def_addb def_rem in_dom_rem eq_sym neq /= andbC.
  Qed.

  Lemma subst_is_def k k' D :
    can_subst k k' D -> def D -> def (subst_env k k' D).
  Proof. by rewrite def_substb=>->->. Qed.

  Lemma dom_substb x k k' D :
    (x \in dom (subst_env k k' D)) =
    can_subst k k' D &&
              ((x == k') && (k \in dom D) || (x != k) && (x \in dom D)).
  Proof.
    case: (boolP (k == k'))=>[/eqP->|]/=; first by
        rewrite subst_envK can_substK;
          case: (boolP (x == k'))=>[/eqP->|]//; rewrite orbC.
    rewrite /can_subst /subst_env => kk'; rewrite (negPf kk')/=.
    case: (domP k D)=>[v|]H;rewrite H /=.
    + rewrite in_addb !in_dom_rem eq_sym kk' /= def_rem Bool.andb_true_r.
      by move: (look_some_in H) =>/in_dom_def->/=.
    rewrite Bool.andb_false_r/= andb_idl //; case: domP=>//v F _.
    by apply: contraT; rewrite negbK=>/eqP-EQ; move: EQ H F=>->->.
  Qed.

  Lemma subst_in k k' D :
    subst_env k k' D = if k \in dom D then subst_env k k' D else D.
  Proof. by rewrite /subst_env; case: domP=>[v|]-H; rewrite H. Qed.

  Ltac rw_step :=
    match goal with
    | [ H: (is_true (?L || ?R)) |- _ ] => move: H; move=>/orP-[H|H]//
    | [ H: (is_true (?L && ?R)) |- _ ] =>
      let H1 := fresh H in let H2 := fresh H in move: H; move=>/andP-[H1 H2]//
    | [ H: is_true (?k1 == ?k2) |- _ ] => move: H; move=>/eqP-H; try rewrite H
    | [ H: is_true (?k1 != ?k2) |- _ ] => move: H; move=>/negPf-H; try rewrite H
    | [ H: is_true (?k != ?k)   |- _ ] => move: H; rewrite eq_refl=>H //
    | [ H: is_true (_ \notin _) |- _ ] => move: H; move=>/negPf-H; try rewrite H
    | [ H: is_true (_ \in _)    |- _ ] => rewrite H
    | [ H: context[_ && false]  |- _ ] => move: H; rewrite !Bool.andb_false_r=>H
    | [ H: context[_ && true ]  |- _ ] => move: H; rewrite !Bool.andb_true_r=>H
    | [ H: context[_ || false]  |- _ ] => move: H; rewrite !Bool.orb_false_r=>H
    | [ H: context[_ || true ]  |- _ ] => move: H; rewrite !Bool.orb_true_r=>H
    | [ H: context[ ~~ (_ && _)]    |- _ ] => move: H; rewrite negb_and=>H
    | [ H: context[ ~~ (_ || _)]    |- _ ] => move: H; rewrite negb_or=>H
    | [ H: context[ ~~ ~~ _]     |- _] => move: H; rewrite negbK=>H
    | [ |- context[_ && false]   ] => rewrite !Bool.andb_false_r
    | [ |- context[_ && true ]   ] => rewrite !Bool.andb_true_r
    | [ |- context[_ || false]   ] => rewrite !Bool.orb_false_r
    | [ |- context[_ || true ]   ] => rewrite !Bool.orb_true_r
    | [ |- context[ ~~ (_ && _)] ] => rewrite negb_and
    | [ |- context[ ~~ (_ || _)] ] => rewrite negb_or
    | [ |- context[ ~~ ~~ _]    ] => rewrite negbK
    | [ |- context[ ?k == ?k ]    ] => rewrite eq_refl
    | [ H1: is_true (?b), H2: is_true (~~ (?b)) |- _ ] => move: H1 H2=>->//
    | [ H1: is_true (?b), H2: ?b = false |- _ ] => move: H1 H2=>->//
    | [ H: is_true ?D |- is_true ?D ] => easy
    | [ |- _ ] => idtac
    end=>/=//.

  Ltac rw_impl :=
    do ! rw_step =>/=.

  Ltac crush_def :=
    do ! (match goal with
          | [ |- is_true (def ?D) -> _ ] => let H := fresh in move=>H
          | [ H: is_true (~~ def ?D) |- _]                  => move: H; move=>/negPf-H; try rewrite H
          | [ H: context[def(subst_env _ _ _)] |- _]        => move: H; rewrite !def_substb /can_subst => H; try rewrite H
          | [ H: context[_ \in dom (subst_env _ _ _)] |- _] => move: H; rewrite !dom_substb /can_subst => H; try rewrite H
          | [ H: context[_ \in dom (add _ _ _)] |- _]       => move: H; rewrite !in_addb => H; try rewrite H
          | [ H: context[def(add _ _ _)] |- _]              => move: H; rewrite !def_addb => H; try rewrite H
          | [ H: context[def(rem _ _)] |- _]                => move: H; rewrite !def_rem => H; try rewrite H
          | [ H: context[_ \in dom (rem _ _)] |- _]         => move: H; rewrite !in_dom_rem => H; try rewrite H
          | _ => idtac
          end=>/=; rw_step).

  Lemma def_subst_add k k' c T D :
    def (subst_env k k' (add c T D)) ->
    def (subst_env k k' D).
  Proof. crush_def. Qed.

  Lemma def_subst_swap k k' D D' :
    (forall k, k \in dom D' -> k \in dom D) ->
    (def D -> def D') ->
    def (subst_env k k' D) ->
    def (subst_env k k' D').
  Proof.
    move=> Sub Def; rewrite !def_substb /can_subst=>/andP-[/Def-{Def}->]/=.
    have Sub' : forall x, x \notin dom D -> x \notin dom D'
        by move=> x0; apply: contraNN; apply: Sub.
    move=> /orP-[/orP-[->//|/Sub'->]|/Sub'->];
             by rewrite Bool.orb_true_r.
  Qed.

  Lemma subst_envK' k k' D : k \notin dom D -> subst_env k k' D = D.
  Proof. by rewrite /subst_env; case: domP=>//->. Qed.

  Lemma def_cansubst k k' D :
    def (subst_env k k' D) -> can_subst k k' D.
  Proof. by rewrite def_substb=>/andP-[]. Qed.

  Lemma sub_dom_add k T D :
    k \notin dom D ->
    forall x, x \in dom D -> x \in dom (add k T D).
  Proof. by move=> n_in x; rewrite !in_addb n_in orbC =>->. Qed.

  Lemma dom_add_swap k T T' D D' :
    k \notin dom D' -> def D' ->
    forall x, (x \in dom D -> x \in dom D') ->
    x \in dom (add k T D) -> x \in dom (add k T' D').
  Proof.
    move=> n_in Def x Sub; rewrite !in_addb.
    rewrite n_in Def =>/andP-[_ /orP-[/andP-[_->]|/Sub->]]//.
    by rewrite orbC.
  Qed.

  Lemma dom_subst_swap k k' D D' :
    (can_subst k k' D' -> can_subst k k' D) ->
    (forall x, x \in dom D' -> x \in dom D) ->
    forall x, x \in dom (subst_env k k' D') ->
                    x \in dom (subst_env k k' D).
  Proof.
    move=> Subst H x Hdom; move: (in_dom_def Hdom)=>Hdef; move: Hdef Hdom.
    rewrite def_substb =>/andP-[_ /Subst-{Subst}].
    have H' : forall x, x \notin dom D -> x \notin dom D'
        by move=> x0; apply: contraNN; apply: H.
    rewrite /can_subst=>/orP-[/orP-[/eqP->|kD]|].
      by rewrite !subst_envK=>/H.
      by move: (H' _ kD)=>kD'; rewrite !subst_envK'// =>/H.
    rewrite !dom_substb /can_subst=>k'D; move: (H' _ k'D) =>k'D'.
    rewrite k'D k'D' !Bool.orb_true_r/=.
    by move=>/orP-[/andP-[->/H->//]|/andP-[->/H->]]; rewrite orbC.
  Qed.

  Lemma cansubst_add k k' k0 T T' D :
    can_subst k k' (add k0 T D) -> can_subst k k' (add k0 T' D).
  Proof.
    by rewrite /can_subst !in_addb !negb_and !negbK !negb_or !negb_and.
  Qed.

  Lemma cansubst_add_next k k' x T D :
    x \notin dom D ->
    can_subst k k' (add x T D) -> can_subst k k' D.
  Proof.
    rewrite /can_subst !in_addb !negb_and !negb_or !negb_and !negbK => xD.
    by move=>/orP-[/orP-[->|/orP-[|/andP-[_->]]]|/orP-[|/andP-[_->]]]//;
       rewrite ?(negPf xD) // Bool.orb_true_r.
  Qed.

  Lemma fun_match_option A B C (f : B -> C) (x : option A) (g : A -> B) (z : B) :
    f match x with
      | Some v => g v
      | None   => z
      end = match x with
            | Some v => f (g v)
            | None => f z
            end.
  Proof. by case: x. Qed.

  Lemma substC k0 k0' k1 k1' D :
    k1' != k0 -> k0' != k1 -> k0 != k1 ->
    subst_env k0 k0' (subst_env k1 k1' D) =
    subst_env k1 k1' (subst_env k0 k0' D).
  Proof.
    case: (boolP (k1' == k1))=>[/eqP->|]; first by rewrite !subst_envK.
    case: (boolP (k0' == k0))=>[/eqP->|]; first by rewrite !subst_envK.
    move=> kk0 kk1 k1'0 k0'1 k01.
    rewrite [subst_env k1 k1' _]/subst_env fun_match_option.
    rewrite [subst_env k1 k1' _ in RHS]/subst_env.
    case: (boolP (def (subst_env k0 k0' D))); last by
        case: defP=>///=H; rewrite H/=; case: (domP k1 D)=>[v|]H';
        rewrite H' // -neq_add_substC// rem_substC// H.
    move=> Hdef.
    rewrite look_subst // eq_sym (negPf k0'1) look_rem eq_sym (negPf k01) if_same.
    case: (domP k1 D)=>[v|]H;rewrite H//.
    by rewrite -rem_substC // neq_add_substC.
  Qed.

  Lemma subst_union c c' D1 D2 :
    subst_env c c' (D1 \:/ D2) = (subst_env c c' D1 \:/ subst_env c c' D2).
  Proof.
    case: (boolP (c' == c)) => [/eqP->|neq]; first by rewrite !subst_envK.
    case: D1=>// f1; rewrite [in RHS]unionC unionC; case: D2=>// f2.
    rewrite [in RHS]unionC unionC /subst_env/look [in LHS]/union; case: ifP=>ds.
    + rewrite fnd_fcat; case: suppP=>[v|]-H; rewrite H//.
      - have Hf1: fnd c f1 = None by apply/fnd_supp; (* FIXME: add lemma in finmap *)
          move: H => /eqP/in_supp_fnd-H; rewrite (fnd_disj_none H) // disjC.
        rewrite Hf1 /union/rem [in RHS]/add /dom supp_rem !inE neq /=.
        rewrite [in LHS]/add /dom/upd !supp_rem !inE neq /= supp_fcat !inE orbC.
        case: suppP => [v'|]-Hf2' ///=; case: suppP => [v'|]-Hf1'.
        * rewrite ifF // (rwP negPf); apply: contraT; rewrite negbK.
          move: Hf1'=>/eqP/in_supp_fnd/fnd_disj_none-Hf /(Hf _) {Hf}.
          by rewrite supp_ins !inE eq_refl.
        * move: Hf1 => /eqP/notin_supp_fnd=>Hf1.
          move: Hf1' => /eqP/notin_supp_fnd=>Hf1'.
          rewrite ifT; first by rewrite fcat_sins fcat_srem //.
          by rewrite disj_ins (disj_rem _ ds) andbC /=.
      - case: (suppP c f1) => [v|]-Hf1; rewrite Hf1//; last by rewrite /union ds.
        rewrite /union /add/rem/dom !supp_rem !inE neq supp_fcat !inE /= .
        case: suppP=>[v'|]-Hf1'/=//; case: suppP => [v'|]-Hf2' ///=.
        * rewrite ifF // (rwP negPf); apply: contraT; rewrite negbK.
          move=> /(fnd_disj_none _)-Hf; move: (Hf c') => {Hf}.
          rewrite supp_ins !inE eq_refl /= => /(_ is_true_true)/fnd_supp.
          by rewrite Hf2'.
        * move: H => /eqP/notin_supp_fnd=>Hf2.
          move: Hf2' => /eqP/notin_supp_fnd=>Hf2'.
          rewrite ifT; first by rewrite fcat_inss // fcat_rems.
          move: ds; rewrite disjC => ds.
          by rewrite disjC disj_ins (disj_rem _ ds) Hf2'.
    + case: (suppP c f1)=> [v1|]-Hf1; rewrite Hf1 //;
         case: (suppP c f2)=> [v2|]-Hf2; rewrite Hf2 //.
      - rewrite add_union unionC add_union.
        by apply/eqP; rewrite eq_sym -/(undef _) add_twice.
      - move: Hf2 => /eqP/notin_supp_fnd-Hf2.
        by rewrite add_union /rem /union ifF // disjC disj_remE // disjC.
      - move: Hf1 => /eqP/notin_supp_fnd-Hf1.
        by rewrite unionC add_union unionC /rem/union ifF// disj_remE// disjC.
      - by rewrite /union ds.
  Qed. (* FIXME: the above should come much easier ... *)

End Environment.

Notation "A /:\ B" := (intersection A B) (at level 80, right associativity). (* : env_scope. *)
Notation "A --- B" := (difference A B)  (at level 80, right associativity). (* : env_scope. *)
Notation "A \:/ B" := (union A B) (at level 80, right associativity). (* : env_scope. *)

Arguments env [K V]. (* declare K and V implicit *)
Arguments nil [K V].
Arguments undef_env [K V].

(* FIXME: avoid ltac repetition: it is not exported inside a section! *)
Ltac rw_step :=
  match goal with
  | [ H: (is_true (?L || ?R)) |- _ ] => move: H; move=>/orP-[H|H]//
  | [ H: (is_true (?L && ?R)) |- _ ] =>
    let H1 := fresh H in let H2 := fresh H in move: H; move=>/andP-[H1 H2]//
  | [ H: is_true (?k1 == ?k2) |- _ ] => move: H; move=>/eqP-H; try rewrite H
  | [ H: is_true (?k1 != ?k2) |- _ ] => move: H; move=>/negPf-H; try rewrite H
  | [ H: is_true (?k != ?k)   |- _ ] => move: H; rewrite eq_refl=>H //
  | [ H: is_true (_ \notin _) |- _ ] => move: H; move=>/negPf-H; try rewrite H
  | [ H: is_true (_ \in _)    |- _ ] => rewrite H
  | [ H: context[_ && false]  |- _ ] => move: H; rewrite !Bool.andb_false_r=>H
  | [ H: context[_ && true ]  |- _ ] => move: H; rewrite !Bool.andb_true_r=>H
  | [ H: context[_ || false]  |- _ ] => move: H; rewrite !Bool.orb_false_r=>H
  | [ H: context[_ || true ]  |- _ ] => move: H; rewrite !Bool.orb_true_r=>H
  | [ H: context[ ~~ (_ && _)]    |- _ ] => move: H; rewrite negb_and=>H
  | [ H: context[ ~~ (_ || _)]    |- _ ] => move: H; rewrite negb_or=>H
  | [ H: context[ ~~ ~~ _]     |- _] => move: H; rewrite negbK=>H
  | [ |- context[_ && false]   ] => rewrite !Bool.andb_false_r
  | [ |- context[_ && true ]   ] => rewrite !Bool.andb_true_r
  | [ |- context[_ || false]   ] => rewrite !Bool.orb_false_r
  | [ |- context[_ || true ]   ] => rewrite !Bool.orb_true_r
  | [ |- context[ ~~ (_ && _)] ] => rewrite negb_and
  | [ |- context[ ~~ (_ || _)] ] => rewrite negb_or
  | [ |- context[ ~~ ~~ _]    ] => rewrite negbK
  | [ |- context[ ?k == ?k ]    ] => rewrite eq_refl
  | [ H: _ = false |- _ ] => rewrite H
  | [ H: forall _, (_ = _) |- _ ] => rewrite H
  | [ H: forall _, is_true (_ != _) |- _ ] => rewrite (negPf (H _))
  | [ H1: is_true (?b), H2: is_true (~~ (?b)) |- _ ] => move: H1 H2=>->//
  | [ H1: ?x = ?y, H2: (?x == ?y) = false |- _ ] => move: H1 H2=>->//
  | [ H1: ?x = ?y, H2: (?y == ?x) = false |- _ ] => move: H1 H2; rewrite eq_sym =>->//
  | [ H1: is_true (?b), H2: ?b = false |- _ ] => move: H1 H2=>->//
  | [ H: is_true ?D |- is_true ?D ] => easy
  | [ |- _ ] => idtac
  end=>/=//.

Ltac rw_impl :=
  do ! rw_step =>/=.

Ltac rw_def := do ! rewrite ?def_substb
                  ?dom_substb
                  ?in_addb
                  ?def_addb
                  ?def_rem
                  ?in_dom_rem.

Ltac crush_def :=
  do ! (match goal with
        | [ |- is_true (def ?D) -> _ ] => let H := fresh in move=>H; try rewrite H
        | [ H: is_true (~~ def ?D) |- _]                  => move: H; move=>/negPf-H; try rewrite H
        | [ H: context[def(subst_env _ _ _)] |- _]        => move: H; rewrite !def_substb => H; try rewrite H
        | [ H: context[_ \in dom (subst_env _ _ _)] |- _] => move: H; rewrite !dom_substb => H; try rewrite H
        | [ H: context[_ \in dom (add _ _ _)] |- _]       => move: H; rewrite !in_addb => H; try rewrite H
        | [ H: context[def(add _ _ _)] |- _]              => move: H; rewrite !def_addb => H; try rewrite H
        | [ H: context[def(rem _ _)] |- _]                => move: H; rewrite !def_rem => H; try rewrite H
        | [ H: context[_ \in dom (rem _ _)] |- _]         => move: H; rewrite !in_dom_rem => H; try rewrite H
        | [ H: is_true (def _) |- _]        => rewrite H
        | [ |- context[def(subst_env _ _ _)] ]        => rw_def
        | [ |- context[_ \in dom (subst_env _ _ _)] ] => rw_def
        | [ |- context[_ \in dom (add _ _ _)] ]       => rw_def
        | [ |- context[def(add _ _ _)] ]              => rw_def
        | [ |- context[def(rem _ _)] ]                => rw_def
        | [ |- context[_ \in dom (rem _ _)] ]         => rw_def
        | _ => idtac
        end=>/=; rw_step).