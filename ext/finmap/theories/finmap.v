(*
    Copyright (C) 2012  G. Gonthier, B. Ziliani, A. Nanevski, D. Dreyer

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

From mathcomp.ssreflect Require Import ssreflect ssrbool eqtype ssrfun seq path.
Require Import ordtype.
Require Import prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Def.
Variables (K : ordType) (V : Type).

Definition key (x : K * V) := x.1.
Definition value (x : K * V) := x.2.
Definition predk k := preim key (pred1 k).
Definition predCk k := preim key (predC1 k).

Structure finMap : Type := FinMap {
  seq_of : seq (K * V);
  _ : sorted ord (map key seq_of)}.

Definition finMap_for of phant (K -> V) := finMap.

Identity Coercion finMap_for_finMap : finMap_for >-> finMap.
End Def.

Notation "{ 'finMap' fT }" := (finMap_for (Phant fT))
  (at level 0, format "{ 'finMap'  '[hv' fT ']' }") : type_scope.

Prenex Implicits key value predk predCk seq_of.

Section Ops.
Variables (K : ordType) (V : Type).
Notation fmap := (finMap K V).
Notation key := (@key K V).
Notation predk := (@predk K V).
Notation predCk := (@predCk K V).

Lemma fmapE (s1 s2 : fmap) : s1 = s2 <-> seq_of s1 = seq_of s2.
Proof.
split=>[->|] //.
move: s1 s2 => [s1 H1] [s2 H2] /= H.
by rewrite H in H1 H2 *; rewrite (bool_irrelevance H1 H2).
Qed.

Definition sorted_nil : sorted ord (map key [::]). Proof. by []. Defined.
Definition nil := FinMap sorted_nil.

Definition fnd k (s : fmap) :=
  if (filter (predk k) (seq_of s)) is (_, v):: _
  then Some v else None.

Fixpoint ins' (k : K) (v : V) (s : seq (K * V)) {struct s} : seq (K * V) :=
  if s is (k1, v1)::s1 then
    if ord k k1 then (k, v)::s else
      if k == k1 then (k, v)::s1 else (k1, v1)::(ins' k v s1)
  else [:: (k, v)].

Lemma path_ins' s k1 k2 v :
        ord k1 k2 -> path ord k1 (map key s) ->
          path ord k1 (map key (ins' k2 v s)).
Proof.
elim: s k1 k2 v=>[|[k' v'] s IH] k1 k2 v H1 /=; first by rewrite H1.
case/andP=>H2 H3; case: ifP=>/= H4; first by rewrite H1 H3 H4.
case: ifP=>H5 /=; first by rewrite H1 (eqP H5) H3.
by rewrite H2 IH //; move: (total k2 k'); rewrite H4 H5.
Qed.

Lemma sorted_ins' s k v :
        sorted ord (map key s) -> sorted ord (map key (ins' k v s)).
Proof.
case: s=>// [[k' v']] s /= H.
case: ifP=>//= H1; first by rewrite H H1.
case: ifP=>//= H2; first by rewrite (eqP H2).
by rewrite path_ins' //; move: (total k k'); rewrite H1 H2.
Qed.

Definition ins k v s := let: FinMap s' p' := s in FinMap (sorted_ins' k v p').

Lemma sorted_filter k s :
        sorted ord (map key s) -> sorted ord (map key (filter (predCk k) s)).
Proof. by move=>H; rewrite -filter_map sorted_filter //; apply: trans. Qed.

Definition rem k s := let: FinMap s' p' := s in FinMap (sorted_filter k p').

Definition supp s := map key (seq_of s).
End Ops.

Prenex Implicits fnd ins rem supp.

Section Laws.
Variables (K : ordType) (V : Type).
Notation fmap := (finMap K V).
Notation nil := (nil K V).

Lemma ord_path (x y : K) s : ord x y -> path ord y s -> path ord x s.
Proof.
elim: s x y=>[|k s IH] x y //=.
by move=>H1; case/andP=>H2 ->; rewrite (trans H1 H2).
Qed.

Lemma last_ins' (x : K) (v : V) s :
        path ord x (map key s) -> ins' x v s = (x, v) :: s.
Proof. by elim: s=>[|[k1 v1] s IH] //=; case: ifP. Qed.

Lemma notin_path (x : K) s : path ord x s -> x \notin s.
Proof.
elim: s=>[|k s IH] //=.
rewrite inE negb_or; case/andP=>T1 T2; case: eqP=>H /=.
- by rewrite H irr in T1.
by apply: IH; apply: ord_path T2.
Qed.

Lemma path_supp_ord (s : seq K) k :
        path ord k s -> forall m, m \in s -> ord k m.
Proof.
  elim: s =>k' s IH // /= /andP-[ord1 path1] m.
  rewrite in_cons => /orP-[/eqP-> | m_in_s] //.
  by apply: IH => //; apply: (ord_path ord1).
Qed.

Lemma notin_filter (x : K) s :
        x \notin (map key s) -> filter (predk V x) s = [::].
Proof.
elim: s=>[|[k v] s IH] //=.
rewrite inE negb_or; case/andP=>H1 H2.
by rewrite eq_sym (negbTE H1); apply: IH.
Qed.

Lemma fmapP (s1 s2 : fmap) : (forall k, fnd k s1 = fnd k s2) -> s1 = s2.
Proof.
rewrite /fnd; move: s1 s2 => [s1 P1][s2 P2] H; rewrite fmapE /=.
elim: s1 P1 s2 P2 H=>[|[k v] s1 IH] /= P1.
- by case=>[|[k2 v2] s2 P2] //=; move/(_ k2); rewrite eq_refl.
have S1: sorted ord (map key s1) by apply: path_sorted P1.
case=>[|[k2 v2] s2] /= P2; first by move/(_ k); rewrite eq_refl.
have S2: sorted ord (map key s2) by apply: path_sorted P2.
move: (IH S1 s2 S2)=>{IH} /= IH H.
move: (notin_path P1) (notin_path P2)=>N1 N2.
case E: (k == k2).
- rewrite -{k2 E}(eqP E) in P2 H N2 *.
  move: (H k); rewrite eq_refl=>[[E2]]; rewrite -E2 {v2 E2} in H *.
  rewrite IH // => k'.
  case E: (k == k'); first by rewrite -(eqP E) !notin_filter.
  by move: (H k'); rewrite E.
move: (H k); rewrite eq_refl eq_sym E notin_filter //.
move: (total k k2); rewrite E /=; case/orP=>L1.
- by apply: notin_path; apply: ord_path P2.
move: (H k2); rewrite E eq_refl notin_filter //.
by apply: notin_path; apply: ord_path P1.
Qed.

Lemma predkN (k1 k2 : K) : predI (predk V k1) (predCk V k2) =1
                           if k1 == k2 then pred0 else predk V k1.
Proof.
by move=>x; case: ifP=>H /=; [|case: eqP=>//->]; rewrite ?(eqP H) ?andbN ?H.
Qed.

CoInductive supp_spec x (s : fmap) : bool -> Type :=
| supp_spec_some v of fnd x s = Some v : supp_spec x s true
| supp_spec_none of fnd x s = None : supp_spec x s false.

Lemma suppP x (s : fmap) : supp_spec x s (x \in supp s).
Proof.
move E: (x \in supp s)=>b; case: b E; move/idP; last first.
- move=>H; apply: supp_spec_none.
  case E: (fnd _ _)=>[v|] //; case: H.
  rewrite /supp /fnd in E *; case: s E=>/=.
  elim=>[|[y w] s IH] H1 //=.
  case: ifP=>H; first by rewrite (eqP H) inE eq_refl.
  rewrite -topredE /= eq_sym H; apply: IH.
  by apply: path_sorted H1.
case: s; elim=>[|[y w] s IH] /= H1 //; rewrite /supp /= inE in IH *.
case: eqP=>[-> _|H] //=.
- by apply: (@supp_spec_some _ _ w); rewrite /fnd /= eq_refl.
move: (path_sorted H1)=>H1'; move/(IH H1'); case=>[v H2|H2];
[apply: (@supp_spec_some _ _ v) | apply: supp_spec_none];
by rewrite /fnd /=; case: eqP H=>// ->.
Qed.

Lemma supp_nil : supp nil = [::]. Proof. by []. Qed.

Lemma supp_nilE (s : fmap) : (supp s = [::]) <-> (s = nil).
Proof. by split=>[|-> //]; case: s; case=>// H; rewrite fmapE. Qed.

Lemma supp_rem k (s : fmap) :
        supp (rem k s) =i predI (predC1 k) (mem (supp s)).
Proof.
case: s => s H1 x; rewrite /supp inE /=.
by case H2: (x == k)=>/=; rewrite -filter_map mem_filter /= H2.
Qed.

Lemma supp_ins k v (s : fmap) :
        supp (ins k v s) =i predU (pred1 k) (mem (supp s)).
Proof.
case: s => s H x; rewrite /supp inE /=.
elim: s x k v H=>[|[k1 v1] s IH] //= x k v H.
case: ifP=>H1 /=; first by rewrite inE.
case: ifP=>H2 /=; first by rewrite !inE (eqP H2) orbA orbb.
by rewrite !inE (IH _ _ _ (path_sorted H)) orbCA.
Qed.

Lemma fnd_empty k : fnd k nil = None. Proof. by []. Qed.

Lemma fnd_rem k1 k2 (s : fmap) :
        fnd k1 (rem k2 s) = if k1 == k2 then None else fnd k1 s.
Proof.
case: s => s H; rewrite /fnd -filter_predI (eq_filter (predkN k1 k2)).
by case: eqP=>//; rewrite filter_pred0.
Qed.

Lemma fnd_ins k1 k2 v (s : fmap) :
        fnd k1 (ins k2 v s) = if k1 == k2 then Some v else fnd k1 s.
Proof.
case: s => s H; rewrite /fnd /=.
elim: s k1 k2 v H=>[|[k' v'] s IH] //= k1 k2 v H.
- by case: ifP=>H1; [rewrite (eqP H1) eq_refl | rewrite eq_sym H1].
case: ifP=>H1 /=.
- by case: ifP=>H2; [rewrite (eqP H2) eq_refl | rewrite (eq_sym k1) H2].
case: ifP=>H2 /=.
- rewrite (eqP H2).
  by case: ifP=>H3; [rewrite (eqP H3) eq_refl | rewrite eq_sym H3].
case: ifP=>H3; first by rewrite -(eqP H3) eq_sym H2.
by apply: IH; apply: path_sorted H.
Qed.

Lemma ins_rem k1 k2 v (s : fmap) :
        ins k1 v (rem k2 s) =
        if k1 == k2 then ins k1 v s else rem k2 (ins k1 v s).
Proof.
move: k1 k2 v s.
have L3: forall (x : K) s,
  path ord x (map key s) -> filter (predCk V x) s = s.
- move=>x t; move/notin_path; elim: t=>[|[k3 v3] t IH] //=.
  rewrite inE negb_or; case/andP=>T1 T2.
  by rewrite eq_sym T1 IH.
have L5: forall (x : K) (v : V) s,
  sorted ord (map key s) -> ins' x v (filter (predCk V x) s) = ins' x v s.
- move=>x v s; elim: s x v=>[|[k' v'] s IH] x v //= H.
  case H1: (ord x k').
  - case H2: (k' == x)=>/=; first by rewrite (eqP H2) irr in H1.
    by rewrite H1 L3 //; apply: ord_path H1 H.
  case H2: (k' == x)=>/=.
  - rewrite (eqP H2) eq_refl in H *.
    by rewrite L3 //; apply: last_ins' H.
  rewrite eq_sym H2 H1 IH //.
  by apply: path_sorted H.
move=>k1 k2 v [s H].
case: ifP=>H1; rewrite /ins /rem fmapE /=.
- rewrite {k1 H1}(eqP H1).
  elim: s k2 v H=>[|[k' v'] s IH] //= k2 v H.
  case H1: (k' == k2)=>/=.
  - rewrite eq_sym H1 (eqP H1) irr in H *.
    by rewrite L3 // last_ins'.
  rewrite eq_sym H1; case: ifP=>H3.
  - by rewrite L3 //; apply: ord_path H3 H.
  by rewrite L5 //; apply: path_sorted H.
elim: s k1 k2 H1 H=>[|[k' v'] s IH] //= k1 k2 H1 H; first by rewrite H1.
case H2: (k' == k2)=>/=.
- rewrite (eqP H2) in H *; rewrite H1.
  case H3: (ord k1 k2)=>/=.
  - by rewrite H1 eq_refl /= last_ins' // L3 //; apply: ord_path H.
  by rewrite eq_refl /= IH //; apply: path_sorted H.
case H3: (ord k1 k')=>/=; first by rewrite H1 H2.
case H4: (k1 == k')=>/=; first by rewrite H1.
by rewrite H2 IH //; apply: path_sorted H.
Qed.

Lemma ins_ins k1 k2 v1 v2 (s : fmap) :
        ins k1 v1 (ins k2 v2 s) = if k1 == k2 then ins k1 v1 s
                                  else ins k2 v2 (ins k1 v1 s).
Proof.
rewrite /ins; case: s => s H; case H1: (k1 == k2); rewrite fmapE /=.
- rewrite (eqP H1) {H1}.
  elim: s H k2 v1 v2=>[|[k3 v3] s IH] /= H k2 v1 v2;
    first by rewrite irr eq_refl.
  case: (totalP k2 k3)=>H1 /=; rewrite ?irr ?eq_refl //.
  case: (totalP k2 k3) H1=>H2 _ //.
  by rewrite IH //; apply: path_sorted H.
elim: s H k1 k2 H1 v1 v2=>[|[k3 v3] s IH] H k1 k2 H1 v1 v2 /=.
- rewrite H1 eq_sym H1.
  by case: (totalP k1 k2) H1=>H2 H1.
case: (totalP k2 k3)=>H2 /=.
- case: (totalP k1 k2) (H1)=>H3 _ //=; last first.
  - by case: (totalP k1 k3)=>//= H4; rewrite ?H2 ?H3.
  case: (totalP k1 k3)=>H4 /=.
  - case: (totalP k2 k1) H3=>//= H3.
    by case: (totalP k2 k3) H2=>//=.
  - rewrite (eqP H4) in H3.
    by case: (totalP k2 k3) H2 H3.
  by case: (totalP k1 k3) (trans H3 H2) H4.
- rewrite -(eqP H2) {H2} (H1).
  case: (totalP k1 k2) (H1)=>//= H2 _; rewrite ?irr ?eq_refl //.
  rewrite eq_sym H1.
  by case: (totalP k2 k1) H1 H2.
case: (totalP k1 k3)=>H3 /=.
- rewrite eq_sym H1.
  case: (totalP k2 k1) H1 (trans H3 H2)=>//.
  by case: (totalP k2 k3) H2=>//=.
- rewrite (eqP H3).
  by case: (totalP k2 k3) H2.
case: (totalP k2 k3)=>H4 /=.
- by move: (trans H4 H2); rewrite irr.
- by rewrite (eqP H4) irr in H2.
by rewrite IH //; apply: path_sorted H.
Qed.

Lemma rem_empty k : rem k nil = nil.
Proof. by rewrite fmapE. Qed.

Lemma rem_rem k1 k2 (s : fmap) :
        rem k1 (rem k2 s) = if k1 == k2 then rem k1 s else rem k2 (rem k1 s).
Proof.
rewrite /rem; case: s => s H /=.
case H1: (k1 == k2); rewrite fmapE /= -!filter_predI; apply: eq_filter=>x /=.
- by rewrite (eqP H1) andbb.
by rewrite andbC.
Qed.

Lemma rem_ins k1 k2 v (s : fmap) :
        rem k1 (ins k2 v s) =
        if k1 == k2 then rem k1 s else ins k2 v (rem k1 s).
Proof.
rewrite /rem; case: s => s H /=; case H1: (k1 == k2); rewrite /= fmapE /=.
- rewrite (eqP H1) {H1}.
  elim: s k2 H=>[|[k3 v3] s IH] k2 /= H; rewrite ?eq_refl 1?eq_sym //.
  case: (totalP k3 k2)=>H1 /=; rewrite ?eq_refl //=;
  case: (totalP k3 k2) H1=>//= H1 _.
  by rewrite IH //; apply: path_sorted H.
elim: s k1 k2 H1 H=>[|[k3 v3] s IH] k1 k2 H1 /= H; first by rewrite eq_sym H1.
case: (totalP k2 k3)=>H2 /=.
- rewrite eq_sym H1 /=.
  case: (totalP k3 k1)=>H3 /=; case: (totalP k2 k3) (H2)=>//=.
  rewrite -(eqP H3) in H1 *.
  rewrite -IH //; last by apply: path_sorted H.
  rewrite last_ins' /= 1?eq_sym ?H1 //.
  by apply: ord_path H.
- by move: H1; rewrite (eqP H2) /= eq_sym => -> /=; rewrite irr eq_refl.
case: (totalP k3 k1)=>H3 /=.
- case: (totalP k2 k3) H2=>//= H2 _.
  by rewrite IH //; apply: path_sorted H.
- rewrite -(eqP H3) in H1 *.
  by rewrite IH //; apply: path_sorted H.
case: (totalP k2 k3) H2=>//= H2 _.
by rewrite IH //; apply: path_sorted H.
Qed.

Lemma rem_supp k (s : fmap) :
        k \notin supp s -> rem k s = s.
Proof.
case: s => s H1; rewrite /supp !fmapE /= => H2.
elim: s H1 H2=>[|[k1 v1] s1 IH] //=; move/path_sorted=>H1.
rewrite inE negb_or; case/andP=>H2; move/(IH H1)=>H3.
by rewrite eq_sym H2 H3.
Qed.

Lemma fnd_supp k (s : fmap) :
        k \notin supp s -> fnd k s = None.
Proof. by case: suppP. Qed.

Lemma fnd_supp_in k (s : fmap) :
        k \in supp s -> exists v, fnd k s = Some v.
Proof. by case: suppP=>[v|]; [exists v|]. Qed.

Lemma cancel_ins k v (s1 s2 : fmap) :
       k \notin (supp s1) -> k \notin (supp s2) ->
         ins k v s1 = ins k v s2 -> s1 = s2.
Proof.
move: s1 s2=>[s1 p1][s2 p2]; rewrite !fmapE /supp /= {p1 p2}.
elim: s1 k v s2=>[k v s2| [k1 v1] s1 IH1 k v s2] /=.
- case: s2=>[| [k2 v2] s2] //= _.
  rewrite inE negb_or; case/andP=>H1 _; case: ifP=>// _.
  by rewrite (negbTE H1); case=>E; rewrite E eq_refl in H1.
rewrite inE negb_or; case/andP=>H1 H2 H3.
case: ifP=>H4; case: s2 H3=>[| [k2 v2] s2] //=.
- rewrite inE negb_or; case/andP=>H5 H6.
  case: ifP=>H7; first by case=>->->->.
  by rewrite (negbTE H5); case=>E; rewrite E eq_refl in H5.
- by rewrite (negbTE H1)=>_; case=>E; rewrite E eq_refl in H1.
rewrite inE negb_or (negbTE H1); case/andP=>H5 H6.
rewrite (negbTE H5); case: ifP=>H7 /=.
- by case=>E; rewrite E eq_refl in H1.
by case=>->-> H; congr (_ :: _); apply: IH1 H.
Qed.

Lemma ins_consE (k : K) (v : V) s : exists k' v' s', ins' k v s = (k',v')::s'.
Proof.
  case: s => [| [k0 v0] s2]/= //; first by exists k, v, [::].
  by case: (totalP k k0) =>// _; [ exists k, v, ((k0,v0)::s2)
                                 | exists k, v, s2
                                 | exists k0, v0, (ins' k v s2) ].
Qed.

Lemma cancel_ins' k v1 v2 (s1 s2 : fmap) :
         ins k v1 s1 = ins k v2 s2 -> v1 = v2.
Proof.
move: s1 s2=>[s1 p1][s2 p2]; rewrite !fmapE /supp /= {p1 p2}.
elim: s1 k v1 s2 => [k v1| [k' v'] s1 IH k v1].
- case=>[[]//|[k' v'] s2] /=.
  case: (totalP k k') =>//; first by move /eqP=>-> [].
  by move: (ins_consE k v2 s2) =>[k'' [v'' [s'->]]].
- case=>// [|[k'' v''] s2]/=.
  + case: (totalP k k')=>//; first by move => _ [].
    by move: (ins_consE k v1 s1) => [k'' [v'' [s''->]]].
  + case: (totalP k k') => kk'.
    * by case: (totalP k k'') => kk''; move=>[] e //; move: e (irr k'') kk''=>->->.
    * by case: (totalP k k'') => kk''; move=>[] e //; move: e (irr k'') kk''=>->->.
    * by case: (totalP k k''); move=> _ [] eq; [ move: eq (irr k') kk'=>->->
                                               | move: eq (irr k') kk'=>->->
                                               | move=> _ /IH ].
Qed.

End Laws.

Section Append.
Variable (K : ordType) (V : Type).
Notation fmap := (finMap K V).
Notation nil := (nil K V).

Lemma seqof_ins k v (s : fmap) :
        path ord k (supp s) -> seq_of (ins k v s) = (k, v) :: seq_of s.
Proof. by case: s; elim=>[|[k1 v1] s IH] //= _; case/andP=>->. Qed.

Lemma path_supp_ins k1 k v (s : fmap) :
        ord k1 k -> path ord k1 (supp s) -> path ord k1 (supp (ins k v s)).
Proof.
case: s=>s p.
elim: s p k1 k v=>[| [k2 v2] s IH] //= p k1 k v H2; first by rewrite H2.
case/andP=>H3 H4.
have H5: path ord k1 (map key s) by apply: ord_path H4.
rewrite /supp /=; case: (totalP k k2)=>H /=.
- by rewrite H2 H H4.
- by rewrite H2 (eqP H) H4.
rewrite H3 /=.
have H6: sorted ord (map key s) by apply: path_sorted H5.
by move: (IH H6 k2 k v H H4); case: s {IH p H4 H5} H6.
Qed.

Lemma path_supp_ins_inv k1 k v (s : fmap) :
        path ord k (supp s) -> path ord k1 (supp (ins k v s)) ->
        ord k1 k && path ord k1 (supp s).
Proof.
case: s=>s p; rewrite /supp /= => H1; rewrite last_ins' //=.
by case/andP=>H2 H3; rewrite H2; apply: ord_path H3.
Qed.

Lemma fmap_ind' (P : fmap -> Prop) :
        P nil -> (forall k v s, path ord k (supp s) -> P s -> P (ins k v s)) ->
        forall s, P s.
Proof.
move=>H1 H2; case; elim=>[|[k v] s IH] /= H.
- by rewrite (_ : FinMap _ = nil); last by rewrite fmapE.
have S: sorted ord (map key s) by apply: path_sorted H.
rewrite (_ : FinMap _ = ins k v (FinMap S)); last by rewrite fmapE /= last_ins'.
by apply: H2.
Qed.

Fixpoint fcat' (s1 : fmap) (s2 : seq (K * V)) {struct s2} : fmap :=
  if s2 is (k, v)::t then fcat' (ins k v s1) t else s1.

Definition fcat s1 s2 := fcat' s1 (seq_of s2).

Lemma fcat_ins' k v s1 s2 :
        k \notin (map key s2) -> fcat' (ins k v s1) s2 = ins k v (fcat' s1 s2).
Proof.
move=>H; elim: s2 k v s1 H=>[|[k2 v2] s2 IH] k1 v1 s1 //=.
rewrite inE negb_or; case/andP=>H1 H2.
by rewrite -IH // ins_ins eq_sym (negbTE H1).
Qed.

Lemma fcat_nil' s : fcat' nil (seq_of s) = s.
Proof.
elim/fmap_ind': s=>[|k v s L IH] //=.
by rewrite seqof_ins //= (_ : FinMap _ = ins k v nil) //
     fcat_ins' ?notin_path // IH.
Qed.

Lemma fcat0s s : fcat nil s = s. Proof. by apply: fcat_nil'. Qed.
Lemma fcats0 s : fcat s nil = s. Proof. by []. Qed.

Lemma fcat_inss k v s1 s2 :
        k \notin supp s2 -> fcat (ins k v s1) s2 = ins k v (fcat s1 s2).
Proof. by case: s2=>s2 p2 H /=; apply: fcat_ins'. Qed.

Lemma fcat_sins k v s1 s2 :
        fcat s1 (ins k v s2) = ins k v (fcat s1 s2).
Proof.
elim/fmap_ind': s2 k v s1=>[|k1 v1 s1 H1 IH k2 v2 s2] //.
case: (totalP k2 k1)=>//= H2.
- have H: path ord k2 (supp (ins k1 v1 s1)).
  - by apply: (path_supp_ins _ H2); apply: ord_path H1.
  by rewrite {1}/fcat seqof_ins //= fcat_ins' ?notin_path.
- by rewrite IH ins_ins H2 IH ins_ins H2.
have H: path ord k1 (supp (ins k2 v2 s1)) by apply: (path_supp_ins _ H2).
rewrite ins_ins.
case: (totalP k2 k1) H2 => // H2 _.
rewrite {1}/fcat seqof_ins //= fcat_ins' ?notin_path // IH ?notin_path //.
rewrite ins_ins; case: (totalP k2 k1) H2 => // H2 _; congr (ins _ _ _).
by rewrite -/(fcat s2 (ins k2 v2 s1)) IH.
Qed.

Lemma fcat_rems k s1 s2 :
        k \notin supp s2 -> fcat (rem k s1) s2 = rem k (fcat s1 s2).
Proof.
elim/fmap_ind': s2 k s1=>[|k2 v2 s2 H IH] k1 v1.
- by rewrite !fcats0.
rewrite supp_ins inE /= negb_or; case/andP=>H1 H2.
by rewrite fcat_sins IH // ins_rem eq_sym (negbTE H1) -fcat_sins.
Qed.

Lemma fcat_srem k s1 s2 :
        k \notin supp s1 -> fcat s1 (rem k s2) = rem k (fcat s1 s2).
Proof.
elim/fmap_ind': s2 k s1=>[|k2 v2 s2 H IH] k1 s1.
- rewrite rem_empty fcats0.
  elim/fmap_ind': s1=>[|k3 v3 s3 H1 IH]; first by rewrite rem_empty.
  rewrite supp_ins inE /= negb_or.
  case/andP=>H2; move/IH=>E; rewrite {1}E .
  by rewrite ins_rem eq_sym (negbTE H2).
move=>H1; rewrite fcat_sins rem_ins; case: ifP=>E.
- by rewrite rem_ins E IH.
by rewrite rem_ins E -IH // -fcat_sins.
Qed.

Lemma fnd_fcat k s1 s2 :
        fnd k (fcat s1 s2) =
        if k \in supp s2 then fnd k s2 else fnd k s1.
Proof.
elim/fmap_ind': s2 k s1=>[|k2 v2 s2 H IH] k1 s1.
- by rewrite fcats0.
rewrite supp_ins inE /=; case: ifP; last first.
- move/negbT; rewrite negb_or; case/andP=>H1 H2.
  by rewrite fcat_sins fnd_ins (negbTE H1) IH (negbTE H2).
case/orP; first by move/eqP=><-; rewrite fcat_sins !fnd_ins eq_refl.
move=>H1; rewrite fcat_sins !fnd_ins.
by case: ifP=>//; rewrite IH H1.
Qed.

Lemma fnd_fcat' k s1 s2 :
  fnd k (fcat s1 s2) =
  match fnd k s2 with
  | Some v => Some v
  | None   => fnd k s1
  end.
Proof.
  by rewrite fnd_fcat; case: (suppP k s2) =>[v|]-> //.
Qed.

Lemma supp_fcat s1 s2 : supp (fcat s1 s2) =i [predU supp s1 & supp s2].
Proof.
elim/fmap_ind': s2 s1=>[|k v s L IH] s1.
- by rewrite supp_nil fcats0 => x; rewrite inE /= orbF.
rewrite fcat_sins ?notin_path // => x.
rewrite supp_ins !inE /=.
case E: (x == k)=>/=.
- rewrite ?inE !supp_ins ?inE E orbT.
  reflexivity.
rewrite ?inE. rewrite ?supp_ins. rewrite ?inE /=.
rewrite IH. rewrite ?inE /=. rewrite E /=.
reflexivity.
Qed.

End Append.

(* an induction principle for pairs of finite maps with equal support *)

Section FMapInd.
Variables (K : ordType) (V : Type).
Notation fmap := (finMap K V).
Notation nil := (@nil K V).

Lemma supp_eq_ins (s1 s2 : fmap) k1 k2 v1 v2 :
        path ord k1 (supp s1) -> path ord k2 (supp s2) ->
          supp (ins k1 v1 s1) =i supp (ins k2 v2 s2) ->
        k1 = k2 /\ supp s1 =i supp s2.
Proof.
move=>H1 H2 H; move: (H k1) (H k2).
rewrite !supp_ins !inE /= !eq_refl (eq_sym k2).
case: totalP=>/= E; last 1 first.
- by move: H1; move/(ord_path E); move/notin_path; move/negbTE=>->.
- by move: H2; move/(ord_path E); move/notin_path; move/negbTE=>->.
rewrite (eqP E) in H1 H2 H * => _ _; split=>// x; move: (H x).
rewrite !supp_ins !inE /=; case: eqP=>//= -> _.
by rewrite (negbTE (notin_path H1)) (negbTE (notin_path H2)).
Qed.

Lemma fmap_ind2 (P : fmap -> fmap -> Prop) :
        P nil nil ->
        (forall k v1 v2 s1 s2,
           path ord k (supp s1) -> path ord k (supp s2) ->
           P s1 s2 -> P (ins k v1 s1) (ins k v2 s2)) ->
        forall s1 s2, supp s1 =i supp s2 -> P s1 s2.
Proof.
move=>H1 H2; elim/fmap_ind'=>[|k1 v1 s1 T1 IH1];
elim/fmap_ind'=>[|k2 v2 s2 T2 _] //.
- by move/(_ k2); rewrite supp_ins inE /= eq_refl supp_nil.
- by move/(_ k1); rewrite supp_ins inE /= eq_refl supp_nil.
by case/supp_eq_ins=>// E; rewrite -{k2}E in T2 *; move/IH1; apply: H2.
Qed.

End FMapInd.

Section DisjointUnion.
Variable (K : ordType) (V : Type).
Notation fmap := (finMap K V).
Notation nil := (nil K V).

Definition disj (s1 s2 : fmap) :=
  all (predC (fun x => x \in supp s2)) (supp s1).

CoInductive disj_spec (s1 s2 : fmap) : bool -> Type :=
| disj_true of (forall x, x \in supp s1 -> x \notin supp s2) :
    disj_spec s1 s2 true
| disj_false x of x \in supp s1 & x \in supp s2 :
    disj_spec s1 s2 false.

Lemma disjP s1 s2 : disj_spec s1 s2 (disj s1 s2).
Proof.
rewrite /disj; case E: (all _ _).
- by apply: disj_true; case: allP E.
move: E; rewrite all_predC; move/negbFE.
by case: hasPx=>// x H1 H2 _; apply: disj_false H1 H2.
Qed.

Lemma disjC s1 s2 : disj s1 s2 = disj s2 s1.
Proof.
case: disjP; case: disjP=>//.
- by move=>x H1 H2; move/(_ x H2); rewrite H1.
by move=>H1 x H2; move/H1; rewrite H2.
Qed.

Lemma disj_nil (s : fmap) : disj s nil.
Proof. by case: disjP. Qed.

Lemma disj_ins k v (s1 s2 : fmap) :
        disj s1 (ins k v s2) = (k \notin supp s1) && (disj s1 s2).
Proof.
case: disjP=>[H|x H1].
- case E: (k \in supp s1)=>/=.
  - by move: (H _ E); rewrite supp_ins inE /= eq_refl.
  case: disjP=>// x H1 H2.
  by move: (H _ H1); rewrite supp_ins inE /= H2 orbT.
rewrite supp_ins inE /=; case/orP=>[|H2].
- by move/eqP=><-; rewrite H1.
rewrite andbC; case: disjP=>[H|y H3 H4] //=.
by move: (H _ H1); rewrite H2.
Qed.

Lemma disj_rem k (s1 s2 : fmap) :
        disj s1 s2 -> disj s1 (rem k s2).
Proof.
case: disjP=>// H _; case: disjP=>// x; move/H.
by rewrite supp_rem inE /= andbC; move/negbTE=>->.
Qed.

Lemma disj_remE k (s1 s2 : fmap) :
        k \notin supp s1 -> disj s1 (rem k s2) = disj s1 s2.
Proof.
move=>H; case: disjP; case: disjP=>//; last first.
- move=>H1 x; move/H1; rewrite supp_rem inE /= => E.
  by rewrite (negbTE E) andbF.
move=>x H1 H2 H3; move: (H3 x H1) H.
rewrite supp_rem inE /= negb_and H2 orbF negbK.
by move/eqP=><-; rewrite H1.
Qed.

Lemma disj_fcat (s s1 s2 : fmap) :
        disj s (fcat s1 s2) = disj s s1 && disj s s2.
Proof.
elim/fmap_ind': s s1 s2=>[|k v s L IH] s1 s2.
- by rewrite !(disjC nil) !disj_nil.
rewrite !(disjC (ins _ _ _)) !disj_ins supp_fcat inE /= negb_or.
case: (k \in supp s1)=>//=.
case: (k \in supp s2)=>//=; first by rewrite andbF.
by rewrite -!(disjC s) IH.
Qed.

Lemma fcatC (s1 s2 : fmap) : disj s1 s2 -> fcat s1 s2 = fcat s2 s1.
Proof.
rewrite /fcat.
elim/fmap_ind': s2 s1=>[|k v s2 L IH] s1 /=; first by rewrite fcat_nil'.
rewrite disj_ins; case/andP=>D1 D2.
by rewrite fcat_ins' // -IH  // seqof_ins //= -fcat_ins' ?notin_path.
Qed.

Lemma fcatA (s1 s2 s3 : fmap) :
        disj s2 s3 -> fcat (fcat s1 s2) s3 = fcat s1 (fcat s2 s3).
Proof.
move=>H.
elim/fmap_ind': s3 s1 s2 H=>[|k v s3 L IH] s1 s2 /=; first by rewrite !fcats0.
rewrite disj_ins; case/andP=>H1 H2.
by rewrite fcat_sins ?notin_path // IH // fcat_sins ?notin_path // fcat_sins.
Qed.

Lemma fcatAC (s1 s2 s3 : fmap) :
        [&& disj s1 s2, disj s2 s3 & disj s1 s3] ->
        fcat s1 (fcat s2 s3) = fcat s2 (fcat s1 s3).
Proof. by case/and3P=>H1 H2 H3; rewrite -!fcatA // (@fcatC s1 s2). Qed.

Lemma fcatCA (s1 s2 s3 : fmap) :
        [&& disj s1 s2, disj s2 s3 & disj s1 s3] ->
        fcat (fcat s1 s2) s3 = fcat (fcat s1 s3) s2.
Proof.
by case/and3P=>H1 H2 H3; rewrite !fcatA // ?(@fcatC s2 s3) ?(disjC s3).
Qed.

Lemma fcatsK (s s1 s2 : fmap) :
        disj s1 s && disj s2 s -> fcat s1 s = fcat s2 s -> s1 = s2.
Proof.
elim/fmap_ind': s s1 s2=>// k v s.
move/notin_path=>H IH s1 s2; rewrite !disj_ins.
case/andP; case/andP=>H1 H2; case/andP=>H3 H4.
rewrite !fcat_sins // => H5.
apply: IH; first by rewrite H2 H4.
by apply: cancel_ins H5; rewrite supp_fcat negb_or /= ?H1?H3 H.
Qed.

Lemma fcatKs (s s1 s2 : fmap) :
        disj s s1 && disj s s2 -> fcat s s1 = fcat s s2 -> s1 = s2.
Proof.
case/andP=>H1 H2.
rewrite (fcatC H1) (fcatC H2); apply: fcatsK.
by rewrite -!(disjC s) H1 H2.
Qed.
End DisjointUnion.

Section EqType.
Variables (K : ordType) (V : eqType).

Definition feq (s1 s2 : finMap K V) := seq_of s1 == seq_of s2.

Lemma feqP : Equality.axiom feq.
Proof.
move=>s1 s2; rewrite /feq.
case: eqP; first by move/fmapE=>->; apply: ReflectT.
by move=>H; apply: ReflectF; move/fmapE; move/H.
Qed.

Lemma notin_supp_fnd k (f : {finMap K -> V}) :
  fnd k f == None -> k \notin supp f.
Proof.
  by move/eqP=>fnd_None; case: (suppP k f); first by rewrite fnd_None.
Qed.

Lemma in_supp_fnd k (f : {finMap K -> V}) (s : V) :
  fnd k f == Some s -> k \in supp f.
  move/eqP.
  destruct (k \in supp f) eqn: Hkf=>//.
  have H:fnd k f= None.
  {
    apply fnd_supp.
    move:Hkf.
    by rewrite/(_\in_)/(_\notin_)/negb=>->.
  }
  move:H=>->.
  congruence.
Qed.

Canonical Structure fmap_eqMixin := EqMixin feqP.
Canonical Structure fmap_eqType := EqType (finMap K V) fmap_eqMixin.
End EqType.

Section SetOp.
  Variables (K : ordType) (V : eqType).
  Notation fmap := (finMap K V).
  Notation nil := (nil K V).

  Lemma sorted_filter_by_pred (s : seq (K * V)) (p : pred K) :
    sorted ord (map key s) -> sorted ord (map key (filter (preim key p) s)).
  Proof.
      by move => H; rewrite -filter_map path.sorted_filter //; apply: trans.
  Qed.

  Definition filter_by_key (pr : pred K) (f : fmap) : fmap
    := let: FinMap s' p' := f in FinMap (sorted_filter_by_pred pr p').

  Lemma seqof_fbk pr f :
    seq_of (filter_by_key pr f) = [seq i <- seq_of f | (preim key pr) i].
  Proof. by case: f. Qed.

  Lemma path_fbk k pr f :
    path ord k (supp f) -> path ord k (supp (filter_by_key pr f)).
  Proof.
    apply: (subseq_order_path (@trans K)).
    by rewrite /supp seqof_fbk map_subseq ?filter_subseq.
  Qed.

  Lemma ord_nsym (k k' : K) : ord k k' -> ord k' k = false.
  Proof. by move=>ord; apply: negbTE; apply/negP; apply: nsym. Qed.

  Lemma ord_irr (k k' : K) : ord k k' -> k' == k = false.
  Proof. by apply: contraTF => /eqP->; rewrite irr. Qed.

  Lemma fbk_nil pr : filter_by_key pr nil = nil.
  Proof. by rewrite fmapE. Qed.

  (* This kind of things might be useful?
  Lemma ins_cancel
        (p : fmap -> fmap) (q : K -> V -> fmap -> fmap)
        (H0 : forall k v s, path ord k (supp s) -> p (ins k v s) = q k v (p s))
        (H1 : p nil = nil)
        (H2 : forall k v v' s, q k v (q k v' s) = q k v s)
        (H3 : forall k k' v v' s, k == k' = false ->
                                  q k v (q k' v' s) = q k' v' (q k v s))
        k v s :
    p (ins k v s) = q k v (p s).
  Proof.
    elim/fmap_ind': s k v =>[| k' v' s' pk' IH] k v; first by rewrite H0 // H1.
    case: (totalP k k') => kk'.
    + by rewrite H0 //; apply: path_supp_ins =>//; apply: (ord_path kk').
    + move: kk' pk' => /eqP<- pk; rewrite ins_ins (eq_refl k).
      by rewrite !H0 // H2.
    + rewrite IH (H3 _ _ _ _ _ (ord_irr kk')) ins_ins (ord_irr kk') H0 ?IH //.
      by apply: path_supp_ins =>//; apply: (ord_path kk').
  Qed.
  *)

  Lemma fbk_ins_ord pr k (v : V) f :
    path ord k (supp f) ->
    filter_by_key pr (ins k v f) = if pr k then ins k v (filter_by_key pr f)
                                   else filter_by_key pr f.
  Proof.
    move=>pp; rewrite fmapE fun_if !seqof_ins ?seqof_fbk ?seqof_ins => //.
      by apply: path_fbk.
  Qed.

  Lemma fbk_ins pr k (v : V) f :
    filter_by_key pr (ins k v f) = if pr k then ins k v (filter_by_key pr f)
                                   else filter_by_key pr f.
  Proof.
    elim/fmap_ind': f k v => [|k' v' s pk' IH] k v; first by apply: fbk_ins_ord.
    case: (totalP k k') pk' => [k_k' | /eqP<- | k'_k] pk'.
    (* Case k < k' by fbk_ins_ord *)
    + have path_k : path ord k (supp (ins k' v' s))
        by apply: path_supp_ins =>//; apply: (ord_path k_k').
      by rewrite fbk_ins_ord.
    (* Case k = k' by fbk_ins_ord and case analysis *)
    + rewrite ins_ins (eq_refl k) !fbk_ins_ord ?fun_if // ins_ins ?(eq_refl k).
      by case: ifP =>->.
    (* Case k' < k  by swapping k' and k with ins_ins, the IH and fbk_ins_ord *)
    + have path_k : path ord k' (supp (ins k v s)) by apply: path_supp_ins.
      rewrite ins_ins (ord_irr k'_k) fbk_ins_ord ?IH ?(fun_if (ins _ _))=> //.
      by rewrite ins_ins eq_sym (ord_irr k'_k); do ! (case: ifP).
  Qed.

  Lemma supp_fbk pr f : supp (filter_by_key pr f) = filter pr (supp f).
  Proof. by rewrite /supp seqof_fbk filter_map. Qed.

  Definition diff (f1 f2 : fmap) : fmap :=
    filter_by_key (fun k => k \notin supp f2) f1.

  Definition intersect (f1 f2 : fmap) : fmap :=
    filter_by_key (fun k => k \in supp f2) f1.

  Definition spl (E1 E2 : fmap) : fmap * fmap * fmap :=
    (diff E1 E2, intersect E1 E2, diff E2 E1).

  Lemma disj_diff_intersect f1 f2 : disj (diff f1 f2) (intersect f1 f2).
  Proof.
    rewrite /disj !supp_fbk; apply/allP => x /=.
      by rewrite !mem_filter =>/andP[/negbTE-> _].
  Qed.

  Lemma disj_diff_comm D D' : disj (diff D D') (diff D' D).
  Proof.
    rewrite /disj !supp_fbk; apply/allP => x /=.
      by rewrite !mem_filter =>/andP[_ ->].
  Qed.

  (* DC: FIXME - This proof is an absolute mess! Break down into useful
     lemmas, avoid repetition, etc. *)
  Lemma supp_intersect D D' : supp (intersect D D') = supp (intersect D' D).
  Proof.
    rewrite !supp_fbk.
    elim/fmap_ind': D D' =>[|k v D path_k_D IH] D'/=;
      first by elim: (supp D') =>//.
    rewrite /=; case: (suppP k D') => [v' | /eqP/notin_supp_fnd-fndNone].
    { move=>/eqP/in_supp_fnd-fndSome.
      rewrite /supp seqof_ins // /= fndSome IH -!/(supp _).
      move: v' D (supp D) path_k_D IH => _ _ s path_k_s _.
      elim/fmap_ind': D' fndSome =>// k' v' D' path_k'_D' IH'.
      rewrite /supp seqof_ins // /= -!/(supp _) in_cons.
      case/orP => [/eqP-eqkk' | k_in_D'].
      { move: eqkk' path_k'_D' =><- path_k_D'.
        rewrite in_cons eq_refl /= (negPf (notin_path path_k_s)); congr cons.
        apply eq_in_filter => k'' k''inD'.
        apply: esym; rewrite in_cons orbC; apply: orb_idr => /eqP-eqk''.
        move: eqk'' path_k_D' k''inD' =>->.
        by move/notin_path/negPf =>->.
      }
      { have ordk'k: ord k' k by apply: path_supp_ord (k_in_D') => //.
        suff/negPf k'notin_s : k' \notin s.
        suff k_not_k' : (k' == k) = false.
          by rewrite in_cons orbC k'notin_s /=;
                     rewrite k_not_k' IH' //.
        { apply/negP => /eqP-kk'.
          move: kk' ordk'k =>->.
            by rewrite irr.
        }
        { apply: contraT; rewrite Bool.negb_involutive => k'ins.
          case: (nsym ordk'k).
          apply: (path_supp_ord path_k_s) => //.
        }
      }
    }
    { rewrite /supp seqof_ins // /= (negPf fndNone) IH -!/(supp _).
      apply eq_in_filter => k' k'inD'.
      apply: esym; rewrite in_cons orbC; apply: orb_idr => /eqP-eqk.
      by move: eqk k'inD' fndNone =>->->.
    }
  Qed.

  Definition all_disj (f : fmap * fmap * fmap) :=
    let: (f1, f2, f3) := f in disj f1 f2 && disj f1 f3 && disj f2 f3.

  Lemma disj_spl f1 f2 : all_disj (spl f1 f2).
  Proof.
    rewrite /all_disj /spl disj_diff_intersect disj_diff_comm disjC.
    by rewrite /disj supp_intersect -/(disj _ _) disj_diff_intersect.
  Qed.

  Lemma fnd_diff k (f f' : fmap) :
    fnd k (diff f f') = match fnd k f' with
                        | Some _ => None
                        | None   => fnd k f
                        end.
  Proof.
    case: (suppP k f') =>[v|] H; rewrite H; move: H => /eqP.
    + move/in_supp_fnd => k_in_f'.
      by apply: fnd_supp; rewrite /diff supp_fbk mem_filter k_in_f'.
    + move/notin_supp_fnd => k_notin_f'; rewrite /diff.
      elim/fmap_ind': f =>// k' v' f path_f IH.
      rewrite fnd_ins fbk_ins; case: eqP =>[<-|].
      - by rewrite k_notin_f' fnd_ins eq_refl.
      - case: (boolP (k' \notin supp f')).
        * by move=>_ /eqP/negPf; rewrite fnd_ins =>->; rewrite IH.
        * by move=>_ _; rewrite IH.
  Qed.

  Lemma in_supp_diff k (f f' : fmap) :
    k \in supp (diff f f') = (k \notin supp f') && (k \in supp f).
  Proof.
    case: suppP=>[v|]; rewrite fnd_diff; case: (suppP k f')=>[v'|]->//.
    + by move=>/eqP/in_supp_fnd->.
    + by move=>/eqP/notin_supp_fnd/negPf->.
  Qed.

  Lemma fnd_intersect k (f f' : fmap) :
    fnd k (intersect f f') = match fnd k f' with
                             | Some _ => fnd k f
                             | None   => None
                             end.
  Proof.
    case: (suppP k f') =>[v|] H; rewrite H; move: H => /eqP.
    + move/in_supp_fnd => k_in_f'; rewrite /intersect.
      elim/fmap_ind': f =>// k' v' f path_f IH.
      rewrite fnd_ins fbk_ins; case: eqP =>[<-|].
      - by rewrite k_in_f' fnd_ins eq_refl.
      - case: (boolP (k' \notin supp f')).
        * by move=>/negPf-> _; rewrite IH.
        * rewrite Bool.negb_involutive=>-> /eqP/negPf-neq.
          by rewrite fnd_ins neq; rewrite IH.
    + move/notin_supp_fnd => k_notin_f'; apply: fnd_supp.
      by rewrite /intersect supp_fbk mem_filter negb_and k_notin_f'.
  Qed.

  Lemma in_supp_isect k (f f' : fmap) :
    k \in supp (intersect f f') = (k \in supp f) && (k \in supp f').
  Proof.
    case: suppP=>[v|]; rewrite fnd_intersect; case: (suppP k f')=>[v'|]->//.
    + by move=>/eqP/in_supp_fnd->.
    + by move=>/eqP/notin_supp_fnd/negPf->.
    + by rewrite andbC.
  Qed.

  Lemma diff_ins_l k T s1 s2 :
    k \in supp s2 -> diff (ins k T s1) s2 = diff s1 s2.
  Proof. by rewrite /diff fbk_ins =>->. Qed.

  Lemma diff_ins_r k T s1 s2 :
    k \notin supp s1 -> diff s1 (ins k T s2) = diff s1 s2.
  Proof.
    rewrite /diff fmapE !seqof_fbk => k_nin_s1.
    apply: eq_in_filter => [[k' v']] /(map_f key)/=-k'_in_s1.
    rewrite supp_ins [in LHS]/in_mem /= Bool.negb_orb andb_idl // =>_.
      by apply/negP => /eqP-kk'; move: kk' k'_in_s1 k_nin_s1 =>->->.
  Qed.

  Lemma diff_ins k T T' s1 s2 :
    k \notin supp s1 ->
    diff (ins k T s1) (ins k T' s2) = diff s1 s2.
  Proof.
    move => ks1; rewrite diff_ins_l ?diff_ins_r //.
    by rewrite supp_ins /in_mem /= eq_refl.
  Qed.

  Lemma ins_rem_eq k T (s1 s2 : fmap) :
    ins k T (rem k s1) = (ins k T (rem k s2)) -> ins k T s1 = ins k T s2.
  Proof. by rewrite !ins_rem (eq_refl k). Qed.

  Lemma intersect_ins k T T' s1 s2 :
    intersect (ins k T s1) (ins k T' s2) = ins k T (intersect s1 s2).
  Proof.
    rewrite /intersect fbk_ins supp_ins
            [in X in if X then _ else _]/in_mem /= (eq_refl k) /=.
    apply ins_rem_eq; case: s1 => s1 ps1; rewrite fmapE /=; congr (ins' k T).
    rewrite -!filter_predI; apply: eq_filter => [[k' v']] /=; rewrite supp_ins.
    by rewrite /predU /pred1 [in LHS]/in_mem /= andb_orr andNb.
  Qed.
End SetOp.

Section HoOps.
  Variables (V1 V2 : eqType) (K : ordType).

  Lemma map_key_applysnd (f : V1 -> V2) s :
    map key s = map (@key K V2) (map (fun t => (t.1, f t.2)) s).
  Proof. by elim: s =>// kv l /= <-. Qed.

  Lemma sorted_map (f : V1 -> V2) (s : seq (K * V1)) :
    sorted ord (map key s) ->
    sorted ord (map key (map (fun t => (t.1, f t.2)) s)).
  Proof. by rewrite (map_key_applysnd f). Qed.

  Definition fmap_map (f : V1 -> V2) s :=
    let: FinMap s' p' := s in FinMap (sorted_map f p').

End HoOps.

Prenex Implicits fmap_map.

Section HoLaws.
  Variable (V1 V2 V3 : eqType) (K : ordType).
  Notation fmap V := (finMap K V).
  Lemma fmap_const_eq (v : V3) (s1 : fmap V1) (s2 : fmap V2) :
    supp s1 == supp s2 -> fmap_map (fun _ => v) s1 = fmap_map (fun _ => v) s2.
  Proof.
    rewrite fmapE; case: s1 => e1; case: s2 => e2; rewrite/fmap_map/supp/seq_of.
    move=> _ _; elim: e1 e2; first by move=>e2; case: e2=> //; rewrite !/key.
    move=> [k1 v1] e1 IH e2; case: e2=> // [[k2 v2]] e2.
      by rewrite !map_cons eqseq_cons /key=>/andP-[/eqP-> H]; rewrite (IH _ H).
  Qed.

  Lemma seqof_fmap (f : V1 -> V2) (s : fmap V1) :
    seq_of (fmap_map f s) = map (fun t => (t.1, f t.2)) (seq_of s).
  Proof. by case: s=>//. Qed.

  Lemma fmap_map_ins (f : V1 -> V2) (k : K) v s :
    fmap_map f (ins k v s) = ins k (f v) (fmap_map f s).
  Proof.
    rewrite fmapE seqof_fmap /fmap_map; case: s=> s'; rewrite !/key /seq_of /=.
    elim: s'=>// [[k' v']] s' IH; rewrite /sorted map_cons -[(k',_).1]/(k').
    case: (totalP k k') => [ord_k_k' | /eqP<- | ord_k'_k] path_k'.
   + rewrite !last_ins' !map_cons /= ?ord_k_k' ?Bool.andb_true_l //.
     by rewrite -map_comp (@eq_map _ _ _ key).
   + by rewrite /= irr eq_refl map_cons.
   + rewrite /= (ord_nsym ord_k'_k) (ord_irr ord_k'_k) map_cons /= IH //.
     by apply: (path_sorted path_k').
  Qed.

  Lemma supp_map (f : V1 -> V2) (s : fmap V1) : supp (fmap_map f s) = supp s.
  Proof.
    elim/fmap_ind': s => // k v0 s path_s IHs.
      by rewrite /supp fmap_map_ins !seqof_ins ?map_cons -!/(supp _) ?IHs //.
  Qed.

  Lemma fnd_map (f : V1 -> V2) (s : fmap V1) k : fnd k (fmap_map f s) =
                                                 match fnd k s with
                                                 | Some v => Some (f v)
                                                 | None   => None
                                                 end.
  Proof.
    elim/fmap_ind' : s =>// k' v s path_k' IH.
      by rewrite fmap_map_ins !fnd_ins; case: eqP =>//.
  Qed.
End HoLaws.
