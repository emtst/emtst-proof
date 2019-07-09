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

From mathcomp.ssreflect Require Import ssreflect ssrbool eqtype seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(***********)
(* Prelude *)
(***********)

(* often used notation definitions and lemmas that are *)
(* not included in the other libraries *)

(* selecting a list element *)
(* should really be in seq.v *)

Section HasSelect.
Variables (A : eqType) (p : pred A).

CoInductive has_spec (s : seq A) : bool -> Type :=
| has_true x of x \in s & p x : has_spec s true
| has_false of (all (predC p) s) : has_spec s false.

Lemma hasPx : forall s, has_spec s (has p s).
Proof.
elim=>[|x s IH] /=; first by apply: has_false.
rewrite orbC; case: IH=>/=.
- by move=>k H1; apply: has_true; rewrite inE H1 orbT.
case E: (p x)=>H; last by apply: has_false; rewrite /= E H.
by apply: has_true E; rewrite inE eq_refl.
Qed.

End HasSelect.
