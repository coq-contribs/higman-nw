(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                                 Higman.v                                 *)
(****************************************************************************)
 
(*****************************************************************************)
(*    Recall of what is needed in the initial state of Coq                   *)

Require Import Arith.
Require Import Compare_dec.
Require Import Max.
Require Import Wf_nat.

(*i  What is needed in Logic.v **

Inductive True : Prop := I : True.

Inductive False : Prop := .
Theorem False_ind : (P:Prop)False->P.

Inductive eq [A:Set;x:A] : A -> Prop :=
   refl_equal : (eq A x x).
Theorem eq_ind : (A:Set)(x:A)(P:A->Prop)(P x)->(a:A)(x=a)->(P a).
Theorem eq_rec : (A:Set)(x:A)(P:A->Set)(P x)->(y:A)(x=y)->(P y).

Theorem sym_eq : (A:Set)(x:A)(y:A)x=y->y=x.
Theorem trans_eq : (A:Set)(x:A)(y:A)(z:A)x=y->y=z->x=z.
Theorem f_equal : (A:Set)(B:Set)(f:A->B)(x:A)(y:A)x=y->(f x)=(f y).

**  What is needed in Specif.v **

Inductive sumbool [A,B:Prop] : Set :=
   left : A ->({A}+{B})
 | right : B->({A}+{B}).

Definition except : (P:Set)False->P.

**  What is needed in Datatypes.v **

Inductive nat : Set :=
   O : nat
 | S : nat -> nat.
Theorem nat_ind : (P:nat->Prop)(P O)->((y:nat)(P y)->(P (S y)))->(n:nat)(P n).
Theorem nat_rec : (P:nat->Set)(P O)->((y:nat)(P y)->(P (S y)))->(n:nat)(P n).

** What is needed in Peano.v **

Definition pred : nat -> nat
            := [n:nat](<nat>Match n with O [u,v:nat]u end).

Theorem pred_Sn : (m:nat) m=(pred (S m)).

Theorem eq_add_S (n,m:nat)(S n)=(S m)->n=m.
Theorem O_S : (n:nat)~(O=(S n)).

Fixpoint plus [n:nat] : nat -> nat := 
   [m:nat]Cases n of 
      O   => m 
  | (S p) => (S (plus p m)) end.

Inductive le [n:nat] : nat -> Prop :=
   le_n : (le n n)
 | le_S : (m:nat)(le n m)->(le n (S m)).

Definition lt := [p,q:nat] (le (S p) q).

** What is needed in Le.v **

Theorem le_n_S : (n,m:nat)(le n m)->(le (S n) (S m)).
Theorem le_trans : (n,m,p:nat)(le n m)->(le m p)->(le n p).
Theorem le_O_n : (n:nat)(le O n).
Theorem le_trans_S : (n,m:nat)(le (S n) m)->(le n m).
Theorem le_S_n : (n,m:nat)(le (S n) (S m))->(le n m).
Theorem le_Sn_O : (n:nat)~(le (S n) O).
Theorem le_Sn_n : (n:nat)~(le (S n) n).
Theorem le_antisym (n,m:nat)(le n m)->(le m n)-><nat>n=m.
Theorem le_n_O_eq (n:nat)(le n O)->(<nat>O=n).

** What is needed in Lt.v ** 

Theorem lt_n_Sm_le : (n,m:nat)(lt n (S m))->(le n m).
Theorem lt_le_weak : (n,m:nat)(lt n m)->(le n m).
Theorem le_lt_trans : (n,m,p:nat)(le n m)->(lt m p)->(lt n p).
Theorem le_not_lt : (n,m:nat)(le n m) -> ~(lt m n).

** What is needed in Compare_dec.v **

Theorem lt_eq_lt_dec : (n,m:nat){(lt n m)}+{n=m}+{(lt m n)}.
Lemma le_lt_dec : (n,m:nat) {le n m} + {lt m n}.

** What is needed in Minus.v ** 

Fixpoint minus [n:nat] : nat -> nat := 
  [m:nat]Cases n m of
            O    _     =>  O
         | (S k) O     => (S k)
         | (S k) (S l) => (minus k l)
        end. 

Lemma minus_n_n : (n:nat)(O=(minus n n)).
Lemma le_plus_minus : (n,m:nat)(le n m)->(m=(plus n (minus m n))).

** What is needed in Plus.v **

Lemma simpl_le_plus_l : (p,n,m:nat)(le (plus p n) (plus p m))->(le n m).

** What is needed in Max.v **

Fixpoint max [n:nat] : nat -> nat :=  
[m:nat]Cases n m of
          O      _     => m
       | (S n')  O     => n
       | (S n') (S m') => (S (max n' m'))
       end.

Lemma le_max_l : (n,m:nat)(le n (max n m)).
Lemma le_max_r : (n,m:nat)(le m (max n m)).

** What is needed in Wf_nat.v **

Lemma lt_wf_rec : (p:nat)(P:nat->Set)
              ((n:nat)((m:nat)(lt m n)->(P m))->(P n)) -> (P p).

i*)

(*****************************************************************************)
(*                          Higman's lemma                                   *)
(*****************************************************************************)

Section Higman_.


(*****************************************************************************)
(*                           Preliminaries                                   *)
(*****************************************************************************)

(* To be a total order *)

Inductive connected (A : Set) (R : A -> A -> Prop) (x y : A) : Set :=
  | R_connected : R x y -> connected A R x y
  | Eq_connected : x = y :>A -> connected A R x y
  | L_connected : R y x -> connected A R x y.

Goal forall n p : nat, connected nat lt n p.
  intros; elim (le_lt_dec n p); intro.
    elim (le_lt_dec p n); intro.
      apply Eq_connected; apply le_antisym; assumption.
    apply R_connected; assumption.
  apply L_connected; assumption.
Save lt_connected.

(* One more property on minus. *)

Lemma lt_minus : forall i j n : nat, n <= i -> i < j -> i - n < j - n.
Proof.
  intros.
  apply plus_lt_reg_l with n.
  rewrite <- le_plus_minus; [ idtac | assumption ].
  rewrite <- le_plus_minus; [ assumption | idtac ].
  apply le_trans with i; [ idtac | apply lt_le_weak ]; assumption.
Qed.


(*****************************************************************************)
(*          Basic notions about words                                        *)

(* The two letters alphabet *)

Inductive M : Set :=
  | A0 : M
  | A1 : M.

Inductive ltM : M -> M -> Prop :=
    ltM_intro : ltM A0 A1.

Definition A0_A1 (h : A0 = A1 :>M) : False :=
  eq_ind A0 (M_rect (fun a : M => Prop) True False) I A1 h.

Definition ltM_connected : forall a b : M, connected M ltM a b.
Proof.
  simple induction a; simple induction b.
        apply Eq_connected; apply refl_equal.
      apply R_connected; apply ltM_intro.
    apply L_connected; apply ltM_intro.
  apply Eq_connected; apply refl_equal.
Defined.


(* The -trivial- well founded induction on letters *)

Theorem wfi_ltM :
 forall (P : M -> Set) (a : M),
 (forall b : M, (forall c : M, ltM c b -> P c) -> P b) -> P a.
Proof.
  intros; apply H.
  elim a; intros.  (* on disjoncte a=A0 ou a=A1 *)
    apply except; apply A0_A1.
    elim H0; apply refl_equal.  (* H0 : (c < A0 *)
  elim H0; apply H; intros.
    apply except; apply A0_A1.
    elim H1; apply refl_equal.  (* H0 : (c0 < A0 *)
Qed.


(* words *)

Inductive word : Set :=
  | Emptyword : word
  | Cons : M -> word -> word.


(* tail and head of a word *)

Definition tail (l : word) :=
  match l with
  | Emptyword => Emptyword
  | Cons _ w => w
  end.

Definition head (l : word) :=
  match l with
  | Emptyword => A0
  | Cons m _ => m
  end.


(* Embedding of a word in an other one *)

Inductive IN : word -> word -> Prop :=
  | INMV : IN Emptyword Emptyword
  | INcons : forall (x y : word) (a : M), IN x y -> IN x (Cons a y)
  | INconscons :
      forall (x y : word) (a : M), IN x y -> IN (Cons a x) (Cons a y).

Theorem MV_IN_all : forall a : word, IN Emptyword a.
Proof.
  simple induction a.
    exact INMV.
  intros.
  apply INcons; assumption.
Qed.


(* Definition of a total order on the words *)

Definition len (x : word) :=
  (fix F (w : word) : nat :=
     match w with
     | Emptyword => 0
     | Cons _ w0 => S (F w0)
     end) x.
Definition eql (x y : word) := len x = len y :>nat.
Definition lel (x y : word) := len x <= len y.
Definition ltl (x y : word) := len x < len y.

(* The strict lexicographic order on words of same length *)

Inductive slexn : word -> word -> Prop :=
  | slexn_ltM :
      forall (x y : word) (a b : M),
      ltM a b -> eql x y -> slexn (Cons a x) (Cons b y)
  | slexn_Cons :
      forall (x y : word) (a : M), slexn x y -> slexn (Cons a x) (Cons a y).

(* Recursive version of slexn *)

Definition slexn' (x : word) :=
  match x with
  | Emptyword => fun _ : word => False
  | Cons m w =>
      fun y : word =>
      match y with
      | Emptyword => False
      | Cons m0 w0 =>
          match ltM_connected m m0 with
          | R_connected _ => eql w w0
          | Eq_connected _ => slexn w w0
          | L_connected _ => False
          end
      end
  end.

(* The strict total order on words *)

Inductive ltw (x y : word) : Prop :=
  | ltw_eql : slexn x y -> ltw x y
  | ltw_ltl : ltl x y -> ltw x y.

Axiom slexn_MV : forall x : word, slexn x Emptyword -> False.
Axiom ltw_ltl_false : forall x y : word, ltw x y -> ltl y x -> False.
Axiom ltw_eq_false : forall x y : word, ltw x y -> x = y :>word -> False.
Axiom ltw_slexn_false : forall x y : word, ltw x y -> slexn y x -> False.

Theorem slexn_slexn' : forall x y : word, slexn x y -> slexn' x y.
Proof.
  simple induction 1.
    simple induction 1; simpl in |- *; intros; assumption.
  simple induction a; simpl in |- *; intros; assumption.
Qed.

Theorem slexn'_rec :
 forall P : word -> word -> Set,
 (forall (x y : word) (a b : M),
  ltM a b -> eql x y -> P (Cons a x) (Cons b y)) ->
 (forall (x y : word) (a : M), slexn x y -> P x y -> P (Cons a x) (Cons a y)) ->
 forall w w0 : word, slexn' w w0 -> P w w0.
Proof.
  simple induction w.
    simpl in |- *; intros; apply except; assumption.
  simple induction w1.
    simpl in |- *; intros; apply except; assumption.
  do 3 intro; simpl in |- *; elim (ltM_connected m m0); intros.
      apply H; assumption.
    elim e; apply H0.
      assumption.
    apply H1; apply slexn_slexn'; assumption.
  apply except; assumption.
Qed.

Theorem slexn_connected :
 forall x y : word, eql x y -> connected word slexn x y.
Proof.
  simple induction x.
    simple induction y; intros.
        apply Eq_connected; apply refl_equal.
      absurd (eql Emptyword (Cons m w)); try assumption.
      unfold eql in |- *; simpl in |- *; apply O_S.
  intros m w; simple induction y; intros.
    absurd (eql Emptyword (Cons m w)).
      unfold eql in |- *; simpl in |- *; apply O_S.
    unfold eql in |- *; apply sym_equal; assumption.
  elim (ltM_connected m m0); intros.
      apply R_connected; apply slexn_ltM; try assumption.
        unfold eql in |- *; apply eq_add_S; assumption.
    elim e; elim (H w0); intros.
          apply R_connected; apply slexn_Cons; assumption.
        apply Eq_connected; elim e0; apply refl_equal.
      apply L_connected; apply slexn_Cons; assumption.
    unfold eql in |- *; apply eq_add_S; assumption.
  apply L_connected; apply slexn_ltM; try assumption.
        unfold eql in |- *; apply eq_add_S; apply sym_equal; assumption.
Qed.

Theorem ltw_rec :
 forall (x y : word) (P : Set),
 (slexn x y -> P) -> (ltl x y -> P) -> ltw x y -> P.
Proof.
  intros x y.
  elim (lt_connected (len x) (len y)); intros.
      apply H0; assumption.
  2: apply except; apply (ltw_ltl_false x y); assumption.
  elim (slexn_connected x y).
  4: assumption.
      assumption.
    intro; apply except; apply (ltw_eq_false x y); assumption.
  intro; apply except; apply (ltw_slexn_false x y); assumption.
Qed.

Theorem ltw_connected : forall x y : word, connected word ltw x y.
Proof.
  intros; elim (lt_connected (len x) (len y)); intro.
      apply R_connected; apply ltw_ltl; assumption.
  2: apply L_connected; apply ltw_ltl; assumption.
  elim (slexn_connected x y); intros.
  4: assumption.
      apply R_connected; apply ltw_eql; assumption.
    apply Eq_connected; assumption.
  apply L_connected; apply ltw_eql; assumption.
Qed.


(*         well founded induction on words           *)

(* well founded induction on words ordered by length *)

Section wfi_ltl_.

Variable P : word -> Set.

Variable x : word.

Remark wfi_ltl1 :
 (forall y : word, (forall z : word, ltl z y -> P z) -> P y) ->
 forall t : word, lel t x -> P t.
Proof.
  intro H.
  elim x; intros.
    apply H; intros.
    absurd (ltl z t); try assumption.
    unfold ltl in |- *; elim (le_n_O_eq (len t)).
      unfold lt in |- *; apply le_Sn_O.
    assumption.
  elim (le_lt_eq_dec (len t) (S (len w)) H1); intro H2.
    apply H0; unfold lel in |- *; apply le_S_n; assumption.
  apply H; intros.
  apply H0.
  unfold lel in |- *; apply le_S_n; intros; elim H2; assumption.
Qed.

Theorem wfi_ltl :
 (forall y : word, (forall z : word, ltl z y -> P z) -> P y) -> P x.
Proof.
  intros.
  apply wfi_ltl1.
    assumption.
  unfold lel in |- *; apply le_n.
Qed.

End wfi_ltl_.


(* well founded induction on words of fixed length ordered lexicographically *)

Theorem wfi_slexn :
 forall (n : nat) (P : word -> Set),
 (forall y : word,
  (forall z : word, slexn z y -> P z) -> len y = n :>nat -> P y) ->
 forall x : word, len x = n :>nat -> P x.
Proof.
  simple induction n; simple induction x; intros.
        apply H; intros.
          apply except; apply slexn_MV with z; assumption.
        assumption.
      apply except; apply O_S with (len w); apply sym_equal; assumption.
    apply except; apply O_S with n0; assumption.
  apply
   (wfi_ltM (fun a : M => forall x : word, len x = n0 :>nat -> P (Cons a x)));
   intros.
  2: apply eq_add_S; assumption.
  apply (H (fun x : word => P (Cons b x))); intros.
  2: assumption.
  apply H0; intros.
  2: elim H6; apply refl_equal.
  cut (head (Cons b y) = b :>M).
  2: apply refl_equal.
  cut (tail (Cons b y) = y :>word).
  2: apply refl_equal.
  pattern z, (Cons b y) in |- *.
  apply slexn'_rec; intros.
  3: apply slexn_slexn'; assumption.
    apply H3.
      elim H11; assumption.
    elim H6; elim H10; assumption.
  simpl in H11.
  elim (sym_equal H11).
  apply H5.
  elim H10; assumption.
Qed.


(* well founded induction on words totally ordered by ltw *)

Theorem wfi_ltw :
 forall (P : word -> Set) (x : word),
 (forall y : word, (forall z : word, ltw z y -> P z) -> P y) -> P x.
Proof.
  intros.
  apply (wfi_ltl P x); intros.
  pattern y in |- *.
  apply wfi_slexn with (len y); intros.
  2: apply refl_equal.
  apply H.
  simple induction 1; intros.
    apply H1; assumption.
  apply H0.
  unfold ltl in |- *; elim H2; assumption.
Qed.



(*****************************************************************************)
(*          The formal A-translated proof of Higman's lemma                  *)
(*****************************************************************************)

Section Formal_Higman.


(* The variable of A-translation *)

Variable A : Set.


(* sequences of words are defined as a predicat and relatively to A *)
(* bad sequences are those which don't verify the lemma             *)

Section Bad_sequence.

Variable f : nat -> word -> Set.

Definition exi_im := forall n : nat, (forall x : word, f n x -> A) -> A.

Definition uniq_im :=
  forall (n : nat) (x y : word), f n x -> f n y -> (x = y :>word -> A) -> A.

Definition cex :=
  forall (i j : nat) (x y : word), f i x -> f j y -> i < j -> IN x y -> A.

Inductive bad : Set :=
    bad_intro : exi_im -> uniq_im -> cex -> bad.

End Bad_sequence.


(* To be equal on the n-1 first terms *)

Definition eqgn (n : nat) (h h' : nat -> word -> Set) :=
  forall i : nat,
  i < n -> forall s t : word, h i s -> h' i t -> (s = t :>word -> A) -> A.


(* To be minimal on the nth term *)

Definition Minbad (n : nat) (h : nat -> word -> Set) 
  (y : word) :=
  forall h' : nat -> word -> Set,
  bad h' -> eqgn n h h' -> forall z : word, h' n z -> ltw z y -> A.


(* To be minimal on the n-1 first terms *)

Definition Minbadns (n : nat) (h : nat -> word -> Set) :=
  forall p : nat, p < n -> (forall y : word, h p y -> Minbad p h y -> A) -> A.


(* The minimal (bad) counter-example *)

Definition Mincex (n : nat) (x : word) :=
  forall C : Set,
  (forall h : nat -> word -> Set,
   bad h -> Minbadns n h -> h n x -> Minbad n h x -> C) -> C.

Definition Mincex_intro (n : nat) (x : word) (h : nat -> word -> Set)
  (p : bad h) (p1 : Minbadns n h) (p2 : h n x) (p3 : Minbad n h x) :
  Mincex n x :=
  fun (C : Set)
    (p4 : forall h : nat -> word -> Set,
          bad h -> Minbadns n h -> h n x -> Minbad n h x -> C) =>
  p4 h p p1 p2 p3.

Theorem Mincex_rec :
 forall (n : nat) (x : word) (P : Set),
 (forall h : nat -> word -> Set,
  bad h -> Minbadns n h -> h n x -> Minbad n h x -> P) -> 
 Mincex n x -> P.
Proof.
  intros.
  apply H0.
  assumption.
Qed.

(* A thick sequence has no empty term. It is the case of counter-examples *)

Section thick_.

Definition thick (f : nat -> word -> Set) :=
  forall n : nat, f n Emptyword -> A.

Variable f : nat -> word -> Set.

Theorem bad_thick : exi_im f -> cex f -> thick f.
Proof.
  red in |- *; intros.
  apply (H (S n)); intros.
  apply (H0 n (S n) Emptyword x).
        assumption.
      assumption.
    exact (le_n (S n)).
  apply MV_IN_all.
Qed.

End thick_.


(* There is an infinity of terms with the same first letter *)

Section infinitely_many_.

Variable h : nat -> word -> Set.

Hypothesis exi_imh : exi_im h.

Hypothesis thick_h : thick h.

Definition the_next_after (a : M) (k : nat) :=
  forall (n : nat) (x : word), k <= n -> h n (Cons a x) -> A.

Definition infinitely_many (a : M) := forall k : nat, the_next_after a k -> A.


Theorem switcher :
 forall k k0 : nat,
 the_next_after A0 k ->
 the_next_after A1 k0 -> forall x : word, h (max k k0) x -> A.
Proof.
  simple induction x.
  (* x=Emptyword *)
      intros; apply (thick_h (max k k0)).
    assumption.
  (* x=m::w *)
  simple induction m; intros.
      (* m=A0 *)
      apply (H (max k k0) w).
        apply le_max_l.
      assumption.
    (* m=A1 *)
    apply (H0 (max k k0) w).
      apply le_max_r.
    assumption.
Qed.

Theorem reader :
 forall k k0 : nat, the_next_after A0 k -> the_next_after A1 k0 -> A.
Proof.
  intros.
  apply (exi_imh (max k k0)); intros.
  apply switcher with k k0 x.
      assumption.
    assumption.
  assumption.
Qed.

Theorem little_inf_A0_or_inf_A1 :
 forall k : nat, the_next_after A0 k -> (infinitely_many A1 -> A) -> A.
Proof.
  intros.
  apply H0.
  red in |- *; intros.
  apply (reader k k0).
    assumption.
  assumption.
Qed.

Theorem inf_A0_or_inf_A1 :
 (infinitely_many A0 -> A) -> (infinitely_many A1 -> A) -> A.
Proof.
  intros.
  apply H.
  red in |- *; intros.
  apply (little_inf_A0_or_inf_A1 k).
    assumption.
  assumption.
Qed.

End infinitely_many_.


(****************************************************************************)
(*      We show that the minimal counter-example is effectively bad         *)

Section BadMin_.

Variable f : nat -> word -> Set.
Hypothesis Badf : bad f.
Variable f0 : word.
Hypothesis f_0_f0 : f 0 f0.


Section ExiMin_.

Theorem eqgn_trans :
 forall (n : nat) (h h' h'' : nat -> word -> Set),
 exi_im h' -> eqgn n h h' -> eqgn n h' h'' -> eqgn n h h''.
Proof.
  intros.
  red in |- *; intros.
  apply (H i); intros.  (* [ H = (exi_im h') ] *)
  unfold eqgn in H0.
  unfold eqgn in H1.
  apply H0 with i s x.
        assumption.
      assumption.
    assumption.
  intros.
  apply H1 with i x t.
        assumption.
      assumption.
    assumption.
  intros.
  apply H5.
  apply trans_equal with x.
    assumption.
  assumption.
Qed.

Theorem eqgn_Minbadns :
 forall h h' : nat -> word -> Set,
 bad h' -> forall n : nat, eqgn n h h' -> Minbadns n h -> Minbadns n h'.
Proof.
  unfold Minbadns at 2 in |- *.
  intros.
  unfold Minbadns in H1; apply H1 with p.
    assumption.
  intros.
  elim H; intros; unfold exi_im in e; apply e with p; intros.
  unfold eqgn in H0; apply H0 with p y x; try assumption.
  intro.
  apply H3 with x.
    assumption.
  unfold Minbad in |- *.
  intros.
  unfold Minbad in H5.
  apply H5 with h'0 z; try assumption.
    apply eqgn_trans with h'; try assumption.
    unfold eqgn in |- *; do 2 intro.
    intros.
    apply H0 with i s t; try assumption.
    apply le_lt_trans with p.
      apply lt_le_weak.
      assumption.
    assumption.
  cut (x = y :>word).
    intros H_eq; elim H_eq; assumption.
  apply sym_equal; assumption.
Qed.

Section exi_cmin_S_.

Variable n : nat.

Theorem exi_cmin_S :
 (forall (x : word) (h : nat -> word -> Set),
  bad h -> Minbadns n h -> Minbad n h x -> h n x -> A) ->
 forall (x : word) (h : nat -> word -> Set),
 bad h -> Minbadns n h -> h n x -> A.
Proof.
  intros H x; pattern x in |- *; apply wfi_ltw.
  intros; apply H with y h; try assumption.  
  unfold Minbad in |- *; intros.
  apply H0 with z h'; try assumption.
  apply eqgn_Minbadns with h; try assumption.
Qed.

Theorem exi_cmin_exi :
 (forall (x : word) (h : nat -> word -> Set),
  bad h -> Minbadns (S n) h -> h (S n) x -> A) ->
 forall (x : word) (h : nat -> word -> Set),
 bad h -> Minbadns n h -> Minbad n h x -> h n x -> A.
Proof.
  simple induction 2; intros.
  unfold exi_im in e; apply e with (S n); intros.
  apply H with x0 h; try assumption.
  unfold Minbadns in |- *; intros.
  elim (le_lt_eq_dec p n); [ intro H7 | intro H7 | intros ].
  3: apply lt_n_Sm_le; assumption.
     unfold Minbadns in H1; apply H1 with p; try assumption.
  apply H6 with x.  
    elim (sym_equal H7); assumption.
  elim (sym_equal H7); assumption.
Qed.

End exi_cmin_S_.

Theorem ExiMin1 :
 forall (x : word) (f1 : nat -> word -> Set),
 bad f1 -> f1 0 x -> exi_im Mincex.
Proof.
  red in |- *.
  unfold Mincex in |- *.
  simple induction n; [ intro H1 | intros y H1 H2 ].
    apply exi_cmin_S with 0 x f1; try assumption.
      intros.
      apply H1 with x0; intros.
      apply H6 with h; try assumption.
    unfold Minbadns in |- *; intros.
    absurd (S p <= 0); apply le_Sn_O || assumption.
  apply H1; intros.
  apply H3; intros.
  apply exi_cmin_exi with y x0 h; try assumption.
  intros.
  apply exi_cmin_S with (S y) x1 h0; try assumption.
  intros.
  apply H2 with x2; intros.
  apply H15 with h1; try assumption.
Qed.

Theorem ExiMin : exi_im Mincex.
Proof.
  apply ExiMin1 with f0 f.
  exact Badf.
  exact f_0_f0.
Qed.

End ExiMin_.


Section UniMin_.

Theorem UniMin_eqgn :
 forall (h h' : nat -> word -> Set) (n i : nat),
 i < S n ->
 bad h ->
 bad h' ->
 Minbadns i h -> Minbadns i h' -> eqgn n Mincex Mincex -> eqgn i h h'.
Proof.
  unfold eqgn in |- *; intros.
  apply H4 with i0 s t; try assumption.
      unfold lt in |- *; apply le_trans with i.
        assumption.
      apply le_S_n; assumption.
    unfold Minbadns in H2.
    apply Mincex_intro with h; try assumption.
      unfold Minbadns in |- *; intros.
      apply H2 with p.
        unfold lt in |- *; apply le_trans with i0; try assumption.
        apply lt_le_weak; assumption.
      assumption.
    unfold Minbad in |- *; intros.
    apply H2 with i0.
      assumption.
    unfold Minbad in |- *; intros.
    elim H0; intros.
    unfold uniq_im in u; apply u with i0 s y; try assumption.
    intro; apply H14 with h'0 z; try assumption.
    elim H15; assumption.
  unfold Minbadns in H3.
  apply Mincex_intro with h'; try assumption.
    unfold Minbadns in |- *; intros.
    apply H3 with p.
      unfold lt in |- *; apply le_trans with i0; try assumption.
      apply lt_le_weak; assumption.
    assumption.
  unfold Minbad in |- *; intros.
  apply H3 with i0.
    assumption.
  unfold Minbad in |- *; intros.
  elim H1; intros.
  unfold uniq_im in u; apply u with i0 t y; try assumption.
  intro; apply H14 with h'0 z; try assumption.
  elim H15; assumption.
Qed.

Theorem UniMin1 : forall n : nat, eqgn n Mincex Mincex.
Proof.
  simple induction n; [ idtac | intro y ]; unfold eqgn in |- *; intros.
    absurd (S i <= 0).
      apply le_Sn_O.
    assumption.
  elim (le_lt_eq_dec i y (lt_n_Sm_le _ _ H0)); intros.
    (* i < y *)
    unfold eqgn in H; apply H with i s t; assumption.
  (* i = y *)
  apply H1; intros h H5 H6 H7 H8.
  apply H2; intros h0 H9 H10 H11 H12.
  (* 3 cas : x<y, y<x, ou x=y *) 
  elim (ltw_connected s t).
  (* Le cas x=y se resoud ds les hypotheses *)
  2: assumption.
      (* x < y *)
    intro H13; unfold Minbad in H12.
    apply H12 with h s; try assumption.
    apply UniMin_eqgn with y; try assumption.
  intro; unfold Minbad in H8.
  apply H8 with h0 t; try assumption.
  apply UniMin_eqgn with y; try assumption.
Qed.

Theorem UniMin : uniq_im Mincex.
Proof.
  unfold uniq_im in |- *; intros.
  cut (eqgn (S n) Mincex Mincex); apply UniMin1 || intro H_eqgn.
  unfold eqgn in H_eqgn; apply H_eqgn with n x y.
        exact (le_n (S n)).
      assumption.
    assumption.
  assumption.
Qed.

End UniMin_.


Section CexMin_.

Theorem CexMin : cex Mincex.
Proof.
  red in |- *; intros.
  (* (Mincex j y) donne un h min sur 1..j valant y en j *)
  apply H0.
  intros.
  elim H3; intros.
  unfold Minbadns in H4.
  (* On exhibe la valeur y0 de h en i *)
  apply H4 with i; assumption || intros.
  cut (Mincex i y0).
    intros.
    apply (UniMin i x y0).
        assumption.
      assumption.
    intros.
    apply (c i j y0 y).  (* on utilise le fait que h est bad *)
          assumption.
        assumption.
      assumption.
    elim H10.                  (* c = (cex h)  *)
    assumption.
  apply (Mincex_intro i y0 h).
        assumption.
      unfold Minbadns in |- *; intros.
      apply H4 with p.
        apply le_lt_trans with i.
          apply lt_le_weak.
          assumption.
        assumption.
      assumption.
    assumption.
  assumption.
Qed.

End CexMin_.


Definition BadMin : bad Mincex := bad_intro Mincex ExiMin UniMin CexMin.

End BadMin_.



(****************************************************************************)
(* We show in this section that the extracted sequence of a bad sequence    *)
(* is also a bad sequence                                                   *)

Section Badfx_.

Variable f : nat -> word -> Set.

Hypothesis Badf : bad f.

Variable a0 : M.

Hypothesis inf_many : infinitely_many f a0.


(*   Xa is the set of word beginning with a0   *)
(* (Xn n) is Xa with the first n words removed *)

Inductive Xn : nat -> nat -> Set :=
  | Xa_intro : forall (n : nat) (y : word), f n (Cons a0 y) -> Xn 0 n
  | X'_intro :
      forall p n : nat,
      Xn p n -> forall n' : nat, Xn p n' -> n' < n -> Xn (S p) n.

Inductive Leastp (X : nat -> Set) (p : nat) : Set :=
    Leastp_intro : X p -> (forall q : nat, q < p -> X q -> A) -> Leastp X p.


(* The subsequence of word beginning with the letter a0 *)

Definition g (n p : nat) := Leastp (Xn n) p.

Theorem Xn_elim :
 forall (P : nat -> nat -> Set) (y y0 : nat),
 Xn y y0 ->
 (forall (n : nat) (y : word), f n (Cons a0 y) -> P 0 n) ->
 (forall p n : nat, P p n -> forall n' : nat, P p n' -> n' < n -> P (S p) n) ->
 P y y0.
Proof.
  intros.
  elim H.
    assumption.
  intros.
  apply H1 with n'.
      assumption.
    assumption.
  assumption.
Qed.


Theorem X'_elim :
 forall i q : nat,
 Xn (S i) q -> (forall q' : nat, Xn i q' -> q' < q -> A) -> A.
Proof.
  intros i q H_Xn.
  cut (pred (S i) = i :>nat); try apply refl_equal.
  intro H_eq; elim H_eq.
  cut (S i = S i :>nat); try apply refl_equal.
  pattern (S i) at 1 2 4, q, H_Xn in |- *.
  elim H_Xn; intros.
    absurd (0 = S i :>nat); assumption || apply O_S.
  apply H2 with n'; assumption.
Qed.

Theorem Xa_elim :
 forall q : nat, Xn 0 q -> (forall y : word, f q (Cons a0 y) -> A) -> A.
Proof.
  intros.
  apply
   (Xn_elim (fun p q : nat => (forall y : word, f q (Cons a0 y) -> A) -> A) 0
      q).
        assumption.
      intros.
      apply (H2 y).
      assumption.
    do 6 intro.
    assumption.
  assumption.
Qed.

Section Xn_decreases_.

Variable n q : nat.

Let P (p : nat) := n <= p -> Xn p q -> Xn n q.

Theorem Xn_decreases1 : forall p : nat, Xn (S p) q -> Xn p q.
Proof.
  intros.
  cut (Xn (pred (S p)) q); intros.
    assumption.
  elim H; intros.
    apply Xa_intro with y.
    assumption.
  assumption.
Qed.


Theorem Xn_decreases : forall p : nat, P p.
Proof.
  intro p.
  elim p.
    red in |- *; intros H H0.
    elim (le_n_O_eq n H).
    assumption.
  red in |- *; intros y H H0 H1.
  elim (le_lt_eq_dec n (S y) H0); intros H2.
    apply (H (le_S_n _ _ H2)).
    apply Xn_decreases1.
    assumption.
  elim (sym_equal H2).
  assumption.
Qed.

End Xn_decreases_.


Theorem Xn_in_Xa : forall n p : nat, Xn n p -> Xn 0 p.
Proof.
  intros.
  apply Xn_decreases with n.
    apply (le_O_n n).
  assumption.
Qed.

Section Xn_non_empty_.

Section X1_.

Let P (n : nat) := forall p q : nat, p < q -> Xn n p -> Xn 0 q -> Xn (S n) q.

Theorem X1 : forall n : nat, P n.
Proof.
  intros.
  elim n.
    red in |- *; intros.
    apply X'_intro with p.
        assumption.
      assumption.
    assumption.
  unfold P in |- *.
  (*Red;*)intro y; intros.
  apply X'_intro with p.
      apply H with p.
            assumption.
          cut (Xn (pred (S y)) p); intros.
            assumption.
          elim H1; intros.
          apply Xa_intro with y0.
          assumption.
        assumption.
      assumption.
    assumption.
  assumption.
Qed.

End X1_.

Let P (n : nat) := (forall p : nat, Xn n p -> A) -> A.

Theorem Xn_non_empty : forall n : nat, P n.
Proof.
  intros.
  elim n.
    red in |- *; intros.
    apply (inf_many 0).
    red in |- *; intros.
    apply (H n0).
    apply Xa_intro with x.
    assumption.
  unfold P in |- *.
  intro y; intros.
  apply H.
  intros.
  apply (inf_many (S p)).
  red in |- *; intros.
  apply (H0 n0).
  apply X1 with p.
      assumption.
    assumption.
  apply Xa_intro with x.
  assumption.
Qed.

End Xn_non_empty_.

(* g is effectively a sequence *)

Theorem Exig : forall n : nat, (forall p : nat, g n p -> A) -> A.
Proof.
  intros.
  apply (Xn_non_empty n).
  intro; pattern p in |- *.
  apply lt_wf_rec.
  intros.
  apply (H n0).
  red in |- *; intros.
  apply Leastp_intro.
    assumption.
  assumption.
Qed.

Theorem Unig : forall n p q : nat, g n p -> g n q -> (p = q :>nat -> A) -> A.
Proof.
  unfold g in |- *.
  unfold g in |- *.
  intros.
  elim H.
  elim H0.
  intros.
  elim (lt_connected p q).
      intro; apply (a p); assumption. (* a = (q0:nat)(lt q0 p)->(Xn n q0)->A *)
    assumption.
  intro; apply (a1 q); assumption.    (* a0 = (q:nat)(lt q p)->(Xn n q)->A   *)
Qed.


(* Definition of the extracted sequence and proof of its badness *)

Section Badfx_.


Variable n0 : nat.

Hypothesis n0_min : g 0 n0.

Inductive fx (i : nat) (x : word) : Set :=
  | fxhd : i < n0 -> f i x -> fx i x
  | fxtl :
      forall p : nat, n0 <= i -> g (i - n0) p -> f p (Cons a0 x) -> fx i x.


Lemma Unifx :
 forall (n : nat) (x y : word), fx n x -> fx n y -> (x = y :>word -> A) -> A.
Proof.
  intros.
  elim Badf; intros.
  elim H; intros.
    elim H0; intros.
      apply (u n x y).    (* [ u = (uniq_im f) ] *)
          assumption.
        assumption.
      assumption.
    apply except.
    apply (le_not_lt n0 n).
      assumption.
    assumption.
  elim H0.
    intros.
    apply except.
    apply (le_not_lt n0 n).
      assumption.
    assumption.
  intros p0 Hl Hg Hf.     (* si on ne force pas, clash anormal avec Unig *)
  apply (Unig (n - n0) p0 p).
      assumption.
    assumption.
  intro.
  apply (u p (Cons a0 x) (Cons a0 y)).
      assumption.
    elim H2.
    assumption.
  intro.
  apply H1.
  cut (tail (Cons a0 x) = tail (Cons a0 y) :>word); intros.
    assumption.
  elim H3; apply refl_equal.
Qed.


Lemma Exifx : forall n : nat, (forall x : word, fx n x -> A) -> A.
Proof.
  intros.
  elim Badf; intros.
  elim (le_lt_dec n0 n); intros.
    apply (Exig (n - n0)).
    intros.
    cut (Leastp (Xn (n - n0)) p).
    intro H2.
    elim H2.
    intros.
    apply (Xn_elim (fun q q' : nat => g (n - n0) q' -> A) (n - n0) p).
            assumption.
          intros.
          apply (H y).
          apply fxtl with n1.
              assumption.
            assumption.
          assumption.
        do 6 intro.
        assumption.
      assumption.
    assumption.
  apply (e n).
  intros.
  apply (H x).
  apply fxhd.
    assumption.
  assumption.
Qed.

Lemma g_grows : forall i j p q : nat, i < j -> g i p -> g j q -> q <= p -> A.
Proof.
  intros.
  unfold g in H0.
  elim H0.
  intros.
  apply (X'_elim i q).
    unfold g in H1.
    apply Xn_decreases with j.
      assumption.
    elim H1.
  intros.
  assumption.
  intros.
  apply (a q').
  2: assumption.
  unfold lt in |- *; apply le_trans with q.
    assumption.
  elim (le_or_lt q p); intros.
    assumption.
  assumption.
Qed.


Lemma g_grows_0 : forall i p : nat, g i p -> p < n0 -> A.
Proof.
  intros.
  unfold g in H.
  elim H.
  intros.
  cut (Leastp (Xn 0) n0); intros.
    elim H1.
    intros H2 a1.
    apply (a1 p).  (* a0 = (q:nat)(Xn O q)->((le n0 q)->A)->A  *)
      assumption.
    apply (Xn_in_Xa i).
    assumption.
  exact n0_min.
Qed.

Lemma Cexfx :
 forall (i j : nat) (x y : word), fx i x -> fx j y -> i < j -> IN x y -> A.
Proof.
  intros.
  elim Badf; intros.
  elim H; intros.
    elim H0; intros.
      apply (c i j x y); intros.      (* [ c = (cex f) ] *)
            assumption.
          assumption.
        assumption.
      assumption.
    elim (le_lt_dec n0 p); intros.
      apply (c i p x (Cons a0 y)).
            assumption.
          assumption.
        unfold lt in |- *; apply le_trans with n0.
          assumption.
        assumption.
      apply INcons.
      assumption.
    apply (g_grows_0 (j - n0) p); intros.
      assumption.
    assumption.
  elim H0; intros.
    apply except.
    apply (le_not_lt j i).
      apply le_trans with n0.
        apply lt_le_weak.
        assumption.
      assumption.
    assumption.
  elim (le_lt_dec p0 p); intro.
    apply (g_grows (i - n0) (j - n0) p p0).
    apply lt_minus.
            assumption.
          assumption.
        assumption.
      assumption.
    assumption.
  apply (c p p0 (Cons a0 x) (Cons a0 y)).
        assumption.
      assumption.
    assumption.
  apply INconscons.
  assumption.
Qed.

Definition Badfx : bad fx := bad_intro fx Exifx Unifx Cexfx.

(* fx and f are identical on the n0-1 first terms *)

Theorem eqgn_f_fx : eqgn n0 f fx.
Proof.
  red in |- *; intros.
  elim H1; intros.
    elim Badf; intros.
    apply (u i s t).
        assumption.
      assumption.
    assumption.
  apply except.
  apply (le_not_lt n0 i).
    assumption.
  assumption.
Qed.

End Badfx_.

End Badfx_.


(*****************************************************************************)
(*                    The contradiction                                      *)

Section contradiction.

Variable f : nat -> word -> Set.
Hypothesis Badf : bad f.
Variable f0 : word.
Hypothesis f_0_f0 : f 0 f0.

Theorem eqgn_fxMin_h :
 forall (a : M) (n : nat) (h : nat -> word -> Set),
 bad h -> Minbadns n h -> eqgn n h (fx Mincex a n).
Proof.
  unfold eqgn in |- *; intros.
  cut (bad Mincex).
    intro H_BadMin.
    unfold Minbadns in H0; apply H0 with i; try assumption.
    intro; elim H; intros; apply (u i s y); assumption || intro.
    intros.
    apply (eqgn_f_fx Mincex H_BadMin a n i H1 y t); try assumption.
      apply Mincex_intro with h; try assumption.
        red in |- *; intros.
        apply H0 with p.
        unfold lt in |- *; apply le_trans with i.
          assumption.
        apply lt_le_weak.
        assumption.
      assumption.
    elim H7; assumption.
  exact (BadMin f Badf f0 f_0_f0).
Qed.

Theorem snake :
 forall a : M,
 infinitely_many Mincex a ->
 forall n0 : nat,
 (forall q : nat, q < n0 -> Xn Mincex a 0 q -> A) -> Xn Mincex a 0 n0 -> A.
Proof.
  intros.
  cut (bad Mincex); intros.
    apply (Xa_elim Mincex a n0); intros.
      assumption.
    cut (bad (fx Mincex a n0)); intros.
      apply H3; intros.
      unfold Minbad in H8.
      apply H8 with (fx Mincex a n0) y.
            assumption.
          apply eqgn_fxMin_h; assumption.
        apply fxtl with n0.
            apply le_n.
          elim (minus_n_n n0).
          red in |- *; intros.
          apply Leastp_intro.
            assumption.
          assumption.
        assumption.
      apply ltw_ltl.
      unfold ltl, lt in |- *.
      apply le_n.
    apply Badfx.
        assumption.
      assumption.
    red in |- *; intros.
    apply Leastp_intro.
      assumption.
    assumption.
  exact (BadMin f Badf f0 f_0_f0).
Qed.

Theorem holf :
 forall a : M,
 infinitely_many Mincex a ->
 forall (n : nat) (x : word), 0 <= n -> Mincex n (Cons a x) -> A.
Proof.
  intros.
  apply (lt_wf_rec n (fun n : nat => Xn Mincex a 0 n -> A)).
    exact (snake a H).
  apply Xa_intro with x.
  assumption.
Qed.

Theorem one_letter_final : forall a : M, infinitely_many Mincex a -> A.
Proof.
  intros.
  apply (H 0).
  exact (holf a H).
Qed.


Theorem final : A.
Proof.
  elim (BadMin f Badf f0 f_0_f0); intros.
  apply (inf_A0_or_inf_A1 Mincex); intros.
        assumption.
      apply bad_thick; assumption.
    apply (one_letter_final A0); assumption.
  apply (one_letter_final A1); assumption.
Qed.

End contradiction.

End Formal_Higman.


(*****************************************************************************)
(*             "A" is now Higman's lemma statement                           *)

Section Higman_end.

Variable f0 : nat -> word.

Inductive f (n : nat) : word -> Set :=
    f_intro : f n (f0 n).

Inductive A : Set :=
    A_intro : forall i j : nat, i < j -> IN (f0 i) (f0 j) -> A.


Theorem Exif : exi_im A f.
Proof.
  red in |- *; intros.
  apply (H (f0 n)).
  apply f_intro.
Qed.

Theorem Unif : uniq_im A f.
Proof.
  unfold uniq_im in |- *; intros n x y H_f_x H_f_y H_eq_x_y.
  apply H_eq_x_y.
  pattern x in |- *.
  elim H_f_x.
  pattern y in |- *.
  elim H_f_y.
  apply refl_equal.
Qed.

Theorem Cexf : cex A f.
Proof.
  red in |- *; do 7 intro.
  pattern x in |- *.
  elim H.
  pattern y in |- *.
  elim H0.
  intro.
  apply (A_intro i j).
    assumption.
  assumption.
Qed.

Definition Badf : bad A f := bad_intro A f Exif Unif Cexf.


Definition higman : A := final A f Badf (f0 0) (f_intro 0).


End Higman_end.

End Higman_.