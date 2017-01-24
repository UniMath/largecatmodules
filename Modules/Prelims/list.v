Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.equalizers.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.

Fixpoint itern (F0:UU) (F : UU -> UU) (n:nat) : UU :=
  match n with
    0 => F0
  | S p => F (itern F0 F p)
  end.


Module List1.

  Definition puissancen (A:UU) (n:nat) : UU := itern unit (fun B => A × B) n.


Definition List : UU := Σ n, puissancen nat n.

Definition nil : List := (0 ,, tt).

Definition cons (a:nat) (l:List): List.
  use tpair.
  exact (S (pr1 l)).
  cbn.
  use tpair.
  exact a.
  exact (pr2 l).
Defined.

(** The induction principle for lists defined using foldr *)
Section list_induction.

Variables (P : List -> UU) (PhSet : Π l, isaset (P l)).
Variables (P0 : P nil)
          (Pc : Π a l, P l -> P (cons a l)).

Lemma final (l:List) : P l.
  destruct l as [n l].
  induction n.
  - destruct l.
  exact P0.
  - specialize (IHn (pr2 l)).
    assert(yop:= Pc (pr1 l) (n,,pr2 l) IHn).
    unfold cons in yop.
    cbn in yop.
    now destruct l.
Defined.

Lemma fnil : final nil = P0.
  apply idpath.
Qed.

Lemma fcons a l : final (cons a l) = Pc a l (final l).
  (* il faut d'abord détruire l pour avoir la réduction *)
  destruct l.
  apply idpath.
Qed.
End list_induction.


Definition length (l:List) := final (fun _ => nat) 0 (fun _ _ n => S n) l.

Eval compute in (length nil).

End List1.

Module List2.
  Open Scope stn.
  Section def.
    Variable (TT : UU).
    (* Local Notation TT := nat *)
  (* Definition One : two := ● 0. *)
  (* Definition Two : two := ● 1. *)

  (* Definition sum (A:UU) (B:UU) := Σ (x:two), two_rec (A:=UU) A B x *)
  Notation sum := coprod (only parsing).

  (* à base de quotient *)
  Definition F (A:UU) :UU := sum unit (TT×A).

  Definition Listn (n:nat) := itern ∅ F n.

  Definition Fmor1 {A B:UU} (C:UU) (f: A -> B) (x:sum C A) : sum C B.
    induction x as [l|t].
    now apply inl.
   (*  use tpair. *)
   (* exact (pr1 x). *)
   (* generalize (pr2 x). *)
   (*  use (two_rec_dep (fun a => two_rec C A a -> two_rec C B a) _ _ (pr1 x));cbn. *)
    (* apply idfun. *)
    (* exact f. *)
    apply inr; apply f; exact t.
  Defined.

  Definition Fmor {A B:UU} (f:A -> B) : F A -> F B.
    apply Fmor1.
    intro x.
    exact (pr1 x,, f (pr2 x)).
  Defined. 

  Definition injF {n} (l:Listn n) : Listn (S n).
    induction n.
    now apply Empty_set_rect.
    revert IHn l.
    apply Fmor.
  Defined.


  Definition list_rel {p q:nat} (l:Listn p) (l':Listn q): UU.
    set (h:= isdeceqnat q (S p) ).
    cbn in h.
    use (coprod_rect (fun _ => UU) _ _ h).
    - intro heq.
      cbn.
      clear h.
      exact (injF l = transportf _ heq l').
    - intros.
      exact Empty_set.
  Defined.

  Definition Chain := Σ n, Listn n.

  Lemma myisapropishinh :Π X : UU, isaprop (ishinh_UU X).
    exact isapropishinh.
    Defined.
  Lemma myisasetsetquot: Π (X : UU) (R : hrel X), isaset (setquot R).
    exact @isasetsetquot.
  Qed.

  (* copié de category_hset_structure *)
(* Theory about hprop is in UniMath.Foundations.Propositions *)
Local Definition rel0 : hrel Chain := λ (ia jb : Chain),
  hProppair (ishinh (list_rel (pr2 ia) (pr2 jb)))
            (myisapropishinh _).

Local Definition rel : hrel Chain := eqrel_from_hrel rel0.
Lemma iseqrel_rel : iseqrel rel.
Proof.
now apply iseqrel_eqrel_from_hrel.
Qed.

Local Definition eqr : eqrel Chain := eqrelpair _ iseqrel_rel.

Definition List : hSet :=
  hSetpair (setquot eqr) (isasetsetquot _).

Definition nil_chain : Chain := (1,, inl tt). (* (1,,(One,,tt)). *)
Definition nil : List := setquotpr eqr nil_chain. (*  *)

Definition cons_chain (a:TT) (l:Chain) : Chain.
  use tpair.
  exact (S (pr1 l)).
  apply inr.
  exact (a,,pr2 l).
Defined.

Lemma myadmit (A:UU) : A.
  admit.
  Admitted.
Lemma isasetChain: isaset Chain.
Proof.
  apply myadmit.
Qed.

Lemma isasetList : isaset List.
apply myadmit.
Qed.

Definition ChainSet : hSet := (_ ,, isasetChain).
Definition ListSet : hSet := (_ ,, isasetList).

Lemma compat_cons (a:TT) : iscomprelfun eqr (cons_chain a).
apply myadmit.
Qed.


Definition cons_list_chain (a:TT) (l:List) : ChainSet.
  use (setquotuniv eqr _ _ _ l).
  apply (cons_chain a).
  apply compat_cons.
  Defined.

Definition cons (a:TT) (l:List) := setquotpr eqr (cons_list_chain a l).
(** The induction principle for lists defined using foldr *)
Section list_induction.

Variables (P : hSet) .
Variables (P0 : P )
          (Pc : TT -> P -> P ).

Definition algP : F P -> P.
  intro h.
  induction h as [_|x].
  now apply P0.
  apply Pc.
  exact (pr1 x).
  exact (pr2 x).

  (*
  generalize (pr2 h).
  use (two_rec_dep (fun a => two_rec _ _ a -> P) _ _(pr1 h)).
  - intros _; exact P0.
  - intro h'.
    cbn in h'.
    apply Pc.
    apply (pr1 h').
    apply (pr2 h').
*)
Defined.


Definition chain_to_P (l:Chain) : P.
  generalize (pr2 l).
  induction (pr1 l).
  - use Empty_set_rect. (* intros ?; cbn in X. exact P0. *)
  - intro h.
    induction h as [_|x].
    + apply P0.                  
    + apply Pc.
      exact (pr1 x).
      apply IHn.
      exact (pr2 x).
Defined.
Lemma test : chain_to_P nil_chain = P0.
  apply idpath.
Qed.


Lemma compat_chainP : iscomprelfun eqr chain_to_P.
apply myadmit.
Qed.

Definition list_ind_non_dep (l: List) : P .
  use (setquotuniv eqr _ _ _ l).
  exact chain_to_P.
  exact compat_chainP.
Defined.
 
Lemma fnil : list_ind_non_dep nil = P0.
  apply idpath.
Qed.

 
Lemma fcons a l : list_ind_non_dep (cons a l) = Pc a (list_ind_non_dep l).
  cbn.
  unfold cons_list_chain.
  revert l.
  eapply surjectionisepitosets.
  apply  issurjsetquotpr.
  apply setproperty.
  intro x.
  apply idpath.
  Qed.
End list_induction.

Section list_induction_dep.

Variables (P : List -> hSet) (PhSet : Π l, isaset (P l)).
Variables (P0 : P nil)
          (Pc : Π a l, P l -> P (cons a l)).


Let P' := Σ l, P l.
Let P'0 : P' := (nil,, P0).
Let P'c : TT -> P' -> P' := fun t a => (cons t (pr1 a),, Pc t (pr1 a) (pr2 a)).

Lemma isasetP' : isaset P'.
apply myadmit.
Qed.

Definition P'Set : hSet := (_ ,, isasetP').

Definition intermede (l:List) : P'Set.
  eapply (list_ind_non_dep).
  apply P'0 .                   
  apply P'c.
  exact l.
Defined.

Lemma eq_refl_nat (n:nat) (e:n=n) : e = idpath _.
  apply proofirrelevance.
  apply isasetnat.
Defined.
Lemma pr1_intermede l : pr1 (intermede (setquotpr _ l)) = setquotpr _ l.
  Proof.
    cbn.
    Abort.
Lemma pr1_intermede_nil  : pr1 (intermede nil) = nil.
  Proof.
    apply idpath.
    Qed.

  (* setquotunivprop *)
Lemma pr1_intermede l : pr1 (intermede l) = l.
Proof.
   eapply (surjectionisepitosets _ (fun x => pr1 (intermede x))(idfun _)).
   (* c'est ce lemme qui fait bloquer la réduction, à cause de setquotl0 qui ne calcule pas,
je pense que c'est à cause de funext *)
  apply  issurjsetquotpr.
  apply isasetList.
  intro x'.
  unfold idfun.
  cbn.
  clear l.
  destruct x' as [n l].
  induction n.
  cbn.
  exact (Empty_set_rect  (fun x => pr1 (empty_rect _ x) = setquotpr eqr (0,,x))  l).
  cbn.
  induction l as [ttu |l IHl].

   - cbn.
     unfold nil.
     apply (iscompsetquotpr eqr).
     cbn.
     intro R.
     intro h.
     unfold nil_chain.
     elim n.
     + destruct ttu.
       apply eqrelrefl.
     + intros p hp.
       eapply eqreltrans.
       apply hp.
       apply h.
       cbn.
       apply hinhpr.
       unfold list_rel.
       set (heq := isdeceqnat _ _).
       induction heq as [eqr|eqrl].
       * cbn.
         clear.
         assert (heq:eqr = idpath _).
         {
           apply proofirrelevance.
           apply isasetnat.
         }
         now rewrite heq.
       * eapply Empty_set_rect.
         apply eqrl.
         apply idpath.
   - cbn.
     apply (iscompsetquotpr eqr).
     cbn.
     intros R hR.
     apply myadmit.
     Defined.

Definition list_ind (l:List) : P l.
  set (x:= pr2 (intermede l)).
  cbn in x.
  rewrite pr1_intermede in x. 
  exact x.
Defined.

(* e' := setquotl0 eqr nil (nil_chain,, eqrelrefl eqr nil_chain) : setquotpr eqr nil_chain = ni *)
Lemma setquotpr_nil : setquotpr eqr nil_chain = nil.
  apply idpath.
  Qed.

Goal  setquotpr eqr nil_chain = nil.
  set (e':=setquotl0 eqr nil (nil_chain,, eqrelrefl eqr nil_chain)).
  cbn in e'.
  unfold setquotl0 in e'.
  cbn in e'.
  Check ((pr1setquot rel) ).
  set (e'' := funextsec _ _ _ _) in e'.
  cbn in e''.
  unfold invmaponpathsincl in e'.
  cbn in e'.
  clearbody e''.
  set (e2 := weqonpathsincl _ _ _ _) in e'.
  cbn in e2.
  compute in e'.
  Abort.

Lemma fnil2 : list_ind nil = P0.
  cbn.
unfold list_ind.
cbn.
set (e:= paths_rect _ _ _ _ _ _ ).
cbn in e.
set (e' := (setquotl0 eqr nil (nil_chain,, eqrelrefl eqr nil_chain))) in e.
cbn in e'.
setquotl0
apply idpath.
unfold pr1_intermede.
Abort.
End list_induction_dep.

Lemma fnil2 (P:hSet) (P0:P) (Pc:TT -> P -> P): list_ind  (fun _ => P) P0 (fun t _ => Pc t) nil = P0.
  apply idpath.
  Abort.


End List2.