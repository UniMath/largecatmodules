(*
  Definition from_Coproducts_weq c : (∏ i, C ⟦ a i , c ⟧) ≃ C ⟦ CoproductObject _ _ (cpC a) , c ⟧.
- unicity at isomorphism près de coproducts
- (∐ (o : O) ∐ (i : A o), B i) ≅ (∐ (oi : ∑ (o : O), A o) , B (pr2 oi))
- Coproducts of epis are epis
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.coproducts.

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Open Scope cat.

Section WEQ.

  Context {C : category} {I : UU} (cpC : Coproducts I C).
  Variable (a : I -> C).

  Definition from_Coproducts_weq c : (∏ i, C ⟦ a i , c ⟧) ≃ C ⟦ CoproductObject _ _ (cpC a) , c ⟧.
    use weqpair.
    - intro f.
      apply CoproductArrow.
      exact f.
    - intro y.
      unfold hfiber.
      use unique_exists.
      + intro i.
        eapply compose.
        * apply CoproductIn.
        * exact y.
      + cbn.
        apply pathsinv0.
        apply CoproductArrowEta.
      + intros h.
        apply (homset_property C).
      + cbn.
        intro y'.
        intro h.
        apply funextsec.
        intro i.
        etrans;[|apply cancel_precomposition;exact h].
        apply pathsinv0.
        apply CoproductInCommutes.
  Defined.
End WEQ.

(** inspired by bincoproducts.v *)
Section coproduct_unique.


  Context {C : category} {I : UU} (a : I -> C).

Definition from_Coproduct_to_Coproduct (CC CC' : Coproduct I C a)
  : CoproductObject _ _ CC --> CoproductObject _ _ CC' :=
 CoproductArrow I C CC (CoproductIn I C CC').


(*
Lemma BinCoproduct_endo_is_identity (CC : BinCoproduct a b)
  (k : BinCoproductObject CC --> BinCoproductObject CC)
  (H1 : BinCoproductIn1 CC · k = BinCoproductIn1 CC)
  (H2 : BinCoproductIn2 CC · k = BinCoproductIn2 CC)
  : identity _ = k.
Proof.
  set (H' := pr2 CC _ (BinCoproductIn1 CC) (BinCoproductIn2 CC) ); simpl in *.
  set (X := (∑ fg : pr1 (pr1 CC) --> BinCoproductObject CC,
          pr1 (pr2 (pr1 CC))· fg = BinCoproductIn1 CC
          × pr2 (pr2 (pr1 CC))· fg = BinCoproductIn2 CC)).
  set (t1 := tpair _ k (dirprodpair H1 H2) : X).
  set (t2 := tpair _ (identity _ ) (dirprodpair (id_right _ ) (id_right _ ) ) : X).
  assert (X' : t1 = t2).
  { apply proofirrelevance.
    apply isapropifcontr.
    apply H'.
  }
  apply pathsinv0.
  apply (base_paths _ _ X').
Defined.
*)


Lemma is_iso_from_Coproduct_to_Coproduct (CC CC' : Coproduct I C a)
  : is_iso (from_Coproduct_to_Coproduct CC CC').
Proof.
  apply is_iso_from_is_z_iso.
  exists (from_Coproduct_to_Coproduct CC' CC).
  split; simpl.
  - apply pathsinv0.
    apply Coproduct_endo_is_identity.
    intro i.
    rewrite assoc. unfold from_Coproduct_to_Coproduct.
    rewrite CoproductInCommutes.
    rewrite CoproductInCommutes.
    apply idpath.
  - apply pathsinv0.
    apply Coproduct_endo_is_identity.
    intro i.
    rewrite assoc; unfold from_Coproduct_to_Coproduct.
    repeat rewrite CoproductInCommutes; apply idpath.
Defined.

Definition iso_from_Coproduct_to_Coproduct (CC CC' : Coproduct I C a)
  : iso (CoproductObject _ _ CC) (CoproductObject _ _ CC')
  := isopair _ (is_iso_from_Coproduct_to_Coproduct CC CC').
End coproduct_unique.

   (* (∐ (o : O) ∐ (i : A o), B i) ≅ (∐ (oi : ∑ (o : O), A o) , B (pr2 oi)) *)
Section CoprodSigma.

  Local Notation CPO := (CoproductObject _ _).

  Context {C : category} {O : UU} {A : O -> UU}.
  Context {B : ∏ (o : O) (a : A o), C} .
  Let BS := (fun z => B _ (pr2 z)).
  Context (cpF : Coproduct (∑ (o : O), A o) _ BS).
  Context (cp1 : ∏ (o : O), Coproduct (A o) _  (B _)).
  Context (cp2 : Coproduct O _  (fun o => (CPO (cp1 o)))).


  (* We show that cp2 is a coproduct *)
  Definition sigma_coprod_In o  : C ⟦ BS o , CPO cp2 ⟧ :=
    CoproductIn _ C (cp1 (pr1 o)) (pr2 o) · CoproductIn O C cp2 (pr1 o).
    
  (** Is it possible to define it without using the homset property ? *)
  Definition sigma_coprod_isCoproduct : isCoproduct _ _ _ _ sigma_coprod_In. 
    intros c f.
    use unique_exists.
    -  apply CoproductArrow.
       intro o.
       apply CoproductArrow.
       intro i.
       apply (f (o ,, i)).
    - abstract(intro i;
        unfold sigma_coprod_In;
        etrans;
        [
          rewrite <- assoc;
          apply cancel_precomposition;
          apply (CoproductInCommutes _ _ _ cp2)
        |];
        etrans;
        [
        set (CC := cp1 _);
        apply (CoproductInCommutes _ _ _ CC)
        |];
        now induction i).
    - intros t.
      cbn -[isaprop].
      apply impred_isaprop.
      intro z.
      apply (homset_property C).
    - cbn.
      intros g hg.
      apply CoproductArrowUnique.
      intro o.
      apply CoproductArrowUnique.
      intro i.
      etrans;[| exact (hg (o ,, i))].
      apply assoc.
  Defined.

  Definition sigma_Coproduct := mk_Coproduct _ _ _ _ _ sigma_coprod_isCoproduct.

  Definition sigma_coprod_iso : iso (CoproductObject _ _ cpF) (CoproductObject _ _ cp2) :=
    iso_from_Coproduct_to_Coproduct _ cpF sigma_Coproduct.
End CoprodSigma.

Section CoprodEpis.
  Context {C : category} {I  : UU} {a b : I -> C}
          (cpa : Coproduct _ _ a)
          (cpb : Coproduct _ _ b).

  Context {ff : ∏ i, C ⟦ a i, b i ⟧} (epif : ∏ i, isEpi (ff i)). 

  Lemma CoproductOfArrows_isEpi : isEpi (CoproductOfArrows _ _ cpa cpb ff).
  Proof.
    intros x f g.
    intro hfg.
    (* unfold CoproductOfArrows. *)
    (* do 2 rewrite postcompWithCoproductArrow. *)
    (* intro hfg. *)
    rewrite (CoproductArrowEta _ _ _ _ _ f).
    rewrite (CoproductArrowEta _ _ _ _ _ g).
    apply maponpaths.
    apply funextsec.
    intro i.
    apply (cancel_precomposition _ _ _ _ _ _ (CoproductIn I C cpa i)) in hfg.
    do 2 rewrite assoc in hfg.
    rewrite CoproductOfArrowsIn in hfg.
    do 2 rewrite <- assoc in hfg.
    now use epif.
  Qed.


End CoprodEpis.



  