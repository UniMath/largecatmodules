(**

Let F : Σ → ϒ be an epimorphism of signatures.
If the base category has pushouts, then for each monad R, F(R) is
an epimorphic natural transformation ([epiSig_is_pwEpi]).

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.limits.graphs.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.

Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModulesColims.
Require Import Modules.Signatures.SignaturesColims.
Require Import Modules.Signatures.Signature.

Section pwEpiAr.
  Local Notation SIG := signature_category.
  Context {C : category}  .
  Local Notation MOD R := (category_LModule R C).

  Context 
          (pos : colimits.Colims_of_shape pushout_graph C)
          {A B : signature C} (F : signature_Mor A  B)
          (epiF : isEpi (C:=SIG) F).


  Lemma PO_eqdiag (R : Monad C) X : 
    eq_diag
  (diagram_pointwise (homset_property C)
                     (mapdiagram (LModule_forget_functor R C) (mapdiagram (forget_Sig R) (pushout_diagram SIG F F))) X)
   (pushout_diagram C (F R X) (F R X) ).
  Proof.
    use tpair.
    use StandardFiniteSets.three_rec_dep;  apply idpath.
    use StandardFiniteSets.three_rec_dep;  use StandardFiniteSets.three_rec_dep;
      exact (empty_rect _ )||exact (λ _, idpath _).
  Defined.

  Let pushout_FF : Pushout SIG F F  :=
    Sig_Colims_of_shape pushout_graph pos (pushout_diagram SIG F F).

  Local Definition pushout_FFpw (R : Monad C) X : Pushout C (F R X) (F R X) :=
    eq_diag_liftcolimcocone
      _ (PO_eqdiag R X)
      (pos
         (diagram_pointwise
            (homset_property C)
            (mapdiagram (LModule_forget_functor R C)
                        (mapdiagram (forget_Sig R) (pushout_diagram signature_precategory F F))) X)).
    

  Lemma epiSig_is_pwEpi (R : Monad C) : isEpi (C := [C,C] ) (F R:nat_trans _ _).
  Proof.
    intros M f g eqfg.
    apply nat_trans_eq;[apply homset_property|].
    intro X.
    assert (eqfgX := nat_trans_eq_pointwise eqfg X).
    set (PO_FF' := pushout_FFpw R X).
    etrans.
    { eapply pathsinv0.
      apply (PushoutArrow_PushoutIn1 _ PO_FF' _ _ _ eqfgX).
    }
    etrans;[| apply (PushoutArrow_PushoutIn2 _ PO_FF' _ _ _ eqfgX)].
    apply cancel_postcomposition.
    assert (HHH : PushoutIn1 _ pushout_FF =  PushoutIn2 _ pushout_FF ).
    {
      apply epiF.
      apply PushoutSqrCommutes .
    }
    exact ( maponpaths (fun (Z : signature_Mor _ _) => (Z R X) ) HHH).
  Qed.
End pwEpiAr.