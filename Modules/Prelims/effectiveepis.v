(**
- Definition of an effective epimorphism.
- Proof that natural transformations that are pointwise effective epis are 
 effective epis.

*)


Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Require Import UniMath.CategoryTheory.Epis.

(* a mettre dans UniMaths ? *)
Require Import Modules.Prelims.eqdiag.


(** Definition of an effective epimorphism.
An effective epimorphism p: A -> B is a morphism wich as a kernel pair and which
is the coequalizer of its kernel pair.
*)
Section EffectiveEpi.
  Context {C:precategory} {A B:C}.
  Variable (f: C ⟦A,B⟧). 
  
  Definition kernel_pair := Pullback  f f.

  Definition isEffective :=
    Σ  g:kernel_pair,
         (isCoequalizer (PullbackPr1 g)
                        (PullbackPr2 g) f (PullbackSqrCommutes g)).
End EffectiveEpi.

Definition EpisAreEffective (C:precategory) :=
  Π (A B:C) (f:C⟦A,B⟧), isEpi f -> isEffective f.




(* Let f be a transfo nat. If f is pointwise effective, then f is effective *)
Section IsEffectivePw.
  
    Context { C :precategory} {D:Precategory} .

    

   Local Notation CD := (@functor_Precategory C D). 

   
    Context {X Y :functor C D } {a:CD ⟦X,Y⟧}.

  Lemma isEffectivePw : (Π (x:C), isEffective (pr1 a x)) -> isEffective a.
    intros h.
    red.
    transparent assert (f:(kernel_pair a)).
    { apply equiv_Pullback_2;[apply homset_property|].
      apply LimFunctorCone.
      intro c.
      specialize (h c).
      set (f := pr1 h).
      apply equiv_Pullback_1 in f;[|apply homset_property].
      use (eq_diag_liftlimcone _  _  f).
      use tpair.
      use StandardFiniteSets.three_rec_dep; apply idpath.
      
      use StandardFiniteSets.three_rec_dep;  use StandardFiniteSets.three_rec_dep; 
         exact (Empty_set_rect _ ) ||  (exact (fun _ => idpath _)).
    }

    exists f.


    apply equiv_isCoequalizer2;[apply homset_property|].
    apply  pointwise_Colim_is_isColimFunctor.
    intro x.
    set (g:= f).
    assert (hf := (pr2 (h x))); simpl in hf.
    apply equiv_isCoequalizer1 in hf;[|apply homset_property].
    red in hf.
    
    revert hf.
    match goal with |- isColimCocone ?d1 _ ?cc1 -> isColimCocone  ?d2 _  ?cc2 =>
                    transparent assert (eqd:(eq_diag d1 d2)) end.
    {
      use tpair.
      use StandardFiniteSets.two_rec_dep; reflexivity.
     use StandardFiniteSets.two_rec_dep;  use StandardFiniteSets.two_rec_dep; 
       try exact (Empty_set_rect _ ).

     intros g'.
     destruct g'.
     apply idpath.
     apply idpath.
    } 

    intro hf.

    set (z:= (eq_diag_iscolimcocone _ eqd hf)).
    set (CC := (mk_ColimCocone _ _ _ z)).
    apply (is_iso_isColim (homset_property D) _ CC).
    rewrite <- (colimArrowUnique CC _ _ (identity _)).
    
    apply identity_is_iso.
    use StandardFiniteSets.two_rec_dep;
    cbn beta;

    rewrite id_right;
    apply idpath.
Qed.


  
End IsEffectivePw.
