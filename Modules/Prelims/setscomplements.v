(**

Complements about the category of set

- has kernel pairs
- has effective epis
- Proof that a natural transformation which is an epi when the codomain of
considered functors is the hSet category has a lifting property similar
to the previously mentionned for surjections.
- Transfo nat that are epis are pointwise epis when the target category is HSET


 *)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.RModules. 


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.pushouts.
Require Import UniMath.CategoryTheory.limits.graphs.coequalizers.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.EffectiveEpis.


Require Import UniMath.CategoryTheory.CocontFunctors.

Require Import UniMath.CategoryTheory.GrothendieckTopos.

Require Import Modules.Prelims.epipw.
Require Import Modules.Prelims.effectiveepis.


Definition hset_Precategory : Precategory := (hset_precategory ,, has_homsets_HSET).

Section kernel_pair_Set.

  Local Notation SET := hset_Precategory.
  Context  {A B:SET}.
  Variable (f: SET ⟦A,B⟧).


  Definition kernel_pair_set : kernel_pair f.
    red.
    apply HSET_Pullbacks.
  Defined.

    
  Local Notation g := kernel_pair_set.

  Import limits.pullbacks.

  Lemma kernel_pair_eq
        (a:pr1 (PullbackObject g)) :
    f ( (PullbackPr1 g) a) = f ((PullbackPr2 g) a).
  Proof.
    intros.
    assert (hg':=PullbackSqrCommutes g).
    apply      toforallpaths in hg'.
    apply hg'.
  Qed.

  Lemma isCoeqEpi (hf:issurjective f) : isCoequalizer _ _ _ (PullbackSqrCommutes g).
  Proof.
    intros.
    red.
    intros C u equ.

    assert (hcompat :   Π x y : pr1 A, f x = f y → u x = u y).
    {
      intros x y eqfxy.
            assert (hpb:=pullback_HSET_univprop_elements
                     (PullbackSqrCommutes g) (isPullback_Pullback g) x y eqfxy).
      assert( hpb' := pr2 (pr1 hpb)); simpl in hpb'.
      destruct hpb' as [hx hy].
      
      etrans.
      symmetry.
      apply maponpaths.      
      apply hx.
      
      symmetry.
      etrans.
      symmetry.
      apply maponpaths.
      apply hy.
      
      apply toforallpaths in equ.
      symmetry.
      apply equ.
    }
    
    use (unique_exists (univ_surj (setproperty C) _ _ _ hf)).
    - exact u.
    - exact hcompat.
    - simpl.
      apply funextfun.
      intros ?.
      apply univ_surj_ax.
    - intros ?; apply homset_property.
    - intros ??; simpl.
      apply funextfun.
      use univ_surj_unique.
      simpl in X.
      apply toforallpaths in X.
      exact X.
  Qed.
End kernel_pair_Set.




    



Lemma EffectiveEpis_HSET : EpisAreEffective hset_precategory.
Proof.
  red.
  clear.
  intros A B f epif.
  exists (kernel_pair_set f).
  apply isCoeqEpi.
  apply epiissurjectiontosets; [apply setproperty|].
  intros C g1 g2 h .
  apply toforallpaths.
  apply (epif C    g1 g2).
  now apply funextfun.
Qed.


Set Automatic Introduction.

(* 

 Preuve qu'on peut relever les épi dans la catégorie des endo foncteurs sur Set
Autrement dit :
    f
 A ---> C
 |
 | p
 |
 \/
 B

Si p est un épi et que pour tout x y dans A, p(x)=p(y) => f(x)=f(b)
alors il existe une unique flèche de B vers C qui complète le diagramme.

Ca vient du fait que les epis sont effectifs

*)
Section LiftEpiNatTrans.
  
  Local Notation SET := hset_Precategory.
  Context { Cat:precategory}.
  Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
  Local Notation C_SET :=  ([Cat, SET, (homset_property SET)]).

  Context {A B C:C_SET} (p:nat_trans (pr1 A) (pr1 B))
          (f:nat_trans (pr1 A)(pr1 C)).

  Hypothesis (comp_epi: Π (X:Cat)  (x y: pr1 (pr1 A X)),
                        p X x =  p X y -> f X x = f X y).


  Hypothesis (surjectivep : isEpi (C:=C_SET) p).

  
  Import graphs.pushouts.

  Lemma HSET_Pushouts : Pushouts SET.
    red.
    intros .
    apply ColimsHSET_of_shape.
  Qed.

  Lemma EffectiveEpis_Functor_HSET : EpisAreEffective C_SET.
  Proof.
    intros F G m isepim.
    apply isEffectivePw.
    intro x.
    apply EffectiveEpis_HSET.
    apply (Pushouts_pw_epi HSET_Pushouts).
    assumption.
  Qed.
    
  Definition univ_surj_nt :nat_trans ( (pr1 B )) ( (pr1 C )).

    apply EffectiveEpis_Functor_HSET in surjectivep.
    red in surjectivep.
    set (coeq := limits.coequalizers.mk_Coequalizer _ _ _ _ (pr2 surjectivep)).
    apply (limits.coequalizers.CoequalizerOut coeq _ f).
    abstract(
    apply (nat_trans_eq (homset_property _));
    intro c;
    apply funextfun;
    intro x;
    apply comp_epi;
    assert (hcommut := limits.pullbacks.PullbackSqrCommutes (pr1 surjectivep));
    eapply nat_trans_eq_pointwise in hcommut;
    apply toforallpaths in hcommut;
    apply hcommut).
  Defined.

  Import limits.coequalizers.

  Lemma univ_surj_nt_ax : nat_trans_comp _ _ _ p  univ_surj_nt   = f .
  Proof.
    unfold univ_surj_nt; cbn.
    set (coeq := mk_Coequalizer _ _ _ _ _).
    apply (CoequalizerCommutes coeq).
  Qed.

  Lemma univ_surj_nt_ax_pw x  : ( p x ;; univ_surj_nt x  )    = f x .
  Proof.
    now rewrite <- univ_surj_nt_ax.
  Qed.

  
  Lemma univ_surj_nt_ax_pw_pw x c : ( p x ;; univ_surj_nt x  ) c   = f x c.
  Proof.
    now rewrite <- univ_surj_nt_ax.
  Qed.

End LiftEpiNatTrans.

Lemma is_pointwise_epi_from_set_nat_trans_epi (C:precategory)
      (F G : functor C hset_Precategory) (f:nat_trans ( F) ( G))
      (h:isEpi (C:=functor_Precategory C hset_Precategory) f)
  : Π (x:C), isEpi (f x).
Proof.
  apply Pushouts_pw_epi.
  apply HSET_Pushouts.
  apply h.
Qed.
