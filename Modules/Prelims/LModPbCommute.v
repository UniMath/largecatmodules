(* Commutation with pullback of modules
- General construction of iso between
modules that have the same underlying functor
- M ~ id* M
- m*(m'*(T'')) ~ (m o m')*(T'')
- pull back functor (base change). This is mathematically redundant with the
cleaving of the large category of modules over monad in modules.v
but more convenient to use
- f* (∐ M_i) ~ ∐ (f* M_i)
- f* (M× N) ~ f* M × f* N
- f* (M') ~ (f* M)'


 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.
Require Import UniMath.CategoryTheory.Monads.Derivative.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.LModuleCoproducts.
Require Import Modules.Prelims.LModuleBinProduct.
(* Require Import Modules.Prelims.LModuleColims. *)
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Open Scope cat.


Section IsoLModPb.
  Context {B} {R:Monad B}  {C:precategory}
          {F : functor B C}.
  Context {m1 m2 : R ∙ F ⟹ F }.

  Let F_data1 : LModule_data _ _ := F ,, m1.
  Let F_data2 : LModule_data _ _ := F ,, m2.

  Context (m1_law : LModule_laws _ F_data1).
  Context (m2_law : LModule_laws _ F_data2).

  Let M1 : LModule _ _ := _ ,, m1_law.
  Let M2 : LModule _ _ := _ ,, m2_law.

  (* Context (hm : ∏ c, lm_mult _ M1 c = lm_mult _ M2 c). *)
  Context (hm : ∏ c, m1 c = m2 c).

  Definition LModule_M1_M2_laws : LModule_Mor_laws R (T := M1) (T' := M2) (nat_trans_id _).
    intro c.
    etrans;[apply id_left|].
    apply pathsinv0.
    etrans;[apply ( (id_right _))|].
    apply hm.
  Qed.

  Definition LModule_M2_M1_laws : LModule_Mor_laws R (T := M2) (T' := M1) (nat_trans_id _).
    intro c.
    etrans;[apply id_left|].
    apply pathsinv0.
    etrans;[apply ( (id_right _))|].
    apply pathsinv0.
    apply hm.
  Qed.

  Definition LModule_M1_M2 : LModule_Mor R M1 M2 := _ ,, LModule_M1_M2_laws.
  Definition LModule_M2_M1 : LModule_Mor R M2 M1 := _ ,, LModule_M2_M1_laws.



  Lemma LModule_M1_M2_is_inverse hsC :
    is_inverse_in_precat (C := precategory_LModule R (category_pair C hsC) )
                         LModule_M1_M2 LModule_M2_M1.
  Proof.
    use mk_is_inverse_in_precat.
    - apply LModule_Mor_equiv;[ apply homset_property|].
      apply  (id_left (C := [B ,C , hsC])).
    - apply LModule_Mor_equiv;[ apply homset_property|].
      apply  (id_right (C := [B ,C , hsC])).
  Qed.

  Definition LModule_M1_M2_iso hsC : iso (C := precategory_LModule R (category_pair C hsC) )
                                         M1 M2.
  Proof.
    eapply isopair.
    eapply is_iso_from_is_z_iso.
    eapply mk_is_z_isomorphism.
    apply LModule_M1_M2_is_inverse.
  Defined.






End IsoLModPb.

(** 
Let T be a module on M'.

In this section, we construct the module morphism T -> id* T (which is
actully an iso) where id* T is the pullback module of T along
the identity morphism in M'.

and also the morphism id* T -> T

*)
Section Pullback_Identity_Module.

Context {B : precategory} {M' : Monad B}  {C : precategory} {T : LModule M' C}.

Local Notation pbmid := (pb_LModule (Monad_identity M') T).

Lemma pbm_id_law :
  ∏ c : B, (lm_mult _ T) c = (pb_LModule_σ (Monad_identity M') T) c.
Proof.
  intro c.
  cbn.
  apply pathsinv0.
  etrans;[|apply id_left].
  apply cancel_postcomposition.
  apply functor_id.
Qed.

Definition pbm_id_iso hsC : iso (C := precategory_LModule _ (C ,, hsC)) T pbmid :=
  LModule_M1_M2_iso _ _ pbm_id_law hsC.

Definition pbm_id  : LModule_Mor _ T pbmid :=
  LModule_M1_M2  _ _ pbm_id_law.

Definition id_pbm  : LModule_Mor _ pbmid T :=
  LModule_M2_M1  _ _ pbm_id_law.


End Pullback_Identity_Module.

(**
In this section, we construct the module morphism (which is actually an iso)
between m*(m'*(T'')) and (m o m')*(T'')

*)

Section Pullback_Composition.

Context {B : precategory} {M M' : Monad B} (m : Monad_Mor M M') {C : precategory}
        {M'' : Monad B} (m' : Monad_Mor M' M'') (T'' : LModule M'' C).

Local Notation comp_pbm := (pb_LModule m (pb_LModule m' T'')).
Local Notation pbm_comp := (pb_LModule (Monad_composition m  m') T'').

  Lemma pbm_mor_comp_law  (c : B) :
    (pb_LModule_σ m (pb_LModule m' T'')) c = (pb_LModule_σ (Monad_composition m m') T'') c.
  Proof.
    cbn.
    etrans; [apply assoc|].
    apply cancel_postcomposition.
    apply pathsinv0.
    apply functor_comp.
  Qed.
  Definition pbm_mor_comp : LModule_Mor _ comp_pbm pbm_comp :=
    LModule_M1_M2 _ _ pbm_mor_comp_law.


  Definition pbm_comp_mor : LModule_Mor _ pbm_comp comp_pbm :=
    LModule_M2_M1 _ _ pbm_mor_comp_law.
      
End Pullback_Composition.


Section pullback_coprod.
  Context {C : category} {B : precategory}.
  Context {R : Monad B}{S : Monad B} (f : Monad_Mor R S).

  Context {O : UU}.
  Context {cpC : Coproducts O C}.

  Let cpLM (X : Monad B) := LModule_Coproducts C  X cpC.
  Let cpFunc := Coproducts_functor_precat _ B _ cpC (homset_property C).

  Context (α : O -> LModule S C ).

  Let αF : O -> functor B C := fun o => α o.
  Let pbm_α : O -> LModule R C := fun o => pb_LModule f (α o).

  Definition pbm_coprod := pb_LModule f (CoproductObject _ _ (cpLM _ α)).
  Definition coprod_pbm : LModule _ _ := CoproductObject _ _ (cpLM _ pbm_α).

  Lemma coprod_pbm_to_pbm_coprod_aux : 
    ∏ c : B,
          (LModule_coproduct_mult cpC (homset_property C) pbm_α) c =
          (pb_LModule_σ f (CoproductObject O (precategory_LModule S C) (cpLM S α))) c.
  Proof.
    intro b.
    apply pathsinv0.
    apply CoproductOfArrows_comp.
  Defined.

  Definition coprod_pbm_to_pbm_coprod : LModule_Mor  _ coprod_pbm pbm_coprod :=
    LModule_M1_M2 _ _  coprod_pbm_to_pbm_coprod_aux.

End pullback_coprod.

Section pullback_binprod.
  Context {C : category} {B : precategory}.
  Context {R : Monad B}{S : Monad B} (f : Monad_Mor R S).

  Context {cpC : BinProducts C}.

  Let cpLM (X : Monad B) := LModule_BinProducts   X cpC (homset_property C).
  Let cpFunc := BinProducts_functor_precat  C _ cpC (homset_property C) .

  Context (a b : LModule S C ).

  (* Let αF : O -> functor B C := fun o => α o. *)
  (* Let pbm_α : O -> LModule R C := fun o => pb_LModule f (α o). *)

  Local Notation BPO := (BinProductObject _ ).

  Definition pbm_binprod := pb_LModule f (BPO (cpLM _ a b)).
  Definition binprod_pbm : LModule _ _ := BPO (cpLM _ (pb_LModule f a)(pb_LModule f b)).


  Lemma binprod_pbm_to_pbm_eq_mult (c : B) :
  (LModule_binproduct_mult cpC (homset_property C) (pb_LModule f a) (pb_LModule f b)) c =
  (pb_LModule_σ f (BPO (cpLM S a b))) c.
  Proof.
    apply pathsinv0.
    apply BinProductOfArrows_comp.
  Defined.
  
  Definition binprod_pbm_to_pbm_iso : iso (C:= precategory_LModule _ _)  binprod_pbm pbm_binprod :=
    LModule_M1_M2_iso _ _ binprod_pbm_to_pbm_eq_mult (homset_property _).
  
  Definition binprod_pbm_to_pbm_binprod : LModule_Mor  _ binprod_pbm pbm_binprod :=
    morphism_from_iso _ _ _ binprod_pbm_to_pbm_iso.

End pullback_binprod.

Section pullback_deriv.
  Context {C : precategory}
          (o : C) (* derivation X ↦ X + o *)
          (bcpC : limits.bincoproducts.BinCoproducts C )
          {D : category}.
          


  Let MOD (R : Monad C) := (precategory_LModule R D).
  Context {R S : Monad C} (f : Monad_Mor R S) (M : LModule S D).
  Local Notation "M '" := (LModule_deriv o bcpC M) (at level 30).


  Local Notation pb_d := (pb_LModule f (M ')).
  Local Notation d_pb := ((pb_LModule f M ) ').

  Lemma pb_deriv_to_deriv_eq_mult c :
    # M (BinCoproductOfArrows C (bcpC o (R c)) (bcpC o (S c)) (identity o) (pr1 f c)) · 
      (# (pr1 M)
         (BinCoproductArrow C (bcpC o (S c)) (BinCoproductIn1 C (bcpC o c) · pr1 (η S) (bcpC o c))
                            (# (pr1 S) (BinCoproductIn2 C (bcpC o c)))) · pr1 (lm_mult S M) (bcpC o c)) =
    # (pr1 M)
      (BinCoproductArrow C (bcpC o (R c)) (BinCoproductIn1 C (bcpC o c) · pr1 (η R) (bcpC o c))
                         (# (pr1 R) (BinCoproductIn2 C (bcpC o c)))) · (# (pr1 M) (pr1 f (bcpC o c)) · 
                                                                          (lm_mult S M) (bcpC o c)).
  Proof.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    do 2 rewrite <- functor_comp.
    apply maponpaths.
    etrans;[ apply precompWithBinCoproductArrow|].
    rewrite id_left.
    rewrite postcompWithBinCoproductArrow.
    apply map_on_two_paths.
    - rewrite <- assoc.
      apply cancel_precomposition.
      apply pathsinv0.
      apply Monad_Mor_η.
    - apply pathsinv0.
      apply nat_trans_ax.
  Qed.
  Definition pb_deriv_to_deriv_pb_iso :
    iso (C := MOD R) pb_d d_pb :=
    LModule_M1_M2_iso (pb_LModule_laws f (M '))
                      (LModule_comp_laws (deriv_dist_is_monad_dist o bcpC R) (pb_LModule f M))
                      pb_deriv_to_deriv_eq_mult
                      (homset_property D).


End pullback_deriv.
