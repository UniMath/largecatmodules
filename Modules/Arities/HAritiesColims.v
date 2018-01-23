(* colimits are computed pointwise
 *)

(**
It is the product of modules
Then it induces a morphism
*)
(* TODO : Faire les mêmes choses pour les limites de Modules *)
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import Modules.Arities.aritiesalt.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.LModuleColims.
Require Import Modules.Prelims.LModPbCommute.
Require Import Modules.Prelims.CoproductsComplements.

Local Open Scope cat.

(*
Lemma compfNat 
   {C : precategory} {g : graph} {d1 d2 d3 : diagram g C}  
   
   {f : ∏ u : vertex g, C ⟦ dob d1 u, dob d2 u ⟧}
  (fNat : ∏ (u v : vertex g) (e : edge u v), dmor d1 e · f v = f u · dmor d2 e) 
   {f2 : ∏ u : vertex g, C ⟦ dob d2 u, dob d3 u ⟧}
   (fNat2 : ∏ (u v : vertex g) (e : edge u v), dmor d2 e · f2 v = f2 u · dmor d3 e)
   (f3 := fun u => f u · f2 u)
   :
   ∏ (u v : vertex g) (e : edge u v), dmor d1 e · f3 v = f3 u · dmor d3 e .
  intros u v e.
  etrans;[apply assoc|].
  etrans;[apply maponpaths_2; apply fNat|].
  etrans;[|apply assoc].
  etrans;[|apply maponpaths; apply fNat2].
  apply pathsinv0.
  apply assoc.
Qed.
*)
(*
Lemma compColimOfArrows
   (C : precategory) (g : graph) (d1 d2 d3 : diagram g C) (CC1 : ColimCocone d1) 
   (CC2 : ColimCocone d2)(CC3 : ColimCocone d3)
   (f : ∏ u : vertex g, C ⟦ dob d1 u, dob d2 u ⟧)
  (fNat : ∏ (u v : vertex g) (e : edge u v), dmor d1 e · f v = f u · dmor d2 e) 
   (f2 : ∏ u : vertex g, C ⟦ dob d2 u, dob d3 u ⟧)
  (fNat2 : ∏ (u v : vertex g) (e : edge u v), dmor d2 e · f2 v = f2 u · dmor d3 e) 
  (x : C) (cc : cocone d2 x) :
  colimOfArrows CC1 CC2 f fNat · colimOfArrows CC2 CC3 f2 fNat2 =
  colimOfArrows CC1 CC3 (fun z => f z · f2 z) (compfNat  fNat fNat2).
  etrans;[apply precompWithColimOfArrows|].
  cbn.
  unfold colimOfArrows.
  apply maponpaths.
  Abort.
*)
(*

  use map_on_two_paths.
  maponpaths
  apply maponpaths2.

  reflexivity.
.fNat · colimOfArrows CC2 CC3 f2 fNat2 .
  colimOfArrows CC1 CC3 (fun 
  colimArrow CC1 x
    (mk_cocone (λ u : vertex g, f u · coconeIn cc u)
       (preCompWithColimOfArrows_subproof CC1 CC2 f fNat x cc)).
*)
(* forget ful functor from Modules to functors *)

(* TODO déplacer ça dans aritiesalt.v *)

Section ColimsHAr.
  Context 
          {C : category}
          {g : graph} (colims_g : Colims_of_shape g C)
          (lims_g : Lims_of_shape g C).
  Let hsC := (homset_property C).
          (* (hsB : has_homsets B) *)
  Let coMod R := (LModule_Colims_of_shape C (B := C) R _ colims_g).
  Let limMod R := (LModule_Lims_of_shape C (B := C) R _ lims_g).

  (* Local Notation limMod := (LModule_Lims_of_shape _ B _ hsC colims_g). *)
  (* Local Notation coFunc := (ColimsFunctorCategory_of_shape _ B _ hsC colims_g). *)
  (* Local Notation limFunc := (LimsFunctorCategory_of_shape _ B _ hsC lims_g). *)
  (* Local Notation bpFunct := *)
  (*   (BinProducts_functor_precat B C bpC hsC (M : functor _ _) (N : functor _ _)). *)

  (* Definition LModule_colim_functor : functor _ _ := *)
  (*   BinProductObject  _ bpFunct. *)
  Local Notation MOD R := (precategory_LModule R C).
  Local Notation HAR := (arity_precategory (C:=C)).
  Variable (d : diagram g HAR).
  (* TODO generalize this kind of construction : composition of a diagram and a functor
(here the forget ful functor MOD --> [B , C])
   *)
  Let FORGET R := (forget_HAr (C:=C) R ).
  Let d' R := (  mapdiagram (FORGET R) d : diagram g (MOD R) ).
  (* The natural candidate *)
  Let  F R := (colim (coMod _ (d' R)) : LModule _ _).
  Let  F' R := (lim (limMod _ (d' R)) : LModule _ _).
  (* Local Notation BP := (binproduct_functor bpC). *)

  (* Is there a lemma that state the existence of a natural transformation
  (A x B) o R --> A o R x B o R  ? *)
  (* TODO define it without nat_trans *)
  Definition HAr_colim_on_mor (R S : Monad C) (f : Monad_Mor R S) :
    LModule_Mor _ (F R) (pb_LModule f (F S)).
  Proof.
  eapply (compose (C:= MOD _)); [| apply pb_LModule_colim_iso].
  use  colimOfArrows.
  - intro u.
    exact ((#(dob d u : arity _))%ar f).
  - abstract (intros u v e;
    apply LModule_Mor_equiv;[apply homset_property|];
    apply pathsinv0;
    apply arity_Mor_ax).
  Defined.

  Definition HAr_lim_on_mor (R S : Monad C) (f : Monad_Mor R S) :
    LModule_Mor _ (F' R) (pb_LModule f (F' S)).
  Proof.
  eapply (compose (C:= MOD _)); [| apply pb_LModule_lim_iso].
  use  limOfArrows.
  - intro u.
    exact ((#(dob d u : arity _))%ar f).
  - abstract(intros u v e;
    apply LModule_Mor_equiv;[apply homset_property|];
    apply arity_Mor_ax).
  Defined.

  Definition HAr_colim_arity_data : arity_data := _ ,, HAr_colim_on_mor.
  Definition HAr_lim_arity_data : arity_data := _ ,, HAr_lim_on_mor.

  Lemma HAr_colim_is_arity : is_arity HAr_colim_arity_data.
  Proof.
    split.
    - intros R c.
      apply pathsinv0.
      apply colim_endo_is_identity.
      intro u.
      cbn.
      rewrite id_right.
      set (cc := colims_g _).
      etrans;[apply (colimArrowCommutes  cc)|].
      cbn.
      etrans;[|apply id_left].
      apply maponpaths_2.
      apply arity_id.
    - intros U V W m n.
      apply LModule_Mor_equiv;[apply homset_property|].
      apply nat_trans_eq;[apply homset_property|].
      intro c.
      cbn.
      repeat rewrite id_right.
      apply pathsinv0.
      apply colimArrowUnique.
      intro u.
      cbn.
      etrans.
      {
        etrans;[apply assoc|].
        apply maponpaths_2.
        set (cc := colims_g _).
        apply (colimArrowCommutes cc).
      }
      cbn.
      etrans.
      {
        cbn.
        rewrite <- assoc.
        apply maponpaths.
        set (cc := colims_g _).
        apply (colimArrowCommutes cc).
        }
      cbn.
      rewrite assoc.
      apply maponpaths_2.
      apply pathsinv0.
      etrans.
      {
      assert (h := arity_comp (dob d u) m n).
      eapply LModule_Mor_equiv in h; try apply homset_property.
      eapply nat_trans_eq_pointwise in h.
      apply h.
      }
      cbn.
      now rewrite id_right.
  Qed.
  Lemma HAr_lim_is_arity : is_arity HAr_lim_arity_data.
  Proof.
    split.
    - intros R c.
      apply pathsinv0.
      apply lim_endo_is_identity.
      intro u.
      cbn.
      rewrite id_right.
      set (cc := lims_g _).
      etrans;[apply (limArrowCommutes  cc)|].
      cbn.
      etrans;[|apply id_right].
      apply maponpaths.
      apply arity_id.
    - intros U V W m n.
      apply LModule_Mor_equiv;[apply homset_property|].
      apply nat_trans_eq;[apply homset_property|].
      intro c.
      cbn.
      repeat rewrite id_right.
      apply pathsinv0.
      apply limArrowUnique.
      intro u.
      cbn.
      etrans.
      {
        rewrite <- assoc.
        (* etrans;[apply assoc|]. *)
        apply maponpaths.
        set (cc := lims_g _).
        apply (limArrowCommutes cc).
      }
      cbn.
      etrans.
      {
        cbn.
        rewrite assoc.
        apply maponpaths_2.
        set (cc := lims_g _).
        apply (limArrowCommutes cc).
        }
      cbn.
      rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      etrans.
      {
      assert (h := arity_comp (dob d u) m n).
      eapply LModule_Mor_equiv in h; try apply homset_property.
      eapply nat_trans_eq_pointwise in h.
      apply h.
      }
      cbn.
      now rewrite id_right.
  Qed.

  Definition HAr_colim : arity _ :=
    _ ,, HAr_colim_is_arity.

  Definition HAr_lim : arity _ :=
    _ ,, HAr_lim_is_arity.



  Lemma HAr_coconeIn_laws v : 
    is_arity_Mor 
                      (dob d v : arity  _)  HAr_colim
      (fun R => (coconeIn (colimCocone (coMod R (d' R))) v   )).
  Proof.
    intros X Y f.
    (* not necessary but more convenienet *)
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn.
    rewrite id_right.
    set (cc1 := colims_g _).
    set (cc2 := colims_g _).
    apply pathsinv0.
    cbn.
    apply (colimArrowCommutes cc2).
  Qed.
  Lemma HAr_coneOut_laws v : 
    is_arity_Mor 
                  HAr_lim    (dob d v : arity  _)  
      (fun R => (coneOut (limCone (limMod R (d' R))) v   )).
  Proof.
    intros X Y f.
    (* not necessary but more convenienet *)
    apply nat_trans_eq;[apply homset_property|].
    intro x.
    cbn.
    rewrite id_right.
    set (cc1 := lims_g _).
    set (cc2 := lims_g _).
    cbn.
    apply (limArrowCommutes cc1).
  Qed.

  Definition HAr_coconeIn v : arity_precategory ⟦ dob d v, HAr_colim ⟧ :=
    _ ,, HAr_coconeIn_laws v.

  Definition HAr_coneOut v : arity_precategory ⟦ HAr_lim, dob d v ⟧ :=
    _ ,, HAr_coneOut_laws v.

  Lemma HAr_coconeIn_commutes (u v : vertex g) (e : edge u v) :
    dmor d e · HAr_coconeIn v = HAr_coconeIn u.
  Proof.
    apply arity_Mor_eq.
    intro R.
    apply (coconeInCommutes (colimCocone (coMod R (d' R)))).
  Defined.
  Lemma HAr_coneOut_commutes (u v : vertex g) (e : edge u v) :
      HAr_coneOut u · dmor d e = HAr_coneOut v.
  Proof.
    apply arity_Mor_eq.
    intro R.
    apply (coneOutCommutes (limCone (limMod _ (d' R)))).
  Defined.


  Definition HAr_colim_cocone : cocone d HAr_colim :=
    mk_cocone HAr_coconeIn HAr_coconeIn_commutes.

  Definition HAr_lim_cone : cone d HAr_lim :=
    mk_cone HAr_coneOut HAr_coneOut_commutes.

  Lemma HAr_colimArrow_laws {M : arity C} (cc : cocone d M) :
    is_arity_Mor
       (  HAr_colim) (M)
      (fun R => colimArrow  (coMod R (d' R)) (M R) (mapcocone (FORGET R) d cc)  ).
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    repeat rewrite id_right.
    apply pathsinv0.
    etrans;[apply postcompWithColimArrow|].
    apply pathsinv0.
    apply colimArrowUnique.
    intro u.
    cbn.
    etrans.
    {
      rewrite assoc.
      apply maponpaths_2.
      set (cc1 := colims_g _).
      apply (colimArrowCommutes cc1).
    }
    cbn.
    etrans.
    {
      rewrite <- assoc.
      apply maponpaths.
      set (cc1 := colims_g _).
      apply (colimArrowCommutes cc1).
    }
    cbn.
    apply arity_Mor_ax_pw.
  Qed.
  Lemma HAr_limArrow_laws {M : arity C} (cc : cone d M) :
    is_arity_Mor
      M  (  HAr_lim) 
      (fun R => limArrow  (limMod R (d' R)) (M R) (mapcone (FORGET R) d cc)  ).
  Proof.
    intros R S f.
    apply nat_trans_eq;[apply homset_property|].
    intro c.
    cbn.
    repeat rewrite id_right.
    apply pathsinv0.
    etrans;[apply postCompWithLimArrow|].
    apply pathsinv0.
    apply limArrowUnique.
    intro u.
    cbn.
    etrans.
    {
      rewrite <- assoc.
      apply maponpaths.
      set (cc1 := lims_g _).
      apply (limArrowCommutes cc1).
    }
    cbn.
    apply pathsinv0.
    etrans.
    {
      rewrite assoc.
      apply maponpaths_2.
      set (cc1 := lims_g _).
      apply (limArrowCommutes cc1).
    }
    cbn.
    apply pathsinv0.
    apply arity_Mor_ax_pw.
  Qed.


  Definition HAr_colimArrow {M : arity _} (cc : cocone d M) :
    arity_Mor  HAr_colim M := _ ,, HAr_colimArrow_laws  cc.

  Definition HAr_limArrow {M : arity C} (cc : cone d M) :
    arity_Mor  M HAr_lim := _ ,, HAr_limArrow_laws  cc.

  Lemma HAr_isColimCocone : isColimCocone _ _ HAr_colim_cocone.
    intros M cc.
    use unique_exists.
    - exact (HAr_colimArrow cc).
    - intro v.
      apply arity_Mor_eq.
      intro R.
      apply (colimArrowCommutes (coMod _ (d' R))).
    - intro y.
      cbn -[isaprop].
      apply  impred_isaprop.
      intro u.
      use arity_category_has_homsets.
    - intros y h.
      apply arity_Mor_eq.
      intro R.
      apply (colimArrowUnique (coMod _ (d' R))).
      intro u.
      apply (  maponpaths (fun z => pr1 z R) (h u)).
  Defined.
  Lemma HAr_isLimCone : isLimCone _ _ HAr_lim_cone.
    intros M cc.
    use unique_exists.
    - exact (HAr_limArrow cc).
    - intro v.
      apply arity_Mor_eq.
      intro R.
      apply (limArrowCommutes (limMod _ (d' R))).
    - intro y.
      cbn -[isaprop].
      apply  impred_isaprop.
      intro u.
      use arity_category_has_homsets.
    - intros y h.
      apply arity_Mor_eq.
      intro R.
      apply (limArrowUnique (limMod _ (d' R))).
      intro u.
      apply (  maponpaths (fun z => pr1 z R) (h u)).
  Defined.


  Definition HAr_ColimCocone : ColimCocone d :=
    mk_ColimCocone  _ _ _  HAr_isColimCocone.

  Definition HAr_LimCone : LimCone d :=
    mk_LimCone  _ _ _  HAr_isLimCone.

End ColimsHAr.

Definition HAr_Colims_of_shape {C : category}
           (g : graph)
           (colims_g : Colims_of_shape g C)
            : Colims_of_shape g (arity_precategory) :=
   HAr_ColimCocone  (C:= C) (g := g) colims_g.
Definition HAr_Lims_of_shape {C : category}
           (g : graph)
           (lims_g : Lims_of_shape g C)
            : Lims_of_shape g (arity_precategory) :=
   HAr_LimCone  (C:= C) (g := g) lims_g.

