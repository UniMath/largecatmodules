(* colimits are computed pointwise
Actually this is not needed for our formalization
limits/colimits of modules are computes pointwise
forget ful functors from modules to functors

Proofs for limits are very similar to proof from colimits

Proof that the pullbacks preserve lims/colims

TODO: refaire en supposant les colimites/limites dans la catégories des foncteurs
plutôt que dans la catégorie cible. Mais est-ce possible ? Comment définir la multiplication
dans ce cas (ltmult) ?
 *)

(**
It is the product of modules
Then it induces a morphism
*)
(* TODO : Faire les mêmes choses pour les limites de Modules *)
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import Modules.Prelims.modules. (* for the definition of the forgetful functor *)
Require Import Modules.Prelims.LModPbCommute. (* for the definition of the iso *)

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
  etrans;[apply cancel_postcomposition; apply fNat|].
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
(* TODO déplacer ça dans LModule.v *)

Section ColimsModule.
  Context 
          {C : precategory}
          {g : graph} (colims_g : Colims_of_shape g C)
          (lims_g : Lims_of_shape g C)
          {B:precategory} {R:Monad B}
          (* (hsB : has_homsets B) *)
          (hsC : has_homsets C).
  Local Notation coFunc := (ColimsFunctorCategory_of_shape _ B _ hsC colims_g).
  Local Notation limFunc := (LimsFunctorCategory_of_shape _ B _ hsC lims_g).
  (* Local Notation bpFunct := *)
  (*   (BinProducts_functor_precat B C bpC hsC (M : functor _ _) (N : functor _ _)). *)

  (* Definition LModule_colim_functor : functor _ _ := *)
  (*   BinProductObject  _ bpFunct. *)
  Local Notation MOD := (precategory_LModule R (C ,, hsC)).
  Variable (d : diagram g MOD).
  (* TODO generalize this kind of construction : composition of a diagram and a functor
(here the forget ful functor MOD --> [B , C])
   *)
  Local Notation FORGET := (forget_LMod R (C ,, hsC)).
  Local Notation d' := (  mapdiagram FORGET d : diagram g [B , C , hsC] ).
  (* The natural candidate *)
  Local Notation F := (colim (coFunc d') : functor _ _).
  Local Notation F' := (lim (limFunc d') : functor _ _).
  (* Local Notation BP := (binproduct_functor bpC). *)

  (* Is there a lemma that state the existence of a natural transformation
  (A x B) o R --> A o R x B o R  ? *)
  (* TODO define it without nat_trans *)
  Definition LModule_colim_mult_data (x : B) : C ⟦ (R ∙ F) x, F x ⟧.
    use colimOfArrows.
    - intro v.
       exact ( lm_mult R (dob d v : LModule _ _) x). 
    - intros u v e.
      cbn.
        now apply  LModule_Mor_σ.
  Defined.

  Definition LModule_lim_mult_data (x : B) : C ⟦ (R ∙ F') x, F' x ⟧.
    use limOfArrows.
    - intro v.
       exact ( lm_mult R (dob d v : LModule _ _) x). 
    - intros u v e.
      cbn.
      apply pathsinv0.
       apply  LModule_Mor_σ.
  Defined.
  (*
      apply lt_mult_σ.
  (* Definition LModule_colim_mult_data  : [B, C , hsC] ⟦ (R ∙ F) , F  ⟧. *)
    apply colimArrow.
    use mk_cocone.
    - intro v.
      eapply compose; revgoals.
      + apply (colimIn _ v).
      + exact ( lm_mult R (dob d v : LModule _ _) x). 
    - intros u v e.
      cbn.
      (*
<<<
           σ u                in_(u x)
d u (R x) ----------> d u x -------
    |                              |
    |                              |
    |                              |
d e |                              |
    |                              |
    V                              V
d v (R x) ---------> d v x ------> colim d x
           σ v               in_(v x)

>>>
qu'on complète par propriété de [d e] en temps que morphisme de module



*)
      abstract(
      rewrite assoc;
      etrans;[
        apply cancel_postcomposition;
        now apply  LModule_Mor_σ
               |] ;
      rewrite <- assoc;
      apply maponpaths;
      cbn;
      set (dpw := diagram_pointwise _ _ _);
      apply ( colimInCommutes (d := dpw))).
  Defined.
(* Local Notation σ := (lm_mult _). *)
*)

  Lemma LModule_colim_mult_is_nat_trans : is_nat_trans _ _  LModule_colim_mult_data.
  Proof.
    intros x y f.
    cbn.
    unfold LModule_colim_mult_data.
    (* par unicité de la colimite *)

    etrans; [use precompWithColimOfArrows|].
    apply pathsinv0            .
    (* etrans; [use precompWithColimOfArrows|]. *)
    apply colimArrowUnique.
    intro v.
    cbn.
    
    apply pathsinv0.
    etrans;[apply assoc|].
    etrans.
    {
      apply cancel_postcomposition.
      apply (nat_trans_ax (lm_mult R (dob d v : LModule _ _))).
    }
    
    apply pathsinv0.
    etrans;[apply assoc|].
    etrans.
    {
      apply cancel_postcomposition.
      set (CC1 := colims_g _ ).
      set (CC2 := colims_g _ ).
      eapply (colimOfArrowsIn _ _ CC1 CC2).
    }
    simpl.
    repeat rewrite <- assoc.
    apply maponpaths.
    unfold ColimFunctor_mor.
    set (CC1 := colims_g _ ).
    set (CC2 := colims_g _ ).
    eapply (colimOfArrowsIn _ _ CC1 CC2).
  Qed.
  Lemma LModule_lim_mult_is_nat_trans : is_nat_trans _ _  LModule_lim_mult_data.
  Proof.
    intros x y f.
    cbn.
    unfold LModule_lim_mult_data.
    (* par unicité de la colimite *)

    etrans; [use postCompWithLimOfArrows|].
    apply pathsinv0            .
    (* etrans; [use precompWithColimOfArrows|]. *)
    apply limArrowUnique.
    intro v.
    cbn.
    
    (* apply pathsinv0. *)
    etrans;[|apply assoc].
    etrans; revgoals.
    {
      apply maponpaths.
      apply pathsinv0.
      apply (nat_trans_ax (lm_mult R (dob d v : LModule _ _))).
    }
    
    apply pathsinv0.
    etrans;[|apply assoc].
    etrans; revgoals.
    {
      apply maponpaths.
      unfold LimFunctor_mor.
      cbn.
      set (CC1 := lims_g _ ).
      set (CC2 :=  lims_g _ ).
      eapply pathsinv0.
      eapply (limOfArrowsOut _ _ CC1 CC2).
    }
    simpl.
    repeat rewrite  assoc.
    apply cancel_postcomposition.
    apply pathsinv0.
    (* unfold LimFunctor_mor. *)
    set (CC2 := lims_g _ ).
    set (CC1 := lims_g _ ).
    apply (limOfArrowsOut _ _ CC1 CC2).
  Qed.

  Definition LModule_colim_mult : R ∙ F ⟹ F :=
    (_ ,, LModule_colim_mult_is_nat_trans).

  Definition LModule_lim_mult : R ∙ F' ⟹ F' :=
    (_ ,, LModule_lim_mult_is_nat_trans).
  

  Definition LModule_colim_data : LModule_data R C :=
    (F ,, LModule_colim_mult).

  Definition LModule_lim_data : LModule_data R C :=
    (F' ,, LModule_lim_mult).

  Lemma LModule_colim_laws : LModule_laws _ LModule_colim_data.
  Proof.
    split.
    - intro x.
      cbn.
      etrans; [use precompWithColimOfArrows|].
      apply pathsinv0            .
      (* etrans; [use precompWithColimOfArrows|]. *)
      apply colimArrowUnique.
      intro u.
      cbn.
      rewrite id_right.
      rewrite assoc.
      apply pathsinv0.
      etrans;[|apply id_left].
      apply cancel_postcomposition.
      apply LModule_law1.
    - intro x.
      cbn.
      etrans; [use precompWithColimOfArrows|].
      apply pathsinv0            .
      (* etrans; [use precompWithColimOfArrows|]. *)
      apply colimArrowUnique.
      intro u.
      cbn.
      etrans; [apply assoc|].
      etrans.
      {
        apply cancel_postcomposition.
        unfold LModule_colim_mult_data.
        cbn.
        set (CC1 := colims_g _ ).
        set (CC2 := colims_g _ ).
        apply (colimOfArrowsIn _ _ CC1 CC2).
      }
      cbn.
      rewrite <- assoc.
      etrans.
      {
        apply maponpaths.
        unfold LModule_colim_mult_data.
        cbn.
        set (CC1 := colims_g _ ).
        set (CC2 := colims_g _ ).
        apply (colimOfArrowsIn _ _ CC1 CC2).
      }
      cbn.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0.
      apply LModule_law2.
  Qed.
  Lemma LModule_lim_laws : LModule_laws _ LModule_lim_data.
  Proof.
    split.
    - intro x.
      cbn.
      etrans; [use postCompWithLimArrow|].
      apply pathsinv0            .
      (* etrans; [use precompWithColimOfArrows|]. *)
      apply limArrowUnique.
      intro u.
      cbn.
      rewrite id_left.
      apply pathsinv0.
      etrans;[apply assoc|].
      etrans.
      {
        apply cancel_postcomposition.
        unfold LimFunctor_mor.
        cbn.
        set (CC2 := lims_g _ ).
        set (CC1 := lims_g _ ).
        apply (limOfArrowsOut _ _ CC1 CC2).
      }
      rewrite <-assoc.
      etrans;[|apply id_right].
      apply maponpaths.
      apply LModule_law1.
    - intro x.
      cbn.
      etrans; [use postCompWithLimOfArrows|].
      apply pathsinv0            .
      apply limArrowUnique.
      intro u.
      cbn.
      etrans.
      {
        rewrite <- assoc.
        apply maponpaths.

        unfold LModule_lim_mult_data.
        cbn.
        set (CC1 := lims_g _ ).
        set (CC2 := lims_g _ ).
        apply (limOfArrowsOut _ _ CC1 CC2).
      }
      cbn.
      etrans.
      {
        rewrite assoc.
        apply cancel_postcomposition.
        unfold LModule_lim_mult_data.
        cbn.
        set (CC2 := lims_g _ ).
        set (CC1 := lims_g _ ).
        apply (limOfArrowsOut _ _ CC1 CC2).
      }
      cbn.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      apply LModule_law2.
  Qed.

  Definition LModule_colim : LModule R C := (_ ,, LModule_colim_laws).
  Definition LModule_lim : LModule R C := (_ ,, LModule_lim_laws).

  Lemma LModule_coconeIn_laws v : 
    LModule_Mor_laws R
                     (T := (dob d v : LModule _ _)) (T' := LModule_colim)
      ((coconeIn (colimCocone (coFunc d')) v : nat_trans _ _) ).
  Proof.
    intro c.
    cbn.
    unfold LModule_colim_mult_data.
    set (CC1 := colims_g _ ).
    set (CC2 := colims_g _ ).
    apply (colimOfArrowsIn _ _ CC1 CC2).
  Defined.
  Lemma LModule_coneOut_laws v : 
    LModule_Mor_laws R
                    (T := LModule_lim) (T' := (dob d v : LModule _ _)) 
      ((coneOut (limCone (limFunc d')) v : nat_trans _ _) ).
  Proof.
    intro c.
    cbn.
    unfold LModule_lim_mult_data.
    set (CC1 := lims_g _ ).
    set (CC2 := lims_g _ ).
    apply pathsinv0.
    apply (limOfArrowsOut _ _ CC1 CC2).
  Defined.

  Definition LModule_coconeIn v : MOD ⟦ dob d v, LModule_colim ⟧ :=
    _ ,, LModule_coconeIn_laws v.

  Definition LModule_coneOut v : MOD ⟦ LModule_lim, dob d v ⟧ :=
    _ ,, LModule_coneOut_laws v.

  Lemma LModule_coconeIn_commutes (u v : vertex g) (e : edge u v) :
    dmor d e · LModule_coconeIn v = LModule_coconeIn u.
  Proof.
    apply LModule_Mor_equiv.
    - exact hsC.
    - apply (coconeInCommutes (colimCocone (coFunc d'))).
  Defined.
  Lemma LModule_coneOut_commutes (u v : vertex g) (e : edge u v) :
      LModule_coneOut u · dmor d e = LModule_coneOut v.
  Proof.
    apply LModule_Mor_equiv.
    - exact hsC.
    - apply (coneOutCommutes (limCone (limFunc d'))).
  Defined.


  Definition LModule_colim_cocone : cocone d LModule_colim :=
    mk_cocone LModule_coconeIn LModule_coconeIn_commutes.

  Definition LModule_lim_cone : cone d LModule_lim :=
    mk_cone LModule_coneOut LModule_coneOut_commutes.

  Definition LModule_colimArrow_laws {M : LModule R C} (cc : cocone d M) :
    LModule_Mor_laws
      _ (T := LModule_colim) (T' := M)
      (colimArrow  (coFunc d') (M : functor _ _) (mapcocone FORGET d cc) : nat_trans _ _ ).
  Proof.
    intro c.
    apply pathsinv0.
    cbn.
    unfold LModule_colim_mult_data.
    cbn.
    etrans;[apply precompWithColimOfArrows|].
    apply pathsinv0.
    apply colimArrowUnique.
    intro u.
    cbn.
    etrans.
    {
      etrans;[apply assoc|].
      apply cancel_postcomposition.
      set (CC1 := colims_g _ ).
      apply (colimArrowCommutes CC1).
    }
    apply LModule_Mor_σ.
  Qed.

  Definition LModule_limArrow_laws {M : LModule R C} (cc : cone d M) :
    LModule_Mor_laws
      _ (T := M)(T' := LModule_lim) 
      (limArrow  (limFunc d') (M : functor _ _) (mapcone FORGET d cc) : nat_trans _ _ ).
  Proof.
    intro c.
    cbn.
    unfold LModule_lim_mult_data.
    cbn.
    etrans;[apply postCompWithLimOfArrows|].
    apply pathsinv0.
    apply limArrowUnique.
    intro u.
    cbn.
    etrans.
    {
      rewrite <- assoc.
      apply maponpaths.
      set (CC1 := lims_g _ ).
      apply (limArrowCommutes CC1).
    }
    apply pathsinv0.
    apply LModule_Mor_σ.
  Qed.

  Definition LModule_colimArrow {M : LModule R C} (cc : cocone d M) :
    LModule_Mor _ LModule_colim M := _ ,, LModule_colimArrow_laws  cc.

  Definition LModule_limArrow {M : LModule R C} (cc : cone d M) :
    LModule_Mor _ M LModule_lim := _ ,, LModule_limArrow_laws  cc.

  Lemma LModule_isColimCocone : isColimCocone _ _ LModule_colim_cocone.
    intros M cc.
    use unique_exists.
    - exact (LModule_colimArrow cc).
    - intro v.
      apply LModule_Mor_equiv;[exact hsC|].
      apply (colimArrowCommutes (coFunc d')).
    - intro y.
      cbn -[isaprop].
      apply  impred_isaprop.
      intro u.
      use has_homsets_LModule.
    - cbn.
      intros y h.
      apply LModule_Mor_equiv;[exact hsC|].
      apply (colimArrowUnique (coFunc d')).
      intro u.
      exact (  maponpaths pr1 (h u)).
  Defined.

  Lemma LModule_isLimCone : isLimCone _ _ LModule_lim_cone.
    intros M cc.
    use unique_exists.
    - exact (LModule_limArrow cc).
    - intro v.
      apply LModule_Mor_equiv;[exact hsC|].
      apply (limArrowCommutes (limFunc d')).
    - intro y.
      cbn -[isaprop].
      apply  impred_isaprop.
      intro u.
      use has_homsets_LModule.
    - cbn.
      intros y h.
      apply LModule_Mor_equiv;[exact hsC|].
      apply (limArrowUnique (limFunc d')).
      intro u.
      exact (  maponpaths pr1 (h u)).
  Defined.

  Definition LModule_ColimCocone : ColimCocone d :=
    mk_ColimCocone  _ _ _  LModule_isColimCocone.

  Definition LModule_LimCone : LimCone d :=
    mk_LimCone  _ _ _  LModule_isLimCone.

End ColimsModule.

Definition LModule_Colims_of_shape (C : category) {B : precategory}
           (R : Monad B)
           (g : graph)
           (colims_g : Colims_of_shape g C)
            : Colims_of_shape g (precategory_LModule R C) :=
   LModule_ColimCocone  colims_g (homset_property C).

Definition LModule_Lims_of_shape (C : category) {B : precategory}
           (R : Monad B)
           (g : graph)
           (lims_g : Lims_of_shape g C)
            : Lims_of_shape g (precategory_LModule R C) :=
   LModule_LimCone  lims_g (homset_property C).
                                         



Section pullback_lims.
  Context 
          {D : category}
          {g : graph} (colims_g : Colims_of_shape g D)
          (lims_g : Lims_of_shape g D)
          {C:category}.
          (* (hsB : has_homsets B) *)

  Let MOD (R : Monad C) := (precategory_LModule R D).
  Let cMod (R : Monad C) := LModule_Colims_of_shape D R g colims_g.
  Let lMod (R : Monad C) := LModule_Lims_of_shape D R g lims_g.

  Context {R S : Monad C} (f : Monad_Mor R S) (M : LModule S D).
  Variable (dS : diagram g (MOD S)).
  Let dR := mapdiagram (pb_LModule_functor f) dS .



  Let cS := colim (cMod S dS).
  Let lS :=   lim (lMod S dS).
  Let cR := colim (cMod R dR).
  Let lR :=   lim (lMod R dR).

  Lemma pb_colims_eq_mult (c : C) :
    (LModule_colim_mult colims_g (homset_property D) dR) c = (pb_LModule_σ f cS) c.
  Proof.
    simpl.
    unfold ColimFunctor_mor, LModule_colim_mult_data.
    etrans;[|eapply pathsinv0;apply precompWithColimOfArrows].
    apply colimArrowUnique.
    intro v.
    etrans;[apply colimOfArrowsIn|].
    cbn.
    apply pathsinv0.
    apply assoc.
  Qed.
  Lemma pb_lims_eq_mult (c : C) :
    (LModule_lim_mult lims_g (homset_property D) dR) c = (pb_LModule_σ f lS) c.
  Proof.
    simpl.
    unfold LimFunctor_mor, LModule_lim_mult_data.
    etrans;[|eapply pathsinv0;apply postCompWithLimOfArrows].
    apply limArrowUnique.
    intro v.
    etrans;[apply limOfArrowsOut|].
    cbn.
    apply assoc.
  Qed.

  Definition pb_LModule_colim_iso : iso (C := MOD R) cR (pb_LModule f cS) :=
    LModule_M1_M2_iso _ _ pb_colims_eq_mult (homset_property _).

  Definition pb_LModule_lim_iso : iso (C := MOD R) lR (pb_LModule f lS) :=
    LModule_M1_M2_iso _ _ pb_lims_eq_mult (homset_property _).
End pullback_lims.