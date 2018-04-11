(**

In this file :

- Proof that HSET has effective epis

- Proof that given a category D with pushouts, if a natural transformation 
between two functors of codomain D is an epi, then it is pointwise an epi 
(Colims_pw_epi).


- Proof that a natural transformation which is an epi when the codomain of
considered functors is the hSet category has a lifting property similar
to the previously mentionned for surjections.

- Proof that if a natural transformation is pointwise epi, then
 any pre-whiskering of it is also an epi.

Section leftadjoint : 
Preuve d'André à traduire.

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.SetValuedFunctors.

Require Import Modules.Arities.aritiesalt.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Arities.quotientrep.

Set Automatic Introduction.
  
  
(**
A morphism of arity F : a -> b induces a functor between representation Rep(b) -> Rep(a)

In this section we construct the left adjoint of this functor (which is defined whenever
F is an epimorphism)
*)

Section leftadjoint.

Local Notation "'SET'" := hset_category.
Local Notation CAT_ARITY := (@arity_category SET).
Local Notation REP := (rep_disp SET).

Variable (ax_choice : AxiomOfChoice.AxiomOfChoice_surj).

Context {a b : arity SET}
        (F : arity_Mor a b).

Section fix_rep_of_a.

Context (R : REP a).


Local Notation "## F" := (pr1 (pr1 (F)))(at level 3).

(**
On any set X we define the following equivalence relation on R X : 
   x ~ y
iff for any representation morphism f : R -> F*(S) (where S is a b-representation)
  f x = f y.


We will show that this relation satisfies the conditions necessary to 
define the quotient of a monad, and of a module over a monad.

*)

Definition equivc {X : SET} (x y : pr1 ( ## R X)) : UU
  := ∏ (S:REP b) ( f : R -->[F] S), ## f X x = ## f X y.

Lemma isaprop_equivc_xy (c : SET) x y : isaprop (equivc (X:=c) x y).
Proof.
  intros.
  apply impred_isaprop; intro S.
  apply impred_isaprop; intros f.
  apply setproperty.
Qed.

Definition equivc_xy_prop (X : SET) x y : hProp :=
  equivc (X:=X) x y ,, isaprop_equivc_xy X x y.

Definition hrel_equivc (X : SET) : hrel (##R X : hSet)
  := fun x y => equivc_xy_prop X x y.

Lemma iseqrel_equivc (X : SET) : iseqrel (hrel_equivc X).
Proof.
  unfold hrel_equivc, equivc_xy_prop, equivc; simpl;
  repeat split.
  - intros x y z. cbn.
    intros h1 h2 S f.
    rewrite h1,h2.
    apply idpath.
  - intros x y; cbn.
    intros h S f.
    symmetry.
    apply h.
Qed.

Definition eqrel_equivc (X : SET) : eqrel _ := _ ,, iseqrel_equivc X.

(** For any f : X -> Y, #R f is compatible with previous equivalence relation *)
Lemma congr_equivc (X Y : SET) (f:SET ⟦X , Y⟧)
  : iscomprelrelfun (eqrel_equivc X) (eqrel_equivc Y) (# (## R) f).
Proof.
  intros z z' eqz S g.
  assert (hg := nat_trans_ax (pr1 (pr1 g)) X Y f).
  apply toforallpaths in hg.
  etrans; [apply hg|].
  apply pathsinv0.
  etrans;[apply hg|].
  cbn.
  apply maponpaths. (* remove #S f *)
  cbn in eqz.
  apply pathsinv0, eqz.
Qed.

Arguments R' : simpl never.
Arguments projR : simpl never.

Let R' := R' congr_equivc.
Let projR := projR congr_equivc.
Let eq_projR_rel := eq_projR_rel congr_equivc.


(** R' est un pseudo objet initial au sens suivant :
     Quel que soit        g : R ---> S morphisme dans la catégorie des représentations de a
     il existe un unique  u : R'---> S tel que g = u o projR
C'est un pseudo objet car il reste à montrer que R' est bien dans la catégorie des représentations
de a et que u est un morphisme de modules.
*)



Section Instantiating_Quotient_Constructions.

(** We define short identifiers for the quotient constructions for 
    functors, monads, and modules (defined in previous files),
    for the equivalence relation induced by a morphism of representations [m]
    over a morphism of arities [F].
*)

Context {S : REP b} (m : R -->[ F] S). 

Lemma compat_m
  : ∏ (X : SET) (x y : (pr1 R X:hSet)),
    projR X x = projR X y → (pr1 m) X x = (pr1 m) X y.
Proof.
  intros X x y eqpr;
  apply eq_projR_rel in eqpr;
  use eqpr.
Qed.

Definition u : nat_trans (pr1 R') (## S).
Proof.
  apply (quotientmonad.u congr_equivc _ (pr1 m)).
  apply compat_m.
Defined.

Lemma u_def : ∏ x, ## m x = projR x · u x.
Proof.
  apply (quotientmonad.u_def).
Qed.

End Instantiating_Quotient_Constructions.


(** We show that the relation induced by a morphism of representations
    satisfies the conditions necessary to induce a quotient monad 
*)

Lemma compat_μ_projR : compat_μ_projR_def congr_equivc.
Proof.
  intros X x y hxy.
  apply rel_eq_projR.
  intros S f.
  rewrite comp_cat_comp.
  rewrite comp_cat_comp.
  apply pathsinv0.
  eapply changef_path.
  - symmetry.
    etrans; [ apply (Monad_Mor_μ (pr1 f)) |].
    etrans.
    { apply (cancel_postcomposition (C:=SET)).
      etrans.
      { apply cancel_postcomposition.
        apply u_def. }
      apply cancel_precomposition.
      apply maponpaths.
      apply u_def.  
    }
    etrans.
    { apply (cancel_postcomposition (C:=SET)).
      etrans.
      { symmetry; apply  (assoc (C:=SET) (projR (## R X)) (u f (## R X))).  } 
      apply cancel_precomposition.
      etrans.
      { symmetry. apply nat_trans_ax. }
      apply cancel_postcomposition.
      apply (functor_comp _ (projR X) (u f X)). 
    }
    repeat rewrite assoc.
    reflexivity.
  - cbn.
    do 3 apply maponpaths.
    apply pathsinv0.
    apply hxy.
Qed.
  
Let R'_monad  := R'_monad ax_choice congr_equivc compat_μ_projR.
Let projR_monad  := projR_monad ax_choice congr_equivc compat_μ_projR.

Definition u_monad {S} (m : R -->[ F] S) 
  : Monad_Mor (quotientmonad.R'_monad ax_choice congr_equivc compat_μ_projR) (pr1 S)
  := quotientmonad.u_monad ax_choice compat_μ_projR (S:=pr1 S) (pr1 m) (compat_m m).


(** * FIN DE LA TROISIEME ETAPE *)



Section R'Representation.

(** Goal: define a representation of [b]
    with underlying monad the quotient monad defined in the previous step
*)

(** R'_rep_τ is defined by the following diagram :
<<
                  rep_τ R
            a R  ----->  R
             |           |
         F R |           | projR
             v           |
            b R          |
             |           |
     b projR |           |
             v           v
           b R' -------> R'
                R'_rep_τ

>>
or rather the following diagram.
<<
                 rep_τ R
            a R  ----->  R
             |           |
     a projR |           | projR
             v           |
            a R'         |
             |           |
        F R' |           |
             v           v
            b R' ------> R'
                R'_rep_τ
>>

We need to show that for all x,y such that
F R' o a projR (x) = F R' o a projR (y), we have
  projR o rep_τ R (x) = projR o rep_τ R (y)

This is lemma [compat_rep_τ_projR]

*)


Section eq_mr.
   
Context {S : REP b} (m : R -->[ F] S).

Lemma cancel_ar_on {a'}
      {R'' (* : REP a*)}                  (*  *)
      (* {F' : CAT_ARITY ⟦ a', b' ⟧ *)
      {S' (* : REP b *)}
      (m2 m' : Monad_Mor R'' S')
      (X : SET) 
  : m2 = m' ->  (# a')%ar m2 X = (# a')%ar m' X .
Proof.
  intro e; induction e.
  apply idpath.
Qed.

Lemma Rep_mor_is_composition 
  : pr1 m = compose (C:=category_Monad _) projR_monad (u_monad m) .
Proof.
  use (invmap (Monad_Mor_equiv _ _ _)).
  apply (homset_property SET).
  apply nat_trans_eq.
  - apply (homset_property SET).
  - intro X'.
    apply (u_def m).
Qed.

Lemma eq_mr X 
  : rep_τ _ R X · ## m X 
    =
    pr1 (# a projR_monad)%ar X · (F (R'_monad ))%ar X 
        ·
        pr1 (# b (u_monad m))%ar X · rep_τ _ S X.
Proof.
  etrans. { apply rep_ar_mor_ax. }
  cpost _.
  etrans.
  { cpost _.
    etrans.
    { apply (cancel_ar_on _ _ _ Rep_mor_is_composition). }
    eapply nat_trans_eq_pointwise.
    apply maponpaths.
    apply arity_comp.
  }
  etrans;[|apply (assoc (C:=SET))].
  apply pathsinv0.
  etrans;[|apply (assoc (C:=SET))].
  cpre SET.
  apply pathsinv0.
  apply (arity_Mor_ax_pw F (u_monad m)).
Qed.

End eq_mr.

Open Scope arity_scope.

(**

<<<<

       hab
   a_R --> b_R'
    |     ^
    |    /
a_π |   / F_R'
    |  /
    V /
    a_R'

>>>>
where π := projR

 *)

Definition hab 
  : mor_disp
      (D:=bmod_disp_ob_mor _ _ )
      (a (pr1 R)) 
      (b  R'_monad)
      projR_monad.    (*: category_Monad _⟦_,_⟧ *)
Proof.
  set (aπ :=(# a projR_monad)%ar).
  cbn.
  eapply (compose (C:=category_LModule _ _) (a := a (pr1 R))).
  - apply (#a projR_monad)%ar.
  - apply pb_LModule_Mor.
    apply (F R'_monad).
Defined.

(**
By naturality of F,

<<<<

       hab
   a_R --> b_R'
    |     ^
    |    /
F_R |   / b_π
    |  /
    V /
    b_R 

>>>>
where π := projR

 *)
Lemma hab_alt : pr1 hab =
                ((F (pr1 R) : nat_trans _ _) : functor_category _ _⟦_, _⟧) ·
                         ((# b projR_monad) : nat_trans _ _).
Proof.
  apply arity_Mor_ax.
Qed.

(** This is the compatibility relation that is needed to construct
R'_rep_τ : b R -> R
*)

Lemma compat_rep_τ_projR 
  : ∏ (X : SET) x y,
    (pr1 hab) X x
    (* =       ( pr1 (# a projR_monad )%ar X ;; (F `` R'_monad) X) y *)
    =
    pr1 hab  X y
    (* (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR_monad )%ar X) x *)
    (* = (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR_monad )%ar X) y *)
    ->
    (rep_τ _ R X · projR X) x = (rep_τ _ R X · projR X) y.
Proof.
  intros X x y comp.
  apply rel_eq_projR.
  intros S m.
  assert (h := eq_mr m X); apply toforallpaths in h.
  etrans; [ apply h |].  
  apply pathsinv0.
  etrans; [ apply h |].
  cbn.
  do 2 apply maponpaths.
  apply (!comp).
Qed.



Definition preservesEpi_arity (c : arity SET) :=
  ∏ M N (f:category_Monad _⟦M,N⟧),
     isEpi (C := functor_category _ _) (pr1 f) -> isEpi (C:= functor_category _ _)
                                                       (pr1 (#c f)%ar).


(** For the explicit subsitution arity example *)
Example EpiArityThetaTheta (choice : AxiomOfChoice.AxiomOfChoice_surj)
        {M N} (f:category_Monad SET ⟦M,N⟧) :
     isEpi (C := functor_category _ _) (pr1 f) -> isEpi (C:= functor_category _ _)
                                                       (horcomp (pr1 f )(pr1 f )).
Proof.
  intro hepi.
  apply is_nat_trans_epi_from_pointwise_epis.
  assert (hf : ∏ x, isEpi (pr1 f x)).
  {
    apply epi_nt_SET_pw.
    exact hepi.
  }
  intro x.
  apply isEpi_comp.
  - apply hf.
  - apply preserves_to_HSET_isEpi.
    + apply choice.
    + apply hf.
Qed.
   

(**
Conditions that we require to prove that [hab] is epimorphic :
either [a] is an epi arity and [F R'] is an epi, either [b] is an epi-arity
and [F R] is an epi
*)
Definition cond_isEpi_hab :=
  (isEpi (C := [_, _]) (pr1 (F R'_monad)) × preservesEpi_arity a) ⨿
                           (isEpi (C := [_, _]) (pr1 (F (pr1 R))) × preservesEpi_arity b).


Context (cond_hab : cond_isEpi_hab).

Lemma isEpi_def_R'_rep_τ : isEpi (C:= [SET,SET]) (pr1 hab).
Proof.
  case cond_hab.
  - intros [epiFR' epia].
    apply (isEpi_comp (functor_category _ _)).
    + apply epia.  apply isEpi_projR.
    + cbn.
      apply epiFR'.
  - intros [epiFR epib].
    rewrite hab_alt.
    apply (isEpi_comp (functor_category _ _)).
    + cbn.
      apply epiFR.
    + apply epib.  apply isEpi_projR.
Qed.


Definition R'_rep_τ_module 
  : LModule_Mor _ (b R'_monad) (tautological_LModule R'_monad) 
  :=
  quotientrep.R'_rep_τ_module ax_choice congr_equivc compat_μ_projR (h:=hab)compat_rep_τ_projR isEpi_def_R'_rep_τ.

Definition R'_rep_τ_def 
  : ∏ (X : SET),
    (# a (projR_monad)%ar) X · (F R'_monad) X · R'_rep_τ_module X  
    = 
    rep_τ _ R X · projR X .
Proof.
  intro X.
  apply (quotientrep.R'_rep_τ_def ax_choice congr_equivc compat_μ_projR (h:=hab)compat_rep_τ_projR isEpi_def_R'_rep_τ).
Qed.

Definition R'_rep : rep_disp SET b.
  use tpair.
  - exact R'_monad.
  - exact R'_rep_τ_module.
Defined.

(* FIN DE LA PARTIE 5 *)

(* projR est un morphisme de representation *)

Lemma projR_rep_laws : rep_ar_mor_law SET R R'_rep F projR_monad.
Proof.
  intro X.
  symmetry.
  apply (R'_rep_τ_def X).
Qed.

Definition projR_rep : R -->[F] R'_rep := (_ ,, projR_rep_laws).


End R'Representation.



(** u morphism of representations *)
Section uRepresentation.

Context {S : REP b} (m : R -->[ F] S).
Context (cond_F : cond_isEpi_hab).

Open Scope arity_scope.
  
(* Local Notation R'_REP := (R'_rep FepiR' aepiR). *)

(* TODO  : foutre ça dans quotientrep *)
Lemma u_rep_laws 
  : rep_ar_mor_law SET (R'_rep cond_F) S (identity (b : CAT_ARITY)) (u_monad m).
Proof.
  intro X.
  apply pathsinv0.
  apply (
               (quotientrep.u_rep_laws ax_choice congr_equivc compat_μ_projR (h:=hab)compat_rep_τ_projR
                                       (isEpi_def_R'_rep_τ cond_F) (S:=pr1 S) (m:=pr1 m) _
                                       (s:=rep_τ _ S) (F:=( (# b ( u_monad m))%ar))
         )).
  intro X'.
  etrans; [apply (rep_ar_mor_ax _ m )|].
  apply cancel_postcomposition.
  etrans.
  (* # a m ;; F_S = #a π ;; F_R' ;; # b u *)
  (* je dois utilier la naturalité de F à droite
     pour avoir #a π ;; #a u ;; F_S et ensuite par définition de m = π ;; u
   *)
  apply cancel_postcomposition.
  etrans.
  apply (cancel_ar_on _ (compose (C:=category_Monad _) projR_monad (u_monad m))).
  use (invmap (Monad_Mor_equiv _ _ _)).
  { apply homset_property. }
  { apply nat_trans_eq.
    apply homset_property.
    apply (u_def m).
  }
  assert (h:=arity_comp a (projR_monad)  (u_monad m)).
  apply LModule_Mor_equiv in h.
  eapply nat_trans_eq_pointwise in h.
  apply h.
  apply homset_property.
  etrans;revgoals.
  etrans;[|apply assoc].
  apply cancel_precomposition.
  apply arity_Mor_ax_pw.
  reflexivity.
Qed.


Definition u_rep : (R'_rep cond_F) -->[identity (b: CAT_ARITY)] S 
  := _ ,, u_rep_laws.


End uRepresentation.
  (* FIN DE LA PARTIE 6 *)

Section uUnique.

Context {S : REP b} 
        (m : R -->[ F] S).
Context (cond_F : cond_isEpi_hab).

Variable u'_rep : R'_rep cond_F -->[identity (b:CAT_ARITY)] S.
Variable (hu' : ∏ x,
                ((projR_rep cond_F : rep_ar_mor_mor _ _ _ _ _ _) x
                 · (u'_rep : rep_ar_mor_mor _ _ _ _ _ _) x)
                = (m : rep_ar_mor_mor _ _ _ _ _ _ ) x
         ).

Lemma u_rep_unique : u'_rep = u_rep m cond_F.
Proof.
  apply rep_ar_mor_mor_equiv.
  apply (univ_surj_nt_unique _ _ _ _ (##u'_rep)).
  - apply nat_trans_eq.
    + apply has_homsets_HSET.
    + intro X.
      apply hu'.
Qed.      

End uUnique.

End fix_rep_of_a.


Let Rep_a : category := fiber_category (rep_disp SET) a.
Let Rep_b : category := fiber_category (rep_disp SET) b.

Let FF : Rep_b ⟶ Rep_a := fiber_functor_from_cleaving _ (rep_cleaving SET) F.

Require Import UniMath.CategoryTheory.limits.initial.

Lemma build_module_law (R : Rep_a) (cond_R :   cond_isEpi_hab R)
  (S : Rep_b) (m : Rep_b ⟦ R'_rep R cond_R, S ⟧)
  : (rep_ar_mor_law _ R (pb_rep SET F S) (arity_Mor_id (pr1 a))
      ((pr1 (projR_rep R cond_R) : category_Monad _ ⟦_,_⟧) · (pr1 m))

    ).
Proof.
  intro x.
  etrans.
  {
    etrans; [apply assoc |].
    apply cancel_postcomposition.
    apply (rep_ar_mor_ax _ (projR_rep R cond_R)).
  }
  rewrite arity_comp.
  repeat rewrite <- assoc.
  etrans; [|apply assoc].
  apply cancel_precomposition.
  etrans; revgoals.
  {
    repeat rewrite assoc.
    eapply pathsinv0.
    etrans; [apply assoc|].
    apply cancel_postcomposition.
    apply arity_Mor_ax_pw.
  }
  etrans.
  {
    apply cancel_precomposition.
    apply (rep_ar_mor_ax _ m).
  }
  reflexivity.
Qed.

Definition build_module (R : Rep_a) (cond_R :   cond_isEpi_hab R)
  (S : Rep_b) (m : Rep_b ⟦ R'_rep R cond_R, S ⟧)
  : (rep_ar_mor_mor _ a a R (pb_rep SET F S) (arity_Mor_id (pr1 a))

    )
      := (_ ,, build_module_law R cond_R S m).
  
Theorem push_initiality (R : Rep_a) (epi_F : isEpi (C := [_, _]) (pr1 (F (pr1 R))))
        (epib : preservesEpi_arity b) :
    isInitial _ R -> Initial Rep_b.
Proof.
  intro iniR.
  set (cond_R := inr (epi_F ,, epib) : cond_isEpi_hab R).
  use tpair.
  - apply (R'_rep R cond_R).

  - intro S.
    unshelve eapply iscontrpair.
    +  use u_rep.
       use (iscontrpr1 (iniR (FF S))).
    + intro m.
      apply u_rep_unique.
      assert (h := iscontr_uniqueness (iniR (FF S)) (build_module R cond_R S m)).
      rewrite <- h.
      intros.
      apply idpath.
Qed.

Theorem push_initiality_weaker (R : Rep_a) (epi_F : ∏ (R : Monad _),
                                                     isEpi (C := [_, _]) (pr1 (F (R))))
        (epia : preservesEpi_arity a) :
    isInitial _ R -> Initial Rep_b.
Proof.
  intro iniR.
  set (cond_R := inl (epi_F _ ,, epia) : cond_isEpi_hab R).
  use tpair.
  - apply (R'_rep R cond_R).

  - intro S.
    unshelve eapply iscontrpair.
    +  use u_rep.
       use (iscontrpr1 (iniR (FF S))).
    + intro m.
      apply u_rep_unique.
      assert (h := iscontr_uniqueness (iniR (FF S)) (build_module R cond_R S m)).
      rewrite <- h.
      intros;
      apply idpath.
Qed.

(* TODO : remplacer Fepi par isEpi F (comme dans le papier) et déduire la version pointwise *)
Context (aepi : preservesEpi_arity a).

Let R'_monad R  := R'_monad ax_choice (congr_equivc R) (compat_μ_projR R).

Lemma helper (Fepi : forall R, isEpi (C := [_, _]) (pr1 (F (R'_monad R))))  (R : Rep_a)
      (cond_F := inl (dirprodpair (Fepi R) aepi ) : cond_isEpi_hab R)
  (S : rep_ar SET b)
  : ∏ (u' : Rep_b ⟦ R'_rep R cond_F, S ⟧) x,
                 (projR (congr_equivc R) x · (u' : rep_ar_mor_mor _ _ _ _ _ _) x) =
                 (pr1 (pr1 (compose  (C:=Rep_a) (b:=FF (R'_rep R cond_F))
                                     (projR_rep R cond_F : rep_ar_mor_mor _ _ _ _ _ _)
                                     (# FF (u'))))) x.
Proof.
  intros u' x.
  apply pathsinv0.
  etrans ; [
      apply (@transport_arity_mor SET a a 
                                  (identity (a:CAT_ARITY) · identity (a:CAT_ARITY))
                                  (identity (a:CAT_ARITY)) (id_right (identity (a:CAT_ARITY))) 
                                  R 
                                  (FF S)
                                  _ 
            ) |].
  apply (cancel_precomposition HSET _ _ _ _ _ ((projR (congr_equivc R) x))).
  cbn.
  set (e := _ @ _).
  induction e; apply idpath.
Qed.


Definition is_right_adjoint_functor_of_reps (Fepi : forall R, isEpi (C := [_, _]) (pr1 (F (R'_monad R))) ) : 
                                              is_right_adjoint FF.
Proof.
  set (cond_F := fun R => inl ((Fepi R),, aepi) : cond_isEpi_hab R).
  use right_adjoint_left_from_partial.
  - intro R. 
    apply (R'_rep R (cond_F R)).
  - intro R. apply projR_rep.
  - intro R.
    unfold is_universal_arrow_to.
    intros S m. cbn in S, m.
    use unique_exists. 
    + apply (u_rep _ m). 
    + (* Ici ca devrait être apply quotientmonad.u_def *)
      apply pathsinv0. 
      apply rep_ar_mor_mor_equiv.
      intro x.
      etrans. { apply u_def. }
      apply (helper Fepi _ _ (u_rep R m (cond_F R))).
    + intro y; apply homset_property.
    + intros u' hu'.
      hnf in hu'.
      apply u_rep_unique.
      rewrite <- hu'.
      intro x.
      apply helper.
Qed.
  
Corollary is_right_adjoint_functor_of_reps_from_pw_epi 
  (Fepi : forall R : Monad SET, isEpi (C:=functor_precategory HSET HSET has_homsets_HSET)
                             (pr1 (F R))) : is_right_adjoint FF.
Proof.
  apply is_right_adjoint_functor_of_reps.
  intro R; apply Fepi.
Qed.
End leftadjoint.

