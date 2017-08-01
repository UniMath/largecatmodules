(*

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

Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.

Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.SetValuedFunctors.

Require Import Modules.Prelims.aritiesalt.
Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientrep.

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

Variables (a b:@arity SET) (R:REP a)
          (F:arity_Mor a b).

Local Notation "## F" := (pr1 (pr1 (F)))(at level 3).


(**
On any set X we define the following equivalence relation on R X : 
   x ~ y
iff for any representation morphism f : R -> F*(S) (where S is a b-representation)
  f x = f y.
*)


Definition equivc   {X:ob SET} (x y:pr1 ( ## R X)) :=
                                  (∏ (S:REP b) ( f : R -->[F] S),
                                   pr1 (pr1 f) X x = ## f X y).

Lemma isaprop_equivc_xy (c:ob SET) x y : isaprop (equivc (X:=c) x y).
Proof.
  intros.
  apply impred_isaprop; intro S.
  apply impred_isaprop; intros f.
  apply setproperty.
Qed.

Definition equivc_xy_prop (X : SET) x y : hProp :=
  equivc (X:=X) x y ,, isaprop_equivc_xy X x y.

Definition hrel_equivc (X : SET) : hrel _ := fun x y => equivc_xy_prop X x y.

Lemma iseqrel_equivc (X : SET) : iseqrel (hrel_equivc X).
Proof.
  unfold hrel_equivc, equivc_xy_prop, equivc; simpl;
  repeat split.
  - intros x y z. cbn.
    intros h1 h2 S f.
    now rewrite h1,h2.
  - intros x y; cbn.
    intros h S f.
    now symmetry.
Qed.


Definition eqrel_equivc (X : SET) : eqrel _ := _ ,, iseqrel_equivc X.

(** For any f : X -> Y, #R f is compatible with previous equivalence relation *)
Lemma congr_equivc (X Y : SET) (f:SET ⟦X , Y⟧):
                    iscomprelrelfun (eqrel_equivc X) (eqrel_equivc Y) (# (## R) f).
Proof.
  intros z z' eqz S g.
  assert (hg := nat_trans_ax (pr1 (pr1 g)) X Y f).
  cbn in eqz.
  apply toforallpaths in hg.
  etrans; [apply hg|].
  apply pathsinv0.
  etrans;[apply hg|].
  unfold equivc in eqz.
  cbn.
  now rewrite eqz.
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

Section CandidatU.

Context {S:REP b} (m:R -->[ F] S).

Lemma compat_m :  ∏ (X : SET) (x y : ((pr1 R) X:hSet)),
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

Lemma u_def : ∏ x, ## m x = projR x ;; u x.
Proof.
  apply (quotientmonad.u_def).
Qed.

End CandidatU.



Lemma compat_μ_projR : compat_μ_projR_def congr_equivc.
Proof.
  intros X x y hxy.
  apply rel_eq_projR.
  intros S f.
  rewrite comp_cat_comp.
  symmetry.
  rewrite comp_cat_comp.
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
  
Let R'_monad  := R'_monad congr_equivc compat_μ_projR.
Let projR_monad  := projR_monad congr_equivc compat_μ_projR.


Definition u_monad {S} (m : R -->[ F] S) 
  : Monad_Mor (quotientmonad.R'_monad congr_equivc compat_μ_projR) (pr1 S)
  := quotientmonad.u_monad compat_μ_projR (S:=pr1 S) (pr1 m) (compat_m m).


(** * FIN DE LA TROISIEME ETAPE *)



Section R'Representation.

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
   
Context {S:REP b} (m:R -->[ F] S).

Lemma cancel_ar_on {a'}
      {R'' (* : REP a*)}                  (*  *)
      (* {F' : CAT_ARITY ⟦ a', b' ⟧ *)
      {S' (* : REP b *)}
      (m2 m' : Monad_Mor R'' S')
      (X : SET) : m2 = m' ->  (# a')%ar m2 X = (# a')%ar m' X .
Proof.
  intro e; now induction e.
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

Lemma eq_mr X : rep_τ _ R X ;; ## m X =
                pr1 (# a projR_monad)%ar X ;;
                    (F (R'_monad ))%ar X ;;
                pr1 (# b (u_monad m))%ar X ;;
                    rep_τ _ S X.
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
  assert (h:= arity_Mor_ax F (u_monad m)).
  eapply nat_trans_eq_pointwise in h.
  apply pathsinv0.
    apply h.
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
Definition hab : mor_disp
                   (D:=bmod_disp_ob_mor _ _ )(a (pr1 R)) (b  R'_monad)
                   ((projR_monad:category_Monad _⟦_,_⟧) ).
Proof.
  set (aπ :=(# a projR_monad)%ar).
  cbn.
  eapply (compose (C:=category_LModule _ _) (a := a (pr1 R))).
  - apply (#a projR_monad)%ar.
  - apply pb_LModule_Mor.
    apply (F R'_monad).
Defined.

(** This is the compatibility relation that is needed to construct
R'_rep_τ : b R -> R
*)

Lemma compat_rep_τ_projR :
      ∏ (X : SET) x y,
       (pr1 hab) X x
      (* =       ( pr1 (# a projR_monad )%ar X ;; (F `` R'_monad) X) y *)
       =
       pr1 hab  X y
      (* (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR_monad )%ar X) x *)
      (* = (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR_monad )%ar X) y *)
      ->
            (rep_τ _ R X ;; projR X) x = (rep_τ _ R X;; projR X) y.
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


(* F preserve the epis *)
Definition isEpi_FR' := isEpi (C:=functor_precategory HSET HSET has_homsets_HSET)
                             (pr1 (F R'_monad)).
(* a preserve les epis *)
Definition a_preserves_epi := ∏ M N (f:category_Monad _⟦M,N⟧),
                              isEpi f -> isEpi
                                          (C:= functor_category _ _) (pr1 (#a f)%ar).

Context (Fepi:isEpi_FR') (aepi:a_preserves_epi).

Lemma isEpi_def_R'_rep_τ : isEpi (C:= [SET,SET]) (pr1 hab).
                          (* (compose (C:=functor_category _ _) *)
                          (*          (pr1 ((# a)%ar projR_monad)) *)
                          (*          (pr1 (F `` R'_monad)%ar)). *)
Proof.
  apply (isEpi_comp (functor_category _ _)).
  - apply aepi; apply isEpi_projR_monad.
  - cbn.
    apply Fepi.
Qed.


(*
Definition R'_rep_τ  : nat_trans (pr1 ( b` R'_monad)) R'.
Proof.
eapply (quotientrep.R'_rep_τ congr_equivc compat_μ_projR (h:=hab)compat_rep_τ_projR isEpi_def_R'_rep_τ).
Defined.

*)



Definition R'_rep_τ_module 
  : LModule_Mor _ (b R'_monad) (tautological_LModule R'_monad) 
  :=
  quotientrep.R'_rep_τ_module congr_equivc compat_μ_projR (h:=hab)compat_rep_τ_projR isEpi_def_R'_rep_τ.

Definition R'_rep_τ_def :
  ∏ (X:SET),
  (# a (projR_monad)%ar) X ;; (F R'_monad) X ;; R'_rep_τ_module X  
  = 
  rep_τ _ R X ;; projR X .
Proof.
  intro X.
  apply (quotientrep.R'_rep_τ_def congr_equivc compat_μ_projR (h:=hab)compat_rep_τ_projR isEpi_def_R'_rep_τ).
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



  (* u morphisme de représentation *)
Section uRepresentation.

Context {S : REP b} (m : R -->[ F] S).
Context (Fepi : isEpi_FR') (aepi : a_preserves_epi).

Open Scope arity_scope.
  
  
(* Local Notation R'_REP := (R'_rep FepiR' aepiR). *)

(* TODO  : foutre ça dans quotientrep *)
Lemma u_rep_laws : rep_ar_mor_law SET (R'_rep Fepi aepi) S (identity (b : CAT_ARITY)) (u_monad m).
Proof.
  intro X.
  apply pathsinv0.
  apply (
               (quotientrep.u_rep_laws congr_equivc compat_μ_projR (h:=hab)compat_rep_τ_projR
                                       (isEpi_def_R'_rep_τ Fepi aepi) (S:=pr1 S) (m:=pr1 m) _
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
  assert (hF := arity_Mor_ax F (u_monad m)).
  eapply nat_trans_eq_pointwise in hF.
  apply hF.
  reflexivity.
Qed.


Definition u_rep : (R'_rep Fepi aepi) -->[identity (b: CAT_ARITY)] S 
  := _ ,, u_rep_laws.


End uRepresentation.
  (* FIN DE LA PARTIE 6 *)

Section uUnique.

Context {S : REP b} (hm : iscontr (R -->[ F] S)).
Context (Fepi : isEpi_FR') (aepi : a_preserves_epi).

Variable u'_rep : (R'_rep Fepi aepi) -->[identity (b:CAT_ARITY)] S.

(* Let foo : R -->[ (F : CAT_ARITY ⟦_,_⟧)(* ;; identity (b:CAT_ARITY)] *)] S *)
Let foo : R -->[ (F : CAT_ARITY ⟦_,_⟧);; identity (b:CAT_ARITY)] S
  := (projR_rep Fepi aepi ;; u'_rep)%mor_disp.

Let foo' : R -->[ (F : CAT_ARITY⟦_,_⟧);; identity (b : CAT_ARITY)] S
(* Let foo' : R -->[ (F : CAT_ARITY⟦_,_⟧)(* ;; identity (b : CAT_ARITY) *)] S *)
  := (iscontrpr1 hm ;; id_disp S)%mor_disp.

Lemma proj_u'_equal_mor : foo = foo'.
Proof.
  unfold foo, foo'.
  rewrite id_right_disp .
  cbn.
  (* induction (id_right (F:CAT_ARITY⟦_,_⟧)). *)
  apply transportf_transpose .
  apply (iscontr_uniqueness hm).
Defined.
 
Lemma u_rep_unique : u'_rep = (u_rep (pr1 hm) Fepi aepi).
Proof.
  apply rep_ar_mor_mor_equiv.
  apply (univ_surj_nt_unique _ _ _ _ (##u'_rep)).
  assert (eqm'2 : pr1 foo = pr1 foo').
  { exact (maponpaths pr1 proj_u'_equal_mor). }
  apply Monad_Mor_equiv in eqm'2.
  - apply nat_trans_eq.
    + apply has_homsets_HSET.
    + intro X.
      eapply nat_trans_eq_pointwise in eqm'2.
      apply eqm'2.
  - apply has_homsets_HSET.
Qed.      

End uUnique.

End leftadjoint.

