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

- Proof that pointwise epimorphisms of signature preserve representability
 if the domain is an epi-signature

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
Require Import Modules.Prelims.EpiComplements.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules. 

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.SetValuedFunctors.

Require Import Modules.Signatures.Signature.
Require Import Modules.Prelims.lib.

Require Import Modules.Prelims.quotientmonad.
Require Import Modules.Prelims.quotientmonadslice.
Require Import Modules.Signatures.quotientrep.
Require Import Modules.Signatures.EpiArePointwise.
Require Import Modules.Signatures.PreservesEpi.

Set Automatic Introduction.


Section all_purpose.
  
(** First a general-purpose lemma: 
    equal monad morphisms are mapped to 
    equal module morphisms by any
    signature
*)
Lemma cancel_ar_on {sig : signature SET}
      {T : Monad SET} 
      {S' : Monad SET}
      (m m' : Monad_Mor T S')
      (X : SET) 
  : m = m' ->  (# sig)%ar m X = (# sig)%ar m' X .
Proof.
  intro e; induction e.
  apply idpath.
Qed.


(** For the explicit subsitution signature example *)
Example EpiSignatureThetaTheta
        (choice : AxiomOfChoice.AxiomOfChoice_surj)
        {M N : category_Monad SET}
        (f : category_Monad SET ⟦M,N⟧) :
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
   

End all_purpose.


(**
A morphism of signature F : a -> b induces a functor between model Rep(b) -> Rep(a)

In this section we construct the left adjoint of this functor (which is defined whenever
F is an epimorphism)
*)


Section leftadjoint.

Local Notation "'SET'" := hset_category.
Local Notation CAT_SIGNATURE := (@signature_category SET).
Local Notation REP := (rep_disp SET).

Variable (ax_choice : AxiomOfChoice.AxiomOfChoice_surj).

Context {a b : signature SET}.

Context  (F : signature_Mor a b).

Section fix_rep_of_a.

Context (R : REP a).
Context (R_epi : preserves_Epi (R : model  _)).

(** Either [a R] preserves epis, or for any monad S (actually only the quotient monad case
  is used), [b S] preserves epis *)
Context (ab_epi : preserves_Epi (a ( R : model _)) ⨿ (∏ S, preserves_Epi (b S))).
Local Notation "## F" := (pr1 (pr1 F))(at level 3).

(**
On any set X we define the following equivalence relation on R X : 
   x ~ y
iff for any model morphism f : R -> F*(S) (where S is a b-model)
  f x = f y.


We will show that this relation satisfies the conditions necessary to 
define the quotient of a monad, and of a module over a monad.

*)


(** Define two elements in R to be related if they are mapped
    to the same element by any morphism f of models 
*)


(* These definitions are used for exploiting quotientmonadslice *)
Let J := ∑ (S : REP b), (R -->[ F] S).
Let dd (j : J) : Monad _ := (pr1 j : model _ ).
Let ff (j : J) : Monad_Mor  (R : model _) (dd j) := (pr2 j : model_mor_mor _ _ _ _ _ ).

Arguments R' : simpl never.
Arguments projR : simpl never.



Section Instantiating_Quotient_Constructions.

(** We define short identifiers for the quotient constructions for 
    functors, monads, and modules (defined in previous files),
    for the equivalence relation induced by a morphism of models [m]
    over a morphism of arities [F].
*)

(** R' est un pseudo objet initial au sens suivant :
     Quel que soit        g : R ---> S morphisme dans la catégorie des représentations de a
     il existe un unique  u : R'---> S tel que g = u o projR
C'est un pseudo objet car il reste à montrer que R' est bien dans la catégorie des représentations
de a et que u est un morphisme de modules.
*)

(** Short notations for the quotient monad and the projection as a monad morphism *)
Definition R' : Monad SET := R'_monad R_epi  dd ff .

Lemma ab_epi2 : preserves_Epi (a (pr1 R)) ⨿ preserves_Epi (b R').
Proof.
  use (coprodf2 _ ab_epi).
  exact (fun f  => f _).
Defined.

Definition projR
  : Monad_Mor (pr1 R) R'
  := projR_monad R_epi dd ff.


(** Short name for the monad morphism out of the quotient *)
Definition u {S : REP b} (m : R -->[ F] S)
  : Monad_Mor R' (pr1 S)
  := u_monad R_epi dd ff (S ,, m) .

(** The induced natural transformation makes a triangle commute *)
Lemma u_def {S : REP b} (m : R -->[ F] S) : ∏ x, ## m x = projR x · u m x.
Proof.
  apply (u_def dd ff (S ,, m)).
Qed.






End Instantiating_Quotient_Constructions.




(** * FIN DE LA TROISIEME ETAPE *)



(** Some helper lemmas *)

(** Any morphism of representations factors, 
    as a monad morphism, via the monad projection *)
Lemma Rep_mor_is_composition
      {S : REP b} (m : R -->[ F] S)
  : pr1 m = compose (C:=category_Monad _) projR (u m) .
Proof.
  use (invmap (Monad_Mor_equiv _ _ _)).
  { apply (homset_property SET). }
  apply nat_trans_eq.
  - apply (homset_property SET).
  - intro X'.
    apply (u_def m).
Qed.

(** 
<<
                 model_τ R
            a R  ----->  R
             |           |
     a projR |           | m
             v           |
            a R'         |
             |           |
        F R' |           |
             v           v
            b R'->b(S)-> S
     b(\overline{m}) · model_τ S
>>
*)

Lemma eq_mr
      {S : REP b} (m : R -->[ F] S) (X : SET)
  : model_τ R X · ## m X 
    =
    pr1 (# a projR)%ar X · (F (R' ))%ar X 
        ·
        pr1 (# b (u m))%ar X · model_τ S X.
Proof.
  etrans. { apply model_mor_ax. }
  cpost _.
  etrans.
  { cpost _.
    etrans.
    { apply (cancel_ar_on _ _ _ (Rep_mor_is_composition m)). }
    eapply nat_trans_eq_pointwise.
    apply maponpaths.
    apply signature_comp.
  }
  etrans;[|apply (assoc (C:=SET))].
  apply pathsinv0.
  etrans;[|apply (assoc (C:=SET))].
  cpre SET.
  apply pathsinv0.
  apply (signature_Mor_ax_pw F (u m)).
Qed.




Section R'Model.

(** Goal: define a model of [b]
    with underlying monad the quotient monad defined in the previous step
*)

(** R'_model_τ is defined by the following diagram :
<<
                  model_τ R
            a R  ----->  R
             |           |
         F R |           | projR
             v           |
            b R          |
             |           |
     b projR |           |
             v           v
           b R' -------> R'
                R'_model_τ

>>
or rather the following diagram.
<<
                 model_τ R
            a R  ----->  R
             |           |
     a projR |           | projR
             v           |
            a R'         |
             |           |
        F R' |           |
             v           v
            b R' ------> R'
                R'_model_τ
>>

We need to show that for all x,y such that
F R' o a projR (x) = F R' o a projR (y), we have
  projR o model_τ R (x) = projR o model_τ R (y)

This is lemma [compat_model_τ_projR]
*)


Open Scope signature_scope.

(**
Definition of [hab]:
The diagonal of the following square, which commutes by naturality of F:

<<
               F(R)
       a(R) ---------> b(R)
        |               |
    a(π)|               |b(π)
        |               |
        v               v
       a(R') --------> b(R')
               F(R')
>>

where π := projR

The R-module morphism 
    #a R · Pullback (π)(F R') : a(R) ---> π^*(b R')
*)
Definition hab :
  LModule_Mor (pr1 R) (a (pr1 R)) (pb_LModule projR (b R'))
  := compose (C:= category_LModule _ _ )
             (# a projR)
             (pb_LModule_Mor projR (F R')).

Lemma hab_alt
  : pr1 hab =
    ((F (pr1 R) : nat_trans _ _) : functor_category _ _⟦_, _⟧)
      ·
      ((# b projR) : nat_trans _ _).
Proof.
  apply signature_Mor_ax.
Qed.

(** This is the compatibility relation that is needed to construct

    R'_model_τ : b R' -> R'

<<
               τ
    a(R) -----------------> R
     |                      |
hab  |                      | π 
     |                      |
     v                      v
   π^*(b R')                R'

>>
*)
Lemma compat_model_τ_projR 
  : ∏ (X : SET) x y,
    (pr1 hab) X x
    (* =       ( pr1 (# a projR )%ar X ;; (F `` R') X) y *)
    =
    pr1 hab X y
    (* (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR )%ar X) x *)
    (* = (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR )%ar X) y *)
    ->
    (model_τ R X · projR X) x = (model_τ R X · projR X) y.
Proof.
  intros X x y comp.
  apply rel_eq_projR.
  intros [S m].
  assert (h := eq_mr m X); apply toforallpaths in h.
  etrans; [ apply h |].  
  apply pathsinv0.
  etrans; [ apply h |].
  cbn.
  do 2 apply maponpaths.
  apply (!comp).
Qed.



(**
Conditions that we require to prove that [hab] is epimorphic :
either [a] is an epi signature and [F R'] is an epi, either [b] is an epi-signature
and [F R] is an epi
*)
Definition cond_isEpi_hab :=
  (isEpi (C := [_, _]) (pr1 (F R')) × sig_preservesNatEpiMonad a) ⨿
                           (isEpi (C := [_, _]) (pr1 (F (pr1 R))) × sig_preservesNatEpiMonad b).


Context (cond_hab : cond_isEpi_hab).

Lemma isEpi_def_R'_model_τ : isEpi (C:= [SET,SET]) (pr1 hab).
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


Definition R'_model_τ_module 
  : LModule_Mor _ (b R') (tautological_LModule R') .
Proof.
  use quotientrep.R'_model_τ_module; revgoals.
  - apply isEpi_def_R'_model_τ.
  - apply compat_model_τ_projR.
  - apply ab_epi2.
Defined.

(** 
<<
           a(π)
    a(R)-------> a(R')
     |            |
     |            | F(R')
     |            v
   τ |           b(R')
     |            |
     |            | τ 
     v            v
     R ---------> R'
          π 
>>
*)

Definition R'_model_τ_def 
  : ∏ (X : SET),
    (# a (projR)%ar) X · (F R') X · R'_model_τ_module X  
    = 
    model_τ R X · projR X .
Proof.
  intro X.
  use quotientrep.R'_model_τ_def.
Qed.

Definition rep_of_b_in_R' : rep_disp _ b.
  use tpair.
  - exact R'.
  - exact R'_model_τ_module.
Defined.

(* FIN DE LA PARTIE 5 *)

(* projR est un morphisme de model *)

Lemma projR_rep_laws : model_mor_law R rep_of_b_in_R' F projR.
Proof.
  intro X.
  symmetry.
  apply (R'_model_τ_def X).
Qed.

Definition projR_rep : R -->[F] rep_of_b_in_R' := (_ ,, projR_rep_laws).


End R'Model.



(** u morphism of models *)
Section uModel.

Context {S : REP b} (m : R -->[ F] S).
Context (cond_F : cond_isEpi_hab).

Open Scope signature_scope.
  

(* TODO  : foutre ça dans quotientrep *)
Lemma u_rep_laws
  : model_mor_law (rep_of_b_in_R' cond_F) S (identity (b : CAT_SIGNATURE)) (u m).
Proof.
  intro X.
  apply pathsinv0.
  apply quotientrep.u_rep_laws.
  intro X'.
  etrans; [apply (model_mor_ax m )|].
  apply cancel_postcomposition.
  etrans.
  (* # a m ;; F_S = #a π ;; F_R' ;; # b u *)
  (* je dois utilier la naturalité de F à droite
     pour avoir #a π ;; #a u ;; F_S et ensuite par définition de m = π ;; u
   *)
  apply cancel_postcomposition.
  etrans.
  apply (cancel_ar_on _ (compose (C:=category_Monad _) projR (u m))).
  use (invmap (Monad_Mor_equiv _ _ _)).
  { apply homset_property. }
  { apply nat_trans_eq.
    apply homset_property.
    apply (u_def m).
  }
  assert (h:=signature_comp a (projR)  (u m)).
  apply LModule_Mor_equiv in h.
  eapply nat_trans_eq_pointwise in h.
  apply h.
  apply homset_property.
  etrans;revgoals.
  etrans;[|apply assoc].
  apply cancel_precomposition.
  apply signature_Mor_ax_pw.
  reflexivity.
Qed.


Definition u_rep : (rep_of_b_in_R' cond_F) -->[identity (b: CAT_SIGNATURE)] S 
  := _ ,, u_rep_laws.


Lemma u_rep_unique
      (u'_rep : rep_of_b_in_R' cond_F -->[identity (b:CAT_SIGNATURE)] S)
      (hu' : ∏ x,
             ((projR_rep cond_F : model_mor_mor _ _ _ _ _) x
              · (u'_rep : model_mor_mor _ _ _ _ _) x)
             =
             (m : model_mor_mor _ _ _ _ _) x)
  : u'_rep = u_rep.
Proof.
  apply model_mor_mor_equiv.
  apply (univ_surj_nt_unique _ _ _ _ (##u'_rep)).
  - apply nat_trans_eq.
    + apply has_homsets_HSET.
    + intro X.
      apply hu'.
Qed.      


End uModel.
  (* FIN DE LA PARTIE 6 *)

End fix_rep_of_a.


Let Rep_a : category := fiber_category (rep_disp SET) a.
Let Rep_b : category := fiber_category (rep_disp SET) b.

Let FF : Rep_b ⟶ Rep_a := fiber_functor_from_cleaving _ (rep_cleaving SET) F.


Lemma build_module_law
      (R : Rep_a)
      (R_epi : preserves_Epi ( R : model _))
      (epiab :  preserves_Epi (a (R : model _)) ⨿ (∏ S : Monad SET, preserves_Epi (b S)))

      (cond_R : cond_isEpi_hab R R_epi)
      (S : Rep_b)
      (m : Rep_b ⟦ rep_of_b_in_R' R R_epi epiab cond_R, S ⟧)
  : model_mor_law  R
                   (pb_rep F S)
                   (signature_Mor_id (pr1 a))
                   ((pr1 (projR_rep R R_epi epiab cond_R) : category_Monad _ ⟦_,_⟧) · pr1 m).
Proof.
  intro x.
  etrans.
  {
    etrans; [apply assoc |].
    apply cancel_postcomposition.
    apply (model_mor_ax (projR_rep R R_epi epiab cond_R)).
  }
  rewrite signature_comp.
  repeat rewrite <- assoc.
  etrans; [|apply assoc].
  apply cancel_precomposition.
  etrans; revgoals.
  {
    repeat rewrite assoc.
    eapply pathsinv0.
    etrans; [apply assoc|].
    apply cancel_postcomposition.
    apply signature_Mor_ax_pw.
  }
  etrans.
  {
    apply cancel_precomposition.
    apply (model_mor_ax m).
  }
  reflexivity.
Qed.

Definition build_module
           (R : Rep_a)
           (R_epi : preserves_Epi ( R : model _))
           (epiab :  preserves_Epi (a (R : model _)) ⨿ (∏ S : Monad SET, preserves_Epi (b S)))
           (cond_R : cond_isEpi_hab R R_epi)
           (S : Rep_b)
           (m : Rep_b ⟦ rep_of_b_in_R' R R_epi epiab cond_R, S ⟧)
  : model_mor_mor a a R (pb_rep F S) (signature_Mor_id (pr1 a))
  := _ ,, build_module_law R R_epi epiab cond_R S m.
  
Theorem push_initiality
        (R : Rep_a)
        (R_epi : preserves_Epi ( R : model _))
        (epiab :  preserves_Epi (a (R : model _)) ⨿ (∏ S : Monad SET, preserves_Epi (b S)))
        (epiSig_F : isEpi (C:= signature_category ) F)
        (epib : sig_preservesNatEpiMonad b)
  : isInitial _ R -> Initial Rep_b.
Proof.
  assert (epi_F : isEpi (C := [_, _]) (pr1 (F (pr1 R)))).
  {
    apply epiSig_is_pwEpi.
    - exact (ColimsHSET_of_shape pushouts.pushout_graph).
    - exact epiSig_F.
  }
  intro iniR.
  set (cond_R := inr (epi_F ,, epib) : cond_isEpi_hab R R_epi).
  use tpair.
  - apply (rep_of_b_in_R' R R_epi epiab cond_R).
  - intro S.
    use iscontrpair.
    +  use u_rep.
       use (iscontrpr1 (iniR (FF S))).
    + intro m.
      apply u_rep_unique.
      assert (h := iscontr_uniqueness (iniR (FF S)) (build_module R R_epi epiab cond_R S m)).
      rewrite <- h.
      intros.
      apply idpath.
Qed.

Theorem push_initiality_weaker
        (R : Rep_a)
        (R_epi : preserves_Epi ( R : model _))
        (epiab :  preserves_Epi (a (R : model _)) ⨿ (∏ S : Monad SET, preserves_Epi (b S)))
        (epi_F : ∏ (R : Monad _), isEpi (C := [_, _]) (pr1 (F (R))))
        (epia : sig_preservesNatEpiMonad a)
  : isInitial _ R -> Initial Rep_b.
Proof.
  intro iniR.
  set (cond_R := inl (epi_F _ ,, epia) : cond_isEpi_hab R R_epi).
  use tpair.
  - apply (rep_of_b_in_R' R R_epi epiab cond_R).
  - intro S.
    use iscontrpair.
    +  use u_rep.
       use (iscontrpr1 (iniR (FF S))).
    + intro m.
      apply u_rep_unique.
      assert (h := iscontr_uniqueness (iniR (FF S)) (build_module R R_epi epiab cond_R S m)).
      rewrite <- h.
      intros;
      apply idpath.
Qed.

Theorem push_initiality_weaker_choice
        (R : Rep_a)
        (choice : AxiomOfChoice.AxiomOfChoice_surj)
        (epi_F : ∏ (R : Monad _), isEpi (C := [_, _]) (pr1 (F (R))))
        (epia : sig_preservesNatEpiMonad a)
  : isInitial _ R -> Initial Rep_b.
Proof.
  apply push_initiality_weaker; (try apply preserves_to_HSET_isEpi); try assumption.
  apply ii1; apply preserves_to_HSET_isEpi; assumption.
Qed.

(* TODO : remplacer Fepi par isEpi F (comme dans le papier) et déduire la version pointwise *)
Context (aepi : sig_preservesNatEpiMonad a).

(* Let R' (R : REP a) : Monad SET := R' ax_choice (congr_equivc R) (compat_μ_projR R). *)

Lemma helper
      (Fepi : ∏ R R_epi, isEpi (C := [_, _]) (pr1 (F (R' R R_epi))))
      (R : Rep_a)
        (R_epi : preserves_Epi ( R : model _))
        (epiab :  preserves_Epi (a (R : model _)) ⨿ (∏ S : Monad SET, preserves_Epi (b S)))
      (cond_F := inl (dirprodpair (Fepi R R_epi) aepi ) : cond_isEpi_hab R R_epi)
      (S : model b)
  : ∏ (u' : Rep_b ⟦ rep_of_b_in_R' R R_epi epiab cond_F, S ⟧) x,
    projR R R_epi x · (u' : model_mor_mor _ _ _ _ _) x =
    pr1 (pr1 (compose (C:=Rep_a) (b:=FF (rep_of_b_in_R' R R_epi epiab cond_F))
                      (projR_rep R R_epi epiab cond_F : model_mor_mor _ _ _ _ _)
                      (# FF u'))) x.
Proof.
  intros u' x.
  apply pathsinv0.
  etrans ; [
      apply (@transport_signature_mor SET a a 
                                  (identity (a:CAT_SIGNATURE) · identity (a:CAT_SIGNATURE))
                                  (identity (a:CAT_SIGNATURE)) (id_right (identity (a:CAT_SIGNATURE))) 
                                  R 
                                  (FF S)
                                  _ 
            ) |].
  apply (cancel_precomposition HSET _ _ _ _ _ ((projR R _ x))).
  cbn.
  set (e := _ @ _).
  induction e; apply idpath.
Qed.


Definition is_right_adjoint_functor_of_reps
           (* this is the case if the axiom of choice is assumed *)
           (epiall : ∏ (R : functor SET SET), preserves_Epi R)
           (Fepi : ∏ R R_epi, isEpi (C := [_, _]) (pr1 (F (R' R R_epi))) )
  : is_right_adjoint FF.
Proof.
  set (cond_F := fun R R_epi => inl ((Fepi R R_epi),, aepi) : cond_isEpi_hab R R_epi).
  use right_adjoint_left_from_partial.
  - intro R. 
    use (rep_of_b_in_R' R _ _ (cond_F R _ )).
    + apply epiall.
    + apply ii1. 
      apply epiall.
  - intro R. apply projR_rep.
  - intro R.
    unfold is_universal_arrow_to.
    intros S m. cbn in S, m.
    use unique_exists. 
    + unshelve use (u_rep _ _ _ m). 
    + (* Ici ca devrait être apply quotientmonad.u_def *)
      apply pathsinv0. 
      apply model_mor_mor_equiv.
      intro x.
      etrans. { apply u_def. }
      use (helper Fepi _ _ _ _ (u_rep R _ _ m (cond_F R _ ))).
    + intro y; apply homset_property.
    + intros u' hu'.
      hnf in hu'.
      apply u_rep_unique.
      rewrite <- hu'.
      intro x.
      apply helper.
Qed.
  
Corollary is_right_adjoint_functor_of_reps_from_pw_epi 
           (epiall : ∏ (R : functor SET SET), preserves_Epi R)
          (Fepi : forall R : Monad SET, isEpi (C:=functor_precategory HSET HSET has_homsets_HSET)
                                              (pr1 (F R)))
  : is_right_adjoint FF.
Proof.
  apply is_right_adjoint_functor_of_reps.
  - intro R; apply epiall.
  - intros; apply Fepi.
Qed.

Corollary is_right_adjoint_functor_of_reps_from_pw_epi_choice 
           (choice : AxiomOfChoice.AxiomOfChoice_surj)
          (Fepi : forall R : Monad SET, isEpi (C:=functor_precategory HSET HSET has_homsets_HSET)
                                              (pr1 (F R)))
  : is_right_adjoint FF.
Proof.
  apply is_right_adjoint_functor_of_reps_from_pw_epi; (try apply preserves_to_HSET_isEpi); try assumption.
Qed.

End leftadjoint.

