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
Require Import TypeTheory.Displayed_Cats.Fibrations.

Require Import UniMath.CategoryTheory.HorizontalComposition.

Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.categories.category_hset_structures.
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

Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.SetValuedFunctors.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).
Local Notation "α ∙∙ β" := (horcomp β α) (at level 20).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).



Require Import Modules.Prelims.arities.

Require Import Modules.Prelims.lib.
Require Import Modules.Prelims.modules.
Require Import Modules.Prelims.quotientmonad.




    
Set Automatic Introduction.

  
  
(*
A morphism of arity F : a -> b induces a functor between representation Rep(b) -> Rep(a)

In this section we construct the left adjoint of this functor (which is defined whenever
F is an epimorphism)
 *)
Section leftadjoint.


Local Notation "'SET'" := hset_category.
Local Notation CAT_ARITY := (arity_category SET).
Local Notation REP := (rep_disp SET).

Variables (a b:CAT_ARITY) (R:REP a)
          (F:CAT_ARITY ⟦ a, b⟧).

Local Notation "## F" := (pr1 (pr1 (F)))(at level 3).



(*
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
  apply impred_isaprop.
  intros S.
  apply impred_isaprop.
  intros f.
  apply setproperty.
Qed.

Definition equivc_xy_prop (c:ob SET) x y : hProp :=
  (equivc  (X:=c) x y ,, isaprop_equivc_xy c x y).

Definition hrel_equivc c : hrel _ := fun x y => equivc_xy_prop c x y.

Lemma iseqrel_equivc c : iseqrel (hrel_equivc c).
Proof.
  unfold hrel_equivc, equivc_xy_prop, equivc; simpl;
  repeat split.
  -  intros x y z. cbn.
     intros h1 h2 S f.
     now rewrite h1,h2.
  - intros x y; cbn.
    intros h S f.
    now symmetry.
Qed.


Definition eqrel_equivc c : eqrel _ := (_ ,, iseqrel_equivc c).

(* For any f : X -> Y, #R f is compatible with previous equivalence relation *)
Lemma congr_equivc (x y:SET) (f:SET⟦ x,  y⟧):
                    iscomprelrelfun (eqrel_equivc x) (eqrel_equivc y) (# (## R) f).
Proof.
  intros z z' eqz S g.
  assert (hg := nat_trans_ax (pr1 (pr1 g)) x y f).
  cbn in eqz.
  apply toforallpaths in hg.
  etrans;[apply hg|].
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


  (* R' est un pseudo objet initial au sens suivant :
     Quel que soit        g : R ---> S morphisme dans la catégorie des représentations de a
     il existe un unique  u : R'---> S tel que g = u o projR
C'est un pseudo objet car il reste à montrer que R' est bien dans la catégorie des représentations
de a et que u est un morphisme de modules.
   *)
Section CandidatU.

Context {S:REP b} (m:R -->[ F] S).

Lemma compat_m :  ∏ (X : SET) (x y : ((pr1 R) X:hSet)),
  (quotientmonad.projR congr_equivc) X x = (quotientmonad.projR congr_equivc) X y
  → (pr1 m) X x = (pr1 m) X y.
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
  intros X x y.
  intros hxy.
  apply rel_eq_projR.
  intros S f.
  rewrite comp_cat_comp.
  symmetry.
  rewrite comp_cat_comp.
  eapply changef_path.
  symmetry.
  etrans.
  apply (Monad_Mor_μ (pr1 f)).
   
  etrans.
  apply (cancel_postcomposition (C:=SET)).
  etrans.
  apply cancel_postcomposition.
  apply u_def.
  apply cancel_precomposition.
  apply maponpaths.
  apply u_def.
  
  etrans.
  apply (cancel_postcomposition (C:=SET)).
  etrans.
  symmetry.      
  apply  (assoc (C:=SET) (projR (## R X)) (u f (## R X))).
  apply cancel_precomposition.
  etrans.
  
  symmetry.
  apply nat_trans_ax.

  apply cancel_postcomposition.
  apply (functor_comp _ (projR X) (u f X)).
  repeat rewrite assoc.
  reflexivity.
  cbn.
  apply maponpaths.
  apply maponpaths.
  apply maponpaths.
  apply pathsinv0.
  cbn.
  apply hxy.
Qed.
  
Let R'_monad  := R'_monad congr_equivc compat_μ_projR.
Let projR_monad  := projR_monad congr_equivc compat_μ_projR.
Section morphInitialU.

Context {S:REP b} (m:R -->[ F] S).

    

Definition u_monad {S} (m:R -->[ F] S) :=
  quotientmonad.u_monad compat_μ_projR (S:=pr1 S) (pr1 m) (compat_m m).

    
End morphInitialU.

  (* FIN DE LA TROISIEME ETAPE *)

Notation "# F" := (ar_mor _ F)
                    (at level 3) : arity_scope.
Delimit Scope arity_scope with ar.


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
      (X : SET) : m2 = m' ->
                  (# a')%ar m2 X = (# a')%ar m' X .
Proof.
  intro e; now induction e.
Qed.


Lemma eq_mr X : rep_τ _ R X ;; ## m X =
                pr1 (# a projR_monad)%ar X ;;
                    (F`` (R'_monad ))%ar X ;;
                pr1 (# b (u_monad m))%ar X ;;
                    rep_τ _ S X.
Proof.
  etrans.
  apply rep_ar_mor_ax.
  cpost _.
  etrans.
  cpost _.
  assert (h:pr1 m=compose (C:=category_Monad _) projR_monad(u_monad m) ).
  {
    use (invmap (Monad_Mor_equiv _ _ _)).
    apply (homset_property SET).
    apply nat_trans_eq.
    apply (homset_property SET).
    intro X'.
    apply (u_def m).
  }
  etrans.
  apply (cancel_ar_on _ _ _ h).
  etrans.
  eapply nat_trans_eq_pointwise.
  apply maponpaths.
  apply (disp_functor_comp a (xx:=tt) (yy:=tt) (zz:=tt) (f:=projR_monad)
                                (g:=u_monad m) tt tt).
  reflexivity.
  etrans;revgoals.
  rewrite <- assoc.
  cpre _.
  etrans.
  assert (hF :=disp_nat_trans_ax  (f:=u_monad m) (xx:=tt) (xx':=tt) F (tt)).
  apply LModule_Mor_equiv in hF.
  eapply nat_trans_eq_pointwise in hF.
  apply hF.
  apply homset_property.
  set (e := nat_trans_ax _ _ _ _).
  clear.
  unfold transportb.
  now induction (!e).
  reflexivity.
Qed.

      
End eq_mr.

Open Scope arity_scope.

(** This is the compatibility relation that is needed to construct
R'_rep_τ : b R -> R
*)
Lemma compat_rep_τ_projR :
      ∏ (X : SET) x y,
      ( pr1 (# a projR_monad )%ar X ;;  (F `` R'_monad) X) x
      =       ( pr1 (# a projR_monad )%ar X ;; (F `` R'_monad) X) y
      (* (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR_monad )%ar X) x *)
      (* = (( armor_ob _ F (pr1 R) X ) ;; pr1 (# b projR_monad )%ar X) y *)
      ->
            ((rep_τ _ R X ;; projR X) ) x = (rep_τ _ R X;; projR X)  y.
Proof.
  intros X x y comp.
  
  apply rel_eq_projR.
  intros S m.
  assert (h:= eq_mr m X).
  apply toforallpaths in h.
  etrans.
  apply h.
  apply pathsinv0.
  etrans.
  apply h.
  apply pathsinv0.
  cbn. 
  (* cbn in comp. *)
  apply maponpaths.
  apply maponpaths.
  (* apply maponpaths *)
  apply comp.
Qed.

    

(* F preserve the epis *)
Definition isEpi_FR' := isEpi (C:=functor_precategory HSET HSET has_homsets_HSET)
                             (pr1 (F `` R'_monad)).
(* a preserve les epis *)
Definition a_preserves_epi := ∏ M N (f:category_Monad _⟦M,N⟧),
                              isEpi f -> isEpi
                                          (C:= functor_category _ _) (pr1 ( # a f)%ar).

Context (Fepi:isEpi_FR') (aepi:a_preserves_epi).


Lemma isEpi_def_R'_rep_τ : isEpi
                          (compose (C:=functor_category _ _)
                                   (pr1 ((# a)%ar projR_monad))
                                   (pr1 (F `` R'_monad)%ar)).
Proof.
  apply (isEpi_comp (functor_category _ _));[|apply Fepi].
  apply aepi;    apply isEpi_projR_monad.
Qed.

Definition R'_rep_τ  : nat_trans (pr1 ( b` R'_monad)) R'.
Proof.
  apply (univ_surj_nt (* (A:= ##R □ ##R) (B:=functor_composite R' R')                     *)
           
           ( pr1 (# a projR_monad )%ar ;;;(( F`` (R'_monad)  )   ))
           (rep_τ _ R  ;;; projR)).
  (* asbtract these *)
  -  apply compat_rep_τ_projR.      
  - apply isEpi_def_R'_rep_τ.
Defined.

Definition R'_rep_τ_def :
  ∏ (X:SET),
  ( (# a (projR_monad))%ar) X ;; (F`` R'_monad) X;;R'_rep_τ X  
  =  rep_τ _ R X ;; projR X .
Proof.
  intro x.
  abstract(
      apply (univ_surj_nt_ax_pw ((pr1 (# a (projR_monad))%ar)  ;;; (F ``  R'_monad) ))).
Qed.


Lemma R'_rep_τ_module_laws : LModule_Mor_laws _ (T:=pr1 (b ` R'_monad))
                                           (T':=  tautological_LModule R'_monad)
                                           R'_rep_τ.
Proof.
  intro X.
  
  (* En vrai, je n'ai pas besoin ici que ce soit un epi pointwise (me semble-t-il)*)
  assert (epi : isEpi (* (C:=functor_Precategory SET SET) *)
                  ((  ( (pr1 (# a (projR_monad))%ar)  ;;;
                                                      (F ``  R'_monad) )    ∙∙ projR) X)).
  {
    apply Pushouts_pw_epi.
    apply PushoutsHSET_from_Colims.
    apply isEpi_horcomp.
    apply isEpi_projR.
    intro Y.
    apply Pushouts_pw_epi.
    apply PushoutsHSET_from_Colims.
    apply isEpi_def_R'_rep_τ.
  }
  apply epi.
  cbn -[R' compose].
  
  (* Etape 1 : utiliser R'_rep_τ_def pour faire disparaître R'_rep_τ *)
  etrans.    
  rewrite (assoc (C:=SET)).
  
  apply (cancel_postcomposition (C:=SET)).

  etrans.
  apply (cancel_postcomposition (C:=SET)).
  
  (* je dois faire reculer le b avec la naturalité de F R' *)
  etrans.
  rewrite <- (assoc (C:=SET)).
  apply (cancel_precomposition SET).
  symmetry.
  apply (nat_trans_ax (F`` R'_monad)).
  (* je dois faire avance le #a projR_monad en avec la naturalité de a *)
  rewrite  (assoc (C:=SET)).
  apply (cancel_postcomposition (C:=SET)).
  
  symmetry.
  apply (nat_trans_ax (pr1 ((# a)%ar projR_monad))).
  
  (* suppression de R'_rep_τ annoncé *)
  rewrite <- (assoc (C:=SET)).
  rewrite <- (assoc (C:=SET)).
  apply (cancel_precomposition SET).
  rewrite assoc.
  apply R'_rep_τ_def.
  
    (* maintenant je dois supprimer R'_mu avec R'_μ_def
  Je dois donc faire appraitre horcomp projR projR devant *)

    (*
      a_R p       m R'        p R'       mu'
a_R R ---> a_R R' ----> R R' ---> R' R' ---> R'

     *)
    

  etrans.
  rewrite assoc.
  (* 
C'est bon : il faut intervertir a_R p et m R' et ça devrait être bon
   *)
  apply (cancel_postcomposition (C:=SET)).
  apply (cancel_postcomposition (C:=SET)).
  apply nat_trans_ax.
  
  etrans.
  rewrite <- assoc.
  rewrite <- assoc.
  apply (cancel_precomposition SET).
  rewrite assoc.
  apply R'_μ_def.
  
  apply pathsinv0.
  (* Dans l'autre sens maintenant *)
  etrans.
  (* 
       a_p R         F_R' R       b_R' p         σ_b_R'      m'
a_R R -----> a_R' R -----> b_R' R ----> b_R' R' -----> b_R' -----> R'
   *)
  (* But : utiliser R'_rep_τ_def pour faire disparaître R'_rep_τ = m' 

Il faut utiliser le fait que F R' et a p sont des morphismes de modules.

faire reculer b_R' p
- par la naturalité de F_R'
- par la naturalité de a_R

   *)
  
  apply (cancel_postcomposition (C:=SET)).
  etrans.
  rewrite <- (assoc (C:=SET)).
  apply (cancel_precomposition SET).
  symmetry.
  apply (nat_trans_ax ((F`` R'_monad))).
  
  rewrite assoc.
  apply cancel_postcomposition.
  symmetry.
  apply (nat_trans_ax (pr1 ((# a)%ar projR_monad))).
  
  (* Maintenant on utilie le fait que F R' et p sont des morphismes de module *)
  etrans.
  rewrite assoc.
  apply (cancel_postcomposition (C:=SET)).
  repeat rewrite <- assoc.
  etrans.
  
  apply (cancel_precomposition SET).
  apply (cancel_precomposition SET).
  
  assert (hb := LModule_Mor_σ _ (  ( pr1 F R'_monad (tt))) X).
  (* On se fait emmerder à cause de # b identitye = identite *)
  assert (hid := functor_id (pr1 (pr1 b R'_monad (tt))) (R' X)).
  use (pathscomp0 _ hb).
  apply cancel_precomposition.
  cbn.
  apply funextfun.
  apply toforallpaths in hid.
  intro x.
  cbn.
  now rewrite hid.
    

    (* Ouf ! passons à #a p morphisme de module *)
    rewrite assoc,assoc.
    apply cancel_postcomposition.
    (* ici negro *)

    assert (ha := LModule_Mor_σ _ (  ( ((# a)%ar projR_monad))) ( X)).
    use (pathscomp0 _ ha).
    (* un petit de natural transformation_ax s'impose pour mettre projR_monad en premier *)
    etrans.
    apply cancel_postcomposition.
    apply (nat_trans_ax (pr1 ((# a)%ar projR_monad))).
    
    apply funextfun.
    intro x.
    apply idpath.

    (* voilà le travail ! maintenant on peu éliminer R'_rep_τ avec R'_rep_τ_def *)
    etrans.
    do 2  rewrite <- assoc.
    apply (cancel_precomposition SET).
    rewrite assoc.
    apply R'_rep_τ_def.
    rewrite assoc.    
    rewrite (assoc (C:=SET)).    
    apply (cancel_postcomposition (C:=SET)).
    etrans.
    (* m_R est un morphism de module *)

    assert (hm := LModule_Mor_σ _ (  ( (rep_τ  SET R )) ) X).
    symmetry.
    apply hm.
    apply idpath.
Qed.    

Definition R'_rep_τ_module :LModule_Mor _ (b` R'_monad)
                                     ( tautological_LModule R'_monad) :=
  (_ ,, R'_rep_τ_module_laws).


Definition R'_rep : (rep_disp SET b).
  use tpair.
  - exact R'_monad.
  - exact R'_rep_τ_module.
Defined.

  (* FIN DE LA PARTIE 5 *)

  (* projR est un morphisme de representation *)

Lemma projR_rep_laws : rep_ar_mor_law SET R R'_rep F projR_monad.
Proof.
  intro X.
  (* etrans. *)
  symmetry.
  apply (R'_rep_τ_def X).
Qed.

Definition projR_rep : R -->[F] R'_rep := (_ ,, projR_rep_laws).


End R'Representation.



  (* u morphisme de représentation *)
Section uRepresentation.

Context {S:REP b} (m:R -->[ F] S).
Context (Fepi:isEpi_FR') (aepi:a_preserves_epi).

Open Scope arity_scope.
  
  
(* Local Notation R'_REP := (R'_rep FepiR' aepiR). *)

Lemma u_rep_laws : rep_ar_mor_law SET (R'_rep Fepi aepi) S (disp_nat_trans_id (pr1 b))
                                  (u_monad m).
Proof.
  intro X.

  (* but : utiliser R'_rep_τ_def *)
  assert (epi : isEpi (* (C:=functor_Precategory SET SET) *)
                  (   ((pr1 (# a (projR_monad))%ar)  ;;;
                                                     (F``  R'_monad) )X    )).
  {
    
    apply Pushouts_pw_epi.
    apply PushoutsHSET_from_Colims.
    apply isEpi_def_R'_rep_τ; assumption.
  }
  
  apply epi.
  
  etrans.
  apply assoc.
  
  etrans.
  cpost _.
  (*  apply (R'_rep_τ_def X) takes a long time, but use is immediate *)
  use (R'_rep_τ_def Fepi aepi X).
  
  (* faire disparaitre le u avec u_def *)
  etrans.
  rewrite <- assoc.
  cpre _.      
  eapply pathsinv0.
  apply (u_def m).
  
  (* utiliser le fait que m est un morphisme de representation *)
  etrans.
  apply (rep_ar_mor_ax _ m X).
  
  rewrite assoc.
  cpost _.
  
  (* on réécrit m *)
  etrans.
  cpost _.
  apply (cancel_ar_on _ (compose (C:=category_Monad _) projR_monad (u_monad m))).
  use (invmap (Monad_Mor_equiv _ _ _)).
  { apply homset_property. }
  { apply nat_trans_eq.
    apply homset_property.
    apply (u_def m).
  }
  
  etrans.
  
  etrans.
  cpost _.
  use (nat_trans_eq_pointwise _ X); cycle 1.
  apply maponpaths.
  assert (yop:= @disp_functor_comp _ _ _ _ _ a ).
  assert (yop2 := fun xx yy zz  =>yop _ _ _ xx yy zz projR_monad (u_monad m)).
  assert (yop3 := yop2 (tt) (tt) (tt) (tt) (tt)).
  apply yop3.
  (* todo : systématiser la séquence préécdente *)
  cpost _.
  cbn -[compose].
  apply idpath.
  
  
  etrans.
  cpost _.
  eapply (pathsinv0 (b:=pr1 (#a projR_monad)%ar X ;; pr1 (#a (u_monad m))%ar X )).
  reflexivity.
  etrans.
  rewrite <- assoc.
  cpre _.
  etrans.
  assert (hF :=disp_nat_trans_ax  (f:= (u_monad m)) (xx:=tt) (xx':=tt) F (tt)).
  apply LModule_Mor_equiv in hF.
  eapply nat_trans_eq_pointwise in hF.
  apply hF.
  apply homset_property.
  set (e:= nat_trans_ax _ _ _ _).
  
  unfold transportb.      
  induction (!e).
  
  (* cbn -[compose]. *)
  apply idpath.
  apply funextfun.
  intro x.
  cbn.
  apply idpath.
Qed.


Definition u_rep : (R'_rep Fepi aepi) -->[(disp_nat_trans_id (pr1 b))] S := (_ ,, u_rep_laws).
      
End uRepresentation.
  (* FIN DE LA PARTIE 6 *)

 Section uUnique.
 Context {S:REP b} (hm: iscontr (R -->[ F] S)).
 Context (Fepi:isEpi_FR') (aepi:a_preserves_epi).

 Variable u'_rep : (R'_rep Fepi aepi) -->[(disp_nat_trans_id (pr1 b))] S.
 
 Lemma u_rep_unique : u'_rep = (u_rep (pr1 hm) Fepi aepi).
 Proof.
   set (m' := (projR_rep Fepi aepi ;; u'_rep)%mor_disp).
   apply rep_ar_mor_mor_equiv.
   intro X.
   
   cbn.
   unfold u.
   
   revert X.
   apply (univ_surj_nt_unique _ _ _ _ (##u'_rep)).
   set (m := (pr1 hm ;; id_disp S)%mor_disp).
   assert (eqm':m' = m).
   {
     subst m.
     rewrite id_right_disp .
     apply transportf_transpose .
     apply (pr2 hm).
   }
   assert(eqm'2: pr1 m' = pr1 m).
   now rewrite eqm'.
   apply Monad_Mor_equiv in eqm'2.
   apply nat_trans_eq.
   apply has_homsets_HSET.
   intro X.
   eapply nat_trans_eq_pointwise in eqm'2.
   apply eqm'2.
   apply has_homsets_HSET.
Qed.      
    
End uUnique.

End leftadjoint.

