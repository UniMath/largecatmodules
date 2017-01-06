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

Require Import Modules.Prelims.epipw.
Require Import Modules.Prelims.setscomplements.



Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).
Local  Notation "α ∙∙ β" := (horcomp β α) (at level 20).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).

(* En attendant que la pull request soit acceptée dans UniMaths  *)
Require Import Modules.Prelims.effectiveepis.
Require Import Modules.Prelims.eqdiag.
Import EffectiveEpis.


Require Import Modules.Prelims.ardef.
Require Import Modules.Prelims.quotientfunctor.

Require Import Modules.Prelims.lib.




    
Set Automatic Introduction.






  
 


(* used as admit when Qed takes too long *)
Lemma toolong : forall A, A.
Admitted.                       


  
(*
A morphism of arity F : a -> b induces a functor between representation Rep(b) -> Rep(a)

In this section we construct the left adjoint of this functor (which is defined whenever
F is an epimorphism)
 *)
Section leftadjoint.


  Local Notation C := hset_Precategory.
  Local Notation SET := hset_Precategory.
  Local Notation PARITY := (arity_Precategory C).
  Local Notation BREP := (brep_disp C).

  Variables (a b:PARITY) (R:BREP a)
            (F:PARITY ⟦ a, b⟧).

  Local Notation "## F" := (pr1 (pr1 (F)))(at level 3).

  Definition equivc   {c:ob C} (x y:pr1 ( ## R c)) :=
                                  (Π (S:BREP b) ( f : R -->[F] S),
                                   pr1 (pr1 f) c x = ## f c y).


  Lemma isaprop_equivc_xy (c:ob C) x y : isaprop (equivc (c:=c) x y).
    intros.
    apply impred_isaprop.
    intros S.
    apply impred_isaprop.
    intros f.
    apply setproperty.
  Qed.

  Definition equivc_xy_prop (c:ob C) x y : hProp :=
    (equivc  (c:=c) x y ,, isaprop_equivc_xy c x y).

  Definition hrel_equivc c : hrel _ := fun x y => equivc_xy_prop c x y.

  Lemma iseqrel_equivc c : iseqrel (hrel_equivc c).
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

  Lemma congr_equivc: Π (x y:C) (f:C⟦ x,  y⟧), iscomprelrelfun (eqrel_equivc x) (eqrel_equivc y) (# (## R) f).
    intros.
    red.
    intros z z' eqz.
    intros S g.
    cbn in eqz.
    unfold equivc in eqz.

    assert (hg := nat_trans_ax (pr1 (pr1 g)) x y f).

    apply toforallpaths in hg.
    etrans.
    apply hg.
    symmetry; etrans. apply hg.
    cbn.
    now rewrite eqz.
  Qed.


  
  (* Foncteur candidat 

I need to make it not convertible to quot_functor otherwise
Coq takes a long time to check or compute things.
For example :   R' ((R' □ R') c) = (R' □ R') (R' c) by reflexivity
is so slow when R' is definitely equal to quot_functor !

*)
  Definition R' := ( quot_functor (pr1 (pr1 R)) _ congr_equivc).
  (* Opaque R'. *)

(*
  Lemma bizarre c: (* forall (R':functor SET SET),  *)  R' ((R' □ R') c) = (R' □ R') (R' c).
    (* intros ?. *)

    reflexivity.
  Qed.
*)
    (* cbn - [R']. *)
    (* reflexivity. *)
    (* !! amazing 
Qed takes so long !!!
*)
  (* Admitted.  *)

  Definition projR : (## R) ⟶ R':= proj_quot _ _ congr_equivc.

  (* Definition projR_lock : (## R) ⟶ R':= proj_quot _ _ congr_equivc. *)

  Arguments projR : simpl never.
  Arguments R' : simpl never.

(* TODO : déplacer dans quotient vector.v *)
  Lemma eq_proj_quot_rel X x y : projR X x = projR X y ->equivc x y.
  Proof.
    apply invmap.
    apply (weqpathsinsetquot (eqrel_equivc X)).
  Qed.
  Lemma rel_eq_proj_quot X x y : equivc x y ->projR X x = projR X y.
  Proof.
    apply (weqpathsinsetquot (eqrel_equivc X)).
  Qed.

  

  (* R' est un pseudo objet initial au sens suivant :
     Quel que soit        g : R ---> S morphisme dans la catégorie des représentations de a
     il existe un unique  u : R'---> S tel que g = u o projR
C'est un pseudo objet car il reste à montrer que R' est bien dans la catégorie des représentations
de a et que u est un morphisme de modules.
   *)
  Section CandidatU.
    Context {S:BREP b} (m:R -->[ F] S).

    Definition u : nat_trans (pr1 R') (## S).
      apply (univ_surj_nt projR (## m)); [| apply is_epi_proj_quot].
      abstract(
      intros X x y eqpr;
      apply eq_proj_quot_rel in eqpr;
      apply eqpr).
    Defined.

    Lemma u_def : Π x, ## m x = projR x ;; u x.
    Proof.
      symmetry.
      apply univ_surj_nt_ax_pw.
    Qed.

  End CandidatU.


  Definition R'_η : (functor_identity C) ⟶ R' := η (## R) ;;; projR .

  Lemma R'_η_def : Π x, R'_η x =  η (## R) x ;; projR x.
  Proof.
    intro x.
    apply idpath.
  Qed.



  (* Notation GODMENT a b := (horcomp a b) (only parsing). *)




  
  (* R'_μ is defined by the following diagram :
<<
                  μ R
            R R  ----->   R
             |           |
 projR projR |     H     | projR
             v           v
            R' R' ---->  R'
                  R'_μ
>>
   *)
  Lemma compat_μ_projR : Π (X : SET) (x y : pr1 ((pr1 (## R □ ## R)) X)),
                            (projR ∙∙ projR) X x = (projR ∙∙ projR) X y →
                            (μ ## R;;; projR) X x = (μ ## R;;; projR) X y.
  Proof.
    intros X x y.
    intros hxy.
    apply rel_eq_proj_quot.
    intros S f.
    rewrite comp_cat_comp.
    match goal with |- ?f0 x = ?t => set (z:=f0); change t with (z y) end.
    neweqsubst z.
    etrans.
    apply Monad_Mor_μ.
   
    etrans.
    apply cancel_postcomposition.
    etrans.
    apply cancel_postcomposition.
    apply u_def.
    apply cancel_precomposition.
    apply cancel_functor_on_morph.
    apply u_def.

    etrans.
    apply cancel_postcomposition.
    etrans.
    symmetry.      
    apply  (assoc (C:=SET) (projR (## R X)) (u f (## R X))).
    apply cancel_precomposition.
    etrans.
    
    symmetry.
    apply nat_trans_ax.

    apply cancel_postcomposition.
    apply (functor_comp _ _ _ _ (projR X) (u f X)).
    repeat rewrite assoc.
    reflexivity.
    cbn.
    apply maponpaths.
    apply maponpaths.
    apply maponpaths.
    apply toolong.
    (* exact hxy. *)
  Qed.
  
  Definition R'_μ  : nat_trans ( R'□  R')  ( R').
  Proof.
    apply (univ_surj_nt (A:= ##R □ ##R) (B:=functor_composite R' R')                    
                       ( projR ∙∙ projR)
                       (μ  (## R) ;;; projR)).
    (* asbtract these *)
    -  apply compat_μ_projR.
      
    - abstract(apply isEpi_horcomp;
               [|apply is_pointwise_epi_from_set_nat_trans_epi];
      apply is_epi_proj_quot).
  Defined.

  Lemma R'_μ_def : Π (x:SET),
                     (projR ∙∙ projR) x ;; R'_μ x = μ (## R) x ;; projR x .
  Proof.
    intro x.
    unfold R'_μ.
    apply univ_surj_nt_ax_pw.
  Qed.

  Definition R'_Monad_data : Monad_data C := ((R' ,, R'_μ) ,, R'_η).
  (*
  Goal Π c, identity (R'_Monad_data c) = identity (R'_Monad_data c).
    intro c.
    unfold R'_Monad_data.
    simpl.
    cbn.
   *)



  
  Lemma R'_Monad_laws : Monad_laws R'_Monad_data.
  Proof.
    repeat split.
    -       cbn -[R' compose identity].
      intro c.
      use (is_pointwise_epi_from_set_nat_trans_epi _ _ _ (projR)).
      apply is_epi_proj_quot.

      repeat rewrite assoc.
      etrans.
      apply (cancel_postcomposition (b:=R' (R' c))).
      apply (cancel_postcomposition _ ((η ## R) (## R c) ;; # (## R) (projR _))).
      apply (nat_trans_ax (η ## R)).

      rewrite <- assoc.
      rewrite <- assoc.
      etrans.
      apply (cancel_precomposition _ _ _ (R' c)).
      apply R'_μ_def.
      
      rewrite assoc, id_right.
      etrans.
      apply cancel_postcomposition.
      apply (Monad_law1 (T:=pr1 R)).
      apply id_left.
      
    - intro c.
      etrans.
      apply cancel_postcomposition.
      etrans.
      apply cancel_functor_on_morph.
      apply R'_η_def.
      apply functor_comp.
      use (is_pointwise_epi_from_set_nat_trans_epi _ _ _ projR).
      apply is_epi_proj_quot.
      repeat rewrite assoc.
      etrans.
      (apply cancel_postcomposition).
      apply cancel_postcomposition.
      symmetry.
      apply (nat_trans_ax (projR)).
      rewrite <- assoc.
      rewrite <- assoc.
      etrans.
      apply cancel_precomposition.
      apply R'_μ_def.
      rewrite assoc, id_right.
      rewrite (Monad_law2 (T:=pr1 R)).
      now rewrite id_left.
    - intro c.             
      cbn -[R' compose].
      (* Note : 

If I write instead :
  assert (epi :isEpi (horcomp projR (horcomp projR projR)  c)).
(convertibly the same by associativity)

then 'apply epi' takes a huge amount of time for Coq !!
This is due to the fact that Coq takes a long time to show that
   ((R' □ R') □ R') c = R' ((R' □ R') c)
because it has a very bad computing strategy. He tries to evaluates R'
which is bad idea. Probably because somewhere there is a Defined instead of 
Qed for some proof, and I suspect somewhere in the section about
quotients in basics/Sets.v

       *)
      assert (epi :isEpi (horcomp (horcomp projR projR) projR c)).
      {
        apply Pushouts_pw_epi.
        apply HSET_Pushouts.        
        apply isEpi_horcomp;[   apply isEpi_horcomp|]; try apply Pushouts_pw_epi;
          try apply HSET_Pushouts; apply is_epi_proj_quot.
      }
      apply epi.

      (* To understand the proof, see the string diagram muproof sent to
Benedikt.

Legend of the diagram :
- μ = μ R
- ν = R'_μ
- i = projR
*)      
      etrans.

      (* First equality *)
      etrans.

      apply assoc.

      rewrite horcomp_pre_post.
      
      etrans.
      apply (cancel_postcomposition (C:=SET)).
      
      etrans.
      apply (cancel_postcomposition (C:=SET)).
      unfold compose.
      cbn -[R' compose horcomp].
      reflexivity.

      etrans.
      rewrite <- assoc.      
      apply (cancel_precomposition SET).
      rewrite <- (functor_comp (C:=SET) (C':=SET)).
      apply cancel_functor_on_morph.
      apply R'_μ_def.
      
      rewrite functor_comp,assoc.
      apply cancel_postcomposition.
      symmetry.
      apply (nat_trans_ax (projR)).

      (* second equality *)
      rewrite <- assoc.
      rewrite <- assoc.
      apply (cancel_precomposition (SET)).     
      apply (R'_μ_def c).

      (* third equality *)
      etrans.
      rewrite assoc.
      
      etrans.
      apply cancel_postcomposition.
      apply (Monad_law3 (T:=pr1 R) c).

      (* Fourth equality *)
      rewrite <- assoc.
      
      etrans.
      apply cancel_precomposition.
      symmetry.
      apply R'_μ_def.

      rewrite assoc.      
      apply cancel_postcomposition.

      (* Fifth equality *)
      etrans.
      cbn -[projR compose].
      rewrite (assoc (C:=SET)).
      apply (cancel_postcomposition (C:=SET)).
      symmetry.
      apply R'_μ_def.


      (* Close to the end *)
      etrans.
      rewrite <- assoc.
      apply (cancel_precomposition SET).
      symmetry.
      apply (nat_trans_ax (R'_μ) (## R c)).
      
      rewrite assoc.
      reflexivity.

      etrans.
      rewrite <- assoc.
      reflexivity.

      etrans.
      apply cancel_postcomposition.

      assert (huse := (horcomp_assoc projR projR projR c)).
      cbn.
  Admitted.
  (*
      TROP DE TEMPS ICI !
      apply huse.
    cbn.
   apply idpath.
Qed.
*)
  (* Le QED précédent prend énormément de temps.. pourquoi ? *)

  Definition R'_monad : Monad _ := (_ ,, R'_Monad_laws).

  (*

FIN DE LA PREMIERE ETAPE

   *)

  Lemma projR_monad_laws: Monad_Mor_laws (T':= R'_monad) projR.
  Proof.
    split.
    - intro X.
      symmetry.
      apply R'_μ_def.
    - intro X.
      symmetry.
      apply R'_η_def.
  Qed.

  Definition projR_monad : Monad_Mor (pr1 R) (R'_monad) :=
    (_ ,, projR_monad_laws).


  (* FIN DE LA SECONDE ETAPE *)

  Section morphInitialU.
    Context {S:BREP b} (m:R -->[ F] S).

    Ltac cpre :=  apply cancel_precomposition.
    Ltac cpost :=  apply cancel_postcomposition.
    

    Lemma u_monad_laws : Monad_Mor_laws (T:= R'_monad) (T':=## S) (u m).
    Proof.
      red.
      split.
      - intro X.
        assert (epi :isEpi ( (horcomp projR projR) X)).
        {
          apply Pushouts_pw_epi.
          apply HSET_Pushouts.
          apply isEpi_horcomp; try apply Pushouts_pw_epi;
            try apply HSET_Pushouts; apply is_epi_proj_quot.
        }
        apply epi.


        (* Now the real work begins *)
        etrans.

        (* use the monadicity of μ *)
        apply cancel_postcomposition.
        apply (nat_trans_ax (projR)).
        etrans.
        

        
        rewrite assoc.        
        apply cancel_postcomposition.
        symmetry.
        apply (Monad_Mor_μ (projR_monad)).

        (* definition of u *)
        etrans.
        rewrite <- assoc.
        cpre.
        symmetry.
        apply u_def.

        (* m is a morphism of monad *)
        etrans.
        apply (Monad_Mor_μ (pr1 m)).

        (* Definition of u *)
        etrans.
        
        cpost.
        etrans.
        etrans.
        cpost.
        apply u_def.        
        cpre.
        etrans.
        apply cancel_functor_on_morph.
        apply u_def.
        apply functor_comp.

        (* il s'agit de rememmtre les termes dans l'ordre *)

        rewrite assoc.
        cpost.
        rewrite <- assoc.
        cpre.
        symmetry.
        apply (nat_trans_ax (u m)).
        rewrite assoc.
        cbn.
        reflexivity.
      - intro X.
        etrans.
        cpost.
        apply R'_η_def.

        rewrite <- assoc.
        rewrite <- u_def.
        apply (Monad_Mor_η (pr1 m)).
    Qed.

    Definition u_monad : Monad_Mor ( R'_monad) (pr1 S) :=
      (_ ,, u_monad_laws).
    
  End morphInitialU.

  (* FIN DE LA TROISIEME ETAPE *)

  Section R'Representation.

     (* R'_μr is defined by the following diagram :
<<
                  μr R
            a R  ----->  R
             |           |
         F R |           | projR
             v           |
            b R          |
             |           |
     b projR |           |
             v           v
           b R' -------> R'
                R'_μr

>>
      *)

    Local Notation zab F R X :=(pr1 (pr1 F (pr1 R) tt) X). (* (at level 3). *)
    Check (pr1 b).

    Definition triv_mor {C:Precategory} {A B:C} (f:C⟦ A,B⟧) :
      mor_disp (D:=liftcat_disp C) tt tt f := tt.

    Notation "[# b f ]" :=
      (functor_over_on_morphisms (pr1 b)
                                     (triv_mor (C:=(monadPrecategory _))
                                                     f))
        (at level 200) :arity_scope.

    Check (functor_over_on_morphisms (pr1 b)
                                     (triv_mor (C:=(monadPrecategory _))
                                                     projR_monad)).

    Check ([# b projR_monad ]).


    Delimit Scope arity_scope with ar.
    
    (*                     (at level 3) : triv_mor_disp_scope. *)

    Section eq_mr.
      Context {S:BREP b} (m:R -->[ F] S).
      Open Scope arity_scope.
      Check ([# b projR_monad ]).

      Lemma eq_mr : μr _ R ;; m =
                    ;;
                 (# b u_monad)%ar
                    μr _ (pr1 S) 
    End eq_mr.

    
  Lemma compat_μ_projR : Π (X : SET) x y,
                          (( zab F R X ) ;;
                                         pr1 (# (pr1 b)
                                            (triv_mor (C:=(monadPrecategory _))
                                                      projR_monad) )%mor_disp X)
                                         x
                         =
                          (( zab F R X ) ;;
                                         pr1 (# (pr1 b)
                                            (triv_mor (C:=(monadPrecategory _))
                                                      projR_monad) )%mor_disp X)
                                         y
                                         ->
                                         ((μr _ R;;; projR) X) x = (μr _ R;;; projR) X y.
  Proof.
  Qed.
    
  End R'Representation.

End leftadjoint.

Section representable.


  Local Notation C := hset_Precategory.
  Local Notation PARITY := (arity_Precategory C).
  Local Notation BREP := (brep_disp C).

  Local Notation initial_rep_type a :=   (Initial (fiber_precategory BREP a)).


  (* an arity is representable if there is an initial object in the category
of representations of the arity*)
  Definition is_representable (a:PARITY) := initial_rep_type a.

  Variables (a b:PARITY) (R:initial_rep_type a)
    (F:Epi _ a b).


  (* Now we are to prove that b is representable *)

  (* We define the quotient of R *)
  Definition R'_data c := Quot F (pr1 R) c.
