Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.kernels.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.Monads.
Require Import Modules.Prelims.modules.
(* Require Import UniMath.CategoryTheory.Modules. *)


Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.
Require Import TypeTheory.Displayed_Cats.Auxiliary.
Require Import TypeTheory.Displayed_Cats.Core.
Require Import TypeTheory.Displayed_Cats.Constructions.
Require Import TypeTheory.Displayed_Cats.Fibrations.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Local Notation "G □ F" := (functor_composite F G) (at level 35).
Local Notation "F ;;; G" := (nat_trans_comp _ _ _ F G) (at level 35).

(* Trouvé dans SubstitutionsSystem/Notation *)
Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Notation "Z ∘ α" := (post_whisker α Z) (at level 50, left associativity).


Require Import Modules.Prelims.ardef.
Require Import Modules.Prelims.quotientfunctor.

(* Let f : A -> B be a function.
It induces an equivalence relation on A.
Reciproquement, any equivalence relation on A is yielded by such an equivalence

Question pour Benedikt : est ce que ce truc est déjà démontré quelque part dans 
lalib standard
 *)
Section FunEquiv.
  Context {A B:hSet} (f:A -> B).

  Definition fun_rel x y := f x = f y.

  Lemma isaprop_fun_rel  x y : isaprop (fun_rel x y).
    intros;
    apply setproperty.
  Qed.

  Definition fun_rel_prop x y : hProp :=
    (fun_rel x y ,, isaprop_fun_rel x y).

  Definition fun_hrel  : hrel _ := fun x y => fun_rel_prop x y.

  Lemma iseqrel_fun_hrel  : iseqrel (fun_hrel ).

    unfold fun_hrel, fun_rel_prop, fun_rel; simpl;
      repeat split; red ; simpl; intros; simpl.
    -  etrans; eauto.
    - now symmetry.
  Qed.

  Definition fun_eqrel : eqrel _ := (_ ,, iseqrel_fun_hrel ).
End FunEquiv.



(* Definition of an effective epimorphism.
An effective epimorphism p: A -> B is a morphism wich as a kernel pair and which
is the coequalizer of its kernel pair.

This property is true of any epimorphism in Set. It allows to lift epimorphism
*)
Section EffectiveEpi.
  Context {C:precategory} {A B:C}.
  Variable (f: C ⟦A,B⟧).

  Definition kernel_mor := Pullback  f f.



  Definition isEffectiveEpi :=
    Σ  g:kernel_mor, (Σ H :  (PullbackPr1 g) ;; f = (PullbackPr2 g) ;; f, isCoequalizer (PullbackPr1 g)
                                                                       (PullbackPr2 g) f H).
End EffectiveEpi.


Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.graphs.pullbacks.

(* wtf ? Il y a deux notions de pullback et je ne trouve pas le resultat suivant *)
Definition equiv_Pullback {C:Precategory} {a b c  : C} {f : C ⟦b, a⟧} {g : C ⟦c, a⟧}
            (pb  : Pullback _ f g):
  limits.pullbacks.Pullback f g.
Proof.
  intros.
  use  (limits.pullbacks.mk_Pullback _ _  (PullbackObject _ pb)
                                     (PullbackPr1 _ pb) (PullbackPr2 _ pb) ).
  apply PullbackSqrCommutes.
  apply equiv_isPullback_2.
  apply homset_property.
  apply isPullback_Pullback.
  apply homset_property.
Defined.

Section kernel_mor_Set.

  Local Notation SET := hset_Precategory.
  Context  {A B:SET}.
  Variable (f: SET ⟦A,B⟧).

  Lemma Pullbacks_HSET : Pullbacks SET.
    clear.
  Admitted.

  Definition kernel_mor_set : kernel_mor f.
    red.
    apply equiv_Pullback.
    apply LimsHSET_of_shape.
  Defined.

    
  Local Notation g := kernel_mor_set.

  Import limits.pullbacks.

  Lemma kernel_mor_eq
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
Abort.
End kernel_mor_Set.


  
(* Let F : C -> Set be a functor.
Any natural transformation m : F -> G yields a quotient functor obtained by
splitting m into epi/mono.

A corollary is that m induces a relation on each image object of F *)


(* Preuve qu'on peut relever les épi dans la catégorie Set
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

*)
Section LiftEpi.

  Local Notation SET := hset_Precategory.
  Context {A B C:SET}.
  Variables        (p : SET ⟦ A, B ⟧) (f: SET ⟦ A, C ⟧).



  Hypothesis (comp_f_epi: Π x y,  p x =  p y -> f x = f y).

  (* Reformulation of the previous hypothesis *)
  Lemma comp_f_epi_hprop : Π b : pr1 B, isaprop (image (fun (x:hfiber ( p) b) => f (pr1 x))).
  Proof.
    intro b.
(* inspiré de     isapropimeqclass *)
    apply isapropsubtype.
    intros x1 x2.
    apply (@hinhuniv2 _ _ (hProppair _ (pr2 C (x1) ( x2)))).
    simpl;
    intros y1 y2; simpl.
    unfold hfiber in y1,y2.
    destruct y1 as [ [z1 h1] h1' ].
    destruct y2 as [ [z2 h2] h2' ].
    rewrite <- h1' ,<-h2'.
    apply comp_f_epi;simpl.
    rewrite h1,h2.
    apply idpath.
  Qed.

  Hypothesis (surjectivep : issurjective p).

  Definition lift_epi : SET ⟦B, C⟧.
    (* inspiré de setquotuniv *)
    intros b.
    assert (c:(hProppair _  (comp_f_epi_hprop b))).
    {
    generalize (surjectivep b).
    apply hinhuniv.
    apply prtoimage.
    }
    exact (pr1 c).
  Defined.

  Lemma lift_epi_ax : Π x,  lift_epi (p x) = f x.
  Proof.
    intro x.
    cbn.
    unfold lift_epi.
    unfold hinhuniv; cbn.
    
    match goal with |- pr1 ?x = _ => set (z:=x) end.
    simpl in z.
    assert (hz := pr2 z).
    cbn beta in hz.
   TODO demander à Benedikt.
  Qed.


End LiftEpi.

(*
J'aurais besoin de la réciproque de surjectionisepitosets

 *)
Section ReciproqueSurjectionIsEpiToSets.
  Local Notation SET := hset_Precategory.
  Context {A B:SET}.
  Variables        (p : SET⟦A, B⟧) (hp:isEpi p).

  Lemma epitosetsissurjection : issurjective p.
  Proof.
    red.
    intros y.
    assert (hepi := hp).
    red in hepi.
    simpl in hepi.
    apply hinhpr.
    red.
    clear.
  Admitted.
  (* proved in Coq Hott, and in the HoTT book. however I don't want to bother with this proof *)

End ReciproqueSurjectionIsEpiToSets.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

(* Composing a functor and a diagram
Demadner à Benedikt : pas trouvé dans la lib *)
Section CompDiagrams.
  Context { C D:precategory} {g:graph}.
  Variables  (d:diagram g C) (F:functor_data C D).
  (* Σ (f : vertex g -> C), Π (a b : vertex g), edge a b -> C⟦f a, f b⟧. *)
  Definition comp_diag_functor : diagram g D.
    exists (fun x => F (pr1 d x)).
    exact (fun a b e => #F (pr2 d a b e)).
  Defined.

End CompDiagrams.

(*
Proof that f: A -> B is an epi is the same as saying that the diagram
A ---> B
|      |
|      |  id         is a pushout
‌\/     ‌‌\/
B----> B
  id
*)
Section EpiPushoutId.

  Context {C:Precategory} {A B:C} (f:C⟦A,B ⟧).
  Require Import UniMath.CategoryTheory.limits.pushouts.


  Lemma epi_to_pushout : isEpi f -> isPushout f f (identity _) (identity _) (idpath _).
  Proof.
    intro h.
    red.
    intros x p1 p2 eqx.
    assert (hp : p1 = p2).
    { now apply h. }
    destruct hp.
    apply (unique_exists p1).
    rewrite id_left.
    now split.
    intros y. apply isapropdirprod; apply homset_property.
    intros y [h1 _].
    now rewrite id_left in h1.
  Qed.

  Lemma pushout_to_epi :  isPushout f f (identity _) (identity _) (idpath _)-> isEpi f.
  Proof.
    intros hf.
    intros D p1 p2 hp.
    apply hf in hp.
    destruct hp as [[p [hp1 hp2]] _].
    now rewrite <- hp1,hp2.
  Qed.

End EpiPushoutId.

(* definition of a functor that creates colimits.

Demander à Benedikt : pas trouvé dans la lib

definition de la préservation des colimites (pas cherché dans la lib)
*)
Section CreateCoLimits.
  Context { C D:precategory}.
  Variable (F:functor_data C D).
(*
  Definition preservesCoLimit (g:graph) (d:diagram g C) :=
    Π (g : graph) (d : diagram g C), ColimCocone d -> ColimCocone (comp_diag_functor d F).

  Definition reflectsCoLimits :=
    Π (g : graph) (d : diagram g C) (x , isColimCocone (comp_diag_functor d F) -> ColimCocone d.
 *)
(*
  Definition createsCoLimit (g:graph) (d:diagram g C) :=
    Σ (f:ColimCocone (comp_diag_functor d F) -> ColimCocone d), isColimCocone



  Definition createsCoLimits :=
    Π (g : graph) (d : diagram g C),
    Σ yop : ColimCocone (comp_diag_functor d F) -> ColimCocone d, isColimCocone (#F yop ).
*)
End CreateCoLimits.


(* The following section is copied from Pullback_pointwise section in limits/Pullbacks.v

Unfortunately, there is no such analogue in limits/Pushouts...

I am interested in showing that if D has colimits, then a colimit in the category [C,D] is
a colimit pointwise. I tried to derive this result from limits/graphs/colimits.v and the
construction of ColimitFunctors, however the pointwise diagrams seems to behave badly
(see tried example in the next section *)

Set Automatic Introduction.

      (** * Pushouts in functor categories *)
Section pushouts_pointwise.

(** Diagram for this section:
<<
          d
    J -------> H
    |          |
  c |          | b
    v          v
    G -------> F
         a
>>
 *)
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Context {C D : precategory} (hsD : has_homsets D).
Let CD := [C, D, hsD].
Context {F G H J : CD}.
Context {a : CD ⟦G, F⟧}{b : CD ⟦H, F⟧}{c : CD⟦J,G⟧}{d : CD⟦J, H⟧}.

Variable Hcomm : c ;; a = d ;; b.

Arguments mk_Pushout {_ _ _ _ _ _ _ _ _ _ } _ .

Let Hcommx x := nat_trans_eq_pointwise Hcomm x.



Local Definition g (T : Π x, isPushout _ _ _ _ (Hcommx x))
      E (h : CD ⟦ G,E ⟧) (k : CD ⟦ H,E⟧)
      (Hhk : c;; h  = d ;; k ) : Π x, D ⟦ pr1 F x, pr1 E x ⟧.
Proof.

  intro x; apply (PushoutArrow (mk_Pushout (T x)) _ (pr1 h x) (pr1 k x)).
  abstract (apply (nat_trans_eq_pointwise Hhk)).
Defined.

Local Lemma is_nat_trans_g (T : Π x, isPushout _ _ _ _ (Hcommx x))
      E (h : CD ⟦ G, E ⟧) (k : CD ⟦ H, E ⟧)
      (Hhk :  c;; h  = d ;; k) : is_nat_trans _ _ (λ x : C, g T E _ _ Hhk x).
Proof.
  intros x y f; unfold g.
  apply (MorphismsOutofPushoutEqual (T x)).
  + rewrite !assoc, (PushoutArrow_PushoutIn1 (mk_Pushout (T x))).
    rewrite <- (nat_trans_ax a), <- assoc.
    now rewrite (PushoutArrow_PushoutIn1 (mk_Pushout (T y))), (nat_trans_ax h).
  + rewrite !assoc,(PushoutArrow_PushoutIn2 (mk_Pushout (T x))).
    rewrite <- (nat_trans_ax b), <- assoc.
    now rewrite (PushoutArrow_PushoutIn2 (mk_Pushout (T y))), (nat_trans_ax k).
Qed.

Lemma po_if_pointwise_po : (Π x, isPushout _ _ _ _ (Hcommx x)) ->
                           isPushout _ _ _ _ Hcomm.
Proof.
  intro T.
  use mk_isPushout; intros E h k Hhk.
  use unique_exists.
  - mkpair.
    + intro x; apply (g T E h k Hhk).
    + apply is_nat_trans_g.
  - abstract (split; apply (nat_trans_eq hsD); intro x;
              [ apply (PushoutArrow_PushoutIn1 (mk_Pushout (T x)))
              | apply (PushoutArrow_PushoutIn2 (mk_Pushout (T x))) ]).
  - abstract (intro; apply isapropdirprod; apply functor_category_has_homsets).
  - abstract (intros t [h1 h2]; destruct h as [h Hh];
              apply (nat_trans_eq hsD); intro x; apply PushoutArrowUnique;
              [ apply (nat_trans_eq_pointwise h1) | apply (nat_trans_eq_pointwise h2) ]).
Defined.



End pushouts_pointwise.

(* Definition of nat trans between diagrams *)
Section diagramNatTrans.

  Context {g:graph} {C:precategory} .

  Local Notation diag := (diagram g C).
  Local Notation "# F" := (dmor F)(at level 3).

  Definition is_diag_nat_trans {J J' : diag}
             (t : Π x : vertex g, dob J x -->  dob J' x) :=
    Π (x x' : vertex g)(f : edge x x'),
    # J f ;; t x' = t x ;; #J' f.


  Lemma isaprop_is_nat_trans (hs: has_homsets C) {J J' : diag}
        (t : Π x : vertex g, dob J x -->  dob J' x) :
    isaprop (is_diag_nat_trans t).
  Proof.
    repeat (apply impred; intro).
    apply hs.
  Qed. 
  
  Definition diag_nat_trans J J' :=
    total2 (fun t : Π x : vertex g, dob J x -->  dob J' x => is_diag_nat_trans t).

  Definition mk_diag_nat_trans {J J' }
             (t : Π x : vertex g, dob J x --> dob J' x)
             (H : is_diag_nat_trans  t) :
  diag_nat_trans J J' := tpair _ t H.

  Lemma isaset_diag_nat_trans  (hs: has_homsets C) J J'
   : isaset (diag_nat_trans J J').
  Proof.
    apply (isofhleveltotal2 2).
    + apply impred; intro t; apply hs.
    + intro x; apply isasetaprop, isaprop_is_nat_trans, hs.
  Qed.

  Definition diag_nat_trans_data  {J J' : diag}
           (a:diag_nat_trans J J') := pr1 a.
  Coercion diag_nat_trans_data : diag_nat_trans >-> Funclass.

  Definition diag_nat_trans_ax {J J' : diag}
             (a:diag_nat_trans J J') := pr2 a.


  (* Actually diagrams g -> C is a category but we just focus on the notion of
 iso *)
  Definition are_inverse {J J':diag} (a :diag_nat_trans J J')
    (b: diag_nat_trans J' J):=
    ( Π v:vertex g, a v ;; b v = identity _)
      ×  Π v:vertex g, b v ;; a v = identity _ .


  
  
End diagramNatTrans.



(* a transfo nat between two diagrams induces a lift of cocones *)
Section liftCocone.

  Context {g:graph} {C:precategory} {J J' : diagram g C}.
  Context (m:diag_nat_trans J J') {c} (cc: cocone J' c).

  Definition lift_cocone : cocone J c.
    assert (h := coconeInCommutes cc).
    set (fin := (coconeIn cc)) in *.

    apply (mk_cocone(fun v => m v ;; fin v)).
        abstract(
    intros u v e;
    rewrite assoc, (diag_nat_trans_ax m), <- assoc, h; apply idpath).
  Defined.
End liftCocone.

Section isoCocone.

  Context {g:graph} {C:precategory} {J J' : diagram g C}.
  Context  {c} (cc: cocone J' c).

  Lemma is_exists_unique {A : UU} {B : A → UU} (H : ∃! a : A, B a) :
    B ( pr1 (iscontrpr1 H)).
  Proof.
    exact(pr2 (pr1 H)).
  Qed.

  Lemma iso_colimCocone (hs:has_homsets C) {a b} (hinv:are_inverse (J:=J) (J':=J') a b) :
    isColimCocone J' c cc -> isColimCocone J c (lift_cocone a cc).
  Proof.
    intros iscolim c' cc'.
    specialize (iscolim c' (lift_cocone b cc')).
    apply (unique_exists (pr1 (pr1 iscolim))).
    - intro v.
      cbn.
      etrans.
      rewrite <- assoc.
      apply cancel_precomposition.
      apply (is_exists_unique iscolim v).
      cbn.
      rewrite assoc,(pr1 hinv).
      apply id_left.
    - intros y.
      apply impred_isaprop.
      intros; apply hs.
    - intros y hy.
      apply (eq_exists_unique _ _ iscolim).
      intro v; specialize (hy v).
      cbn in hy; cbn.
      rewrite <- hy, assoc, assoc, (pr2 hinv), id_left.
      apply idpath.
  Qed.

    

End isoCocone.

(* used because as admit to signal that I don't want to wait for too long *)
Lemma toolong : forall A, A.
Admitted.                       

(*
  (* Exclusive lemma : the converse *)
Lemma pointwise_po_if_po (hpo :Pushouts D) :   isPushout _ _ _ _ Hcomm ->
                                               (Π x, isPushout _ _ _ _ (Hcommx x)).
Proof.
  intros T x.
  assert (pocd := (hpo _ _ _ (pr1 c x) (pr1 d x))).
  set (pocd2 := isPushout_Pushout pocd).
  use mk_isPushout; intros E h k Hhk.
  use unique_exists.
  - mkpair.
    + intro x; apply (g T E h k Hhk).
    + apply is_nat_trans_g.
  - abstract (split; apply (nat_trans_eq hsD); intro x;
              [ apply (PushoutArrow_PushoutIn1 (mk_Pushout (T x)))
              | apply (PushoutArrow_PushoutIn2 (mk_Pushout (T x))) ]).
  - abstract (intro; apply isapropdirprod; apply functor_category_has_homsets).
  - abstract (intros t [h1 h2]; destruct h as [h Hh];
              apply (nat_trans_eq hsD); intro x; apply PushoutArrowUnique;
              [ apply (nat_trans_eq_pointwise h1) | apply (nat_trans_eq_pointwise h2) ]).
Defined.
*)

(* if colimits are computed pointwise, then a transfo nat which is an epi is
 pointwise an epi*)
  Require Import UniMath.CategoryTheory.CocontFunctors.
Section PointwiseEpi.
  Context { C :precategory} {D:Precategory} .

  Definition functor_Precategory : Precategory :=
    (functor_precategory C D (homset_property D),,
                         functor_category_has_homsets _ _ _).

  Local Notation CD := functor_Precategory.
  Require Import UniMath.CategoryTheory.limits.graphs.colimits.
  Require Import UniMath.CategoryTheory.limits.graphs.pushouts.


  (* transfo nat between pushouts pw and pushout in D *)
  Section pushouts.
    Context {X Y Z :CD} {a:CD  ⟦ X, Y ⟧} {b:CD ⟦ X, Z⟧} (x:C).
    Local Notation poD := (pushout_diagram D (pr1 a x) (pr1 b x)).
    Local Notation po_pw := ((diagram_pointwise (homset_property D)
                                                (pushout_diagram CD a b) x) ).

    Definition poD_to_pw_data :  Π v : vertex _, dob poD v -->  dob po_pw v.
      use StandardFiniteSets.three_rec_dep;simpl; apply identity.
    Defined.

    Definition pw_to_poD_data : Π v : vertex _, dob po_pw v -->  dob poD v.
      use StandardFiniteSets.three_rec_dep;simpl; apply identity.
    Defined.

    Lemma is_nat_trans_poD_to_pw : is_diag_nat_trans poD_to_pw_data.
      use StandardFiniteSets.three_rec_dep;
        use StandardFiniteSets.three_rec_dep;
        try exact (Empty_set_rect _ );
      cbn;
        unfold idfun; simpl;
      now rewrite id_left, id_right.
    Qed.

    Lemma is_nat_trans_pw_to_poD : is_diag_nat_trans pw_to_poD_data.
    Proof.
      use StandardFiniteSets.three_rec_dep;
        use StandardFiniteSets.three_rec_dep;
        try exact (Empty_set_rect _ );
      cbn;
        unfold idfun; simpl;
      now rewrite id_left, id_right.
    Qed.      

    Definition pw_to_poD : diag_nat_trans po_pw poD :=
      mk_diag_nat_trans _ is_nat_trans_pw_to_poD.

    Definition poD_to_pw : diag_nat_trans poD po_pw :=
      mk_diag_nat_trans _ is_nat_trans_poD_to_pw.

    Lemma is_inv_pw_poD : are_inverse pw_to_poD poD_to_pw.
    Proof.
      split; use StandardFiniteSets.three_rec_dep; apply id_left.
    Qed.

  End pushouts.

(*  
  Definition colims_func (colimD : @Colims D) : @Colims CD.
    intros.
    red.
    intros g d.
    apply ColimFunctorCocone.
    intros a.
    apply colimD.
  Defined.
*)
  (* A colimit is a colimit pointwise *)
  Lemma pw_colim
        (g:graph) (J:diagram g CD)
        (colimD: Π a : C, ColimCocone
                 (diagram_pointwise (homset_property D) J a))
(F:CD) (R:cocone J F) :
    isColimCocone J F R ->
    Π c : C,
          isColimCocone (diagram_pointwise  (homset_property _)  J c) (pr1 F c)
                        (cocone_pointwise  (homset_property _)  J F R c).
  Proof.
    intros  isColim c.
    apply isColimFunctor_is_pointwise_Colim.
    intros b; apply colimD.
    assumption.
  Qed.

  Lemma cocone_pushout_pw {X Y Z :CD} {a:CD  ⟦ X, Y ⟧} {b:CD ⟦ X, Z⟧} {x c}
        (cc : cocone (pushout_diagram D (pr1 a x) (pr1 b x))  c) :
    cocone
      (diagram_pointwise (homset_property D)
                         (pushout_diagram CD a b) x) c.
  Proof.
    simple refine (mk_cocone _ _  ).
    -
    intro v.
    specialize (pr1 cc v).
    pattern v.
   
    use StandardFiniteSets.three_rec_dep;simpl; apply idfun.

    - 
     
    intros u v e;
     specialize (pr2 cc u v e);
     revert u v e;
     use StandardFiniteSets.three_rec_dep;  use StandardFiniteSets.three_rec_dep; 
        exact (Empty_set_rect _ ) || (exact (fun v h => h)).
  Defined.

  Lemma Colims_pw_epi (colimD : Pushouts D) (A B : CD) (a:CD⟦ A,B⟧)
        (epia:isEpi a) : Π (x:C), isEpi (pr1 a x).
  Proof.    
    intro  x; simpl.
    apply epi_to_pushout in epia.
    apply pushout_to_epi.
    simpl.
    apply equiv_isPushout1 in epia; [| apply homset_property].
    apply equiv_isPushout2; [ apply homset_property|].

    red in epia.    
    
    
    apply pw_colim with (c:=x) in epia ; cycle 1.
    {
      intro c.
      unfold Pushouts in colimD.
      specialize (colimD _ _ _ (pr1 a c) (pr1 a c)).
      assert (colimc := isColimCocone_from_ColimCocone colimD).
      assert (epia' := iso_colimCocone  _ (homset_property D) (is_inv_pw_poD _)
                                        colimc).      
      apply (mk_ColimCocone _ _ _(epia')).
    }

    intros c cc.
    specialize (epia c (cocone_pushout_pw cc)).
    apply (unique_exists (pr1 (iscontrpr1 epia))).

    - assert (hepi := pr2 (iscontrpr1 epia)); simpl in hepi.
      intro v.
      generalize v (hepi v).
      use StandardFiniteSets.three_rec_dep; intro h; apply h.
    - intros y.
      apply impred_isaprop.
      intros t.
      apply homset_property.
    - assert (hepi2 := eq_exists_unique _ _ epia); simpl in hepi2.
      intros y hv; specialize (hepi2 y).
      apply hepi2.
      intros v; specialize (hv v).
      revert v hv.
      use StandardFiniteSets.three_rec_dep;intro h; apply h.
  Qed.

End PointwiseEpi.

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

Demander à Benedikt si ce truc est déjà démontrer. En particulier, je voudrais montrer que tout
épi est en fait un setquotfun
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

  Lemma PushoutsHSET : Pushouts SET.
    red.
    intros .
    apply ColimsHSET_of_shape.
  Qed.
    
  Definition lift_epi_nt_data : Π (X:Cat), pr1 (pr1 B X) -> pr1 (pr1 C X).
    intros X.
    assert (h:= (lift_epi (A:=pr1 A X) (B:=pr1 B X) (C:=pr1 C X))).
    cbn in h.
    eapply h.
    apply comp_epi.
    apply epitosetsissurjection.
    apply (Colims_pw_epi (C:=Cat)(D:=SET)).
    exact PushoutsHSET.
    assumption.
  Qed.


End LiftEpiNatTrans.




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
      repeat split; red ; simpl; intros; simpl.
    -  etrans; eauto.
    - now symmetry.
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

  (* Foncteur candidat *)
  Definition R' := quot_functor (pr1 (pr1 R)) _ congr_equivc.
  Definition projR : (## R) ⟶ R':= proj_quot _ _ congr_equivc.

  (* R' est un pseudo objet initial au sens suivant :
     Quel que soit        g : R ---> S morphisme dans la catégorie des représentations de a
     il existe un unique  u : R'---> S tel que g = u o projR
C'est un pseudo objet car il reste à montrer que R' est bien dans la catégorie des représentations
de a et que u est un morphisme de modules.
   *)
  Section CandidatU.
    Context {S:BREP a} (m:R -->[identity _] S).

    Definition u : nat_trans (pr1 R') (## S).
      apply lift_epi.


  End CandidatU.


  Definition R'_η : (functor_identity C) ⟶ R' := η (## R) ;;; projR .

  Notation GODMENT a b := ((pre_whisker _ a) ;;; post_whisker b _) (only parsing).

  Definition relRR c : eqrel (pr1 (## R (## R c))) :=  nt_eqrel  (GODMENT projR projR)  c.

  Lemma R_μ_comp c : iscomprelrelfun (relRR c) (eqrel_equivc c) ( (μ ## R) c).
  Proof.
    intros c x y.
    simpl.
    unfold nt_rel.
    cbn.
    intros hxy.
    red

  Definition R'_μ : R'□R' ⟶ R'.

  Definition R'_Monad_data : Monad_data C := ((R' ,, ) ,, η R


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
