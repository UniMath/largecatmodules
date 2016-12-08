Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.Monads.
Require Import Largecat.modules.
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


Require Import Largecat.ardef.
Require Import Largecat.quotientfunctor.

(* Let f : A -> B be a function.
It induces an equivalence relation on A.
Reciproquement, any equivalence relation on A is yielded by such an equivalence

Question pour Benedikt : est ce que ce truc est déjà démontré quelque part dans lalib standard
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

(* Let F : C -> Set be a functor.
Any natural transformation m : F -> G yields a quotient functor obtained by
splitting m into epi/mono.

A corollary is that m induces a relation on each image object of F *)
(*
Section FunctorEquiv.
  Local Notation SET := hset_Precategory.
  Context { C:precategory} { F G:functor_data C SET}.
  Variable  (m:F ⟶  G) (c:C).

  Definition nt_rel x y := m c x = m c y.




  Lemma isaprop_nt_rel  x y : isaprop (nt_rel x y).
    intros;
    apply setproperty.
  Qed.





End FunctorEquiv.
*)


(* Preuve qu'on peut relever les épi dans la catégorie des endo foncteurs sur Set
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


End LiftEpi.

(*
J'aurais besoin de la réciproque de surjectionisepitosets

Demander à Benedikt : je n'ai pas trouvé la preuve dnas la lib
 *)
Section ReciproqueSurjectionIsEpiToSets.
  Local Notation SET := hset_Precategory.
  Context {A B:SET}.
  Variables        (p : Epi _ A B).

  Lemma epitosetsissurjection : issurjective (pr1 p).
  Proof.
    red.
    intros y.
    assert (hepi := pr2 p).
    red in hepi.
    simpl in hepi.
    apply hinhpr.
    red.
  Abort.



End ReciproqueSurjectionIsEpiToSets.

(* if colimits are computed pointwise, then a transfo nat which is an epi is pointwise an epi*)
Section PointwiseEpi.
  Context { C D:precategory}.
  Variable (D:subcategory [C,D]).
  Hypothesis (pw_colimits : les colimites de D se calculent pointwise )
             Lemma pw_epi (F G : D) (a:Epi _ F G) : Π x, isEpi ( a x).
  TODO

End PointwiseEpi.

(* Lifting transfo nat *)
Section PointwiseLift.

  Local Notation SET := hset_Precategory.
  Context {C:precategory} (F G: functor_data C SET).
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


End PointwiseLift.


(* définition du quotient nécessaire pour la preuve de préservation par épi de la représentabilité
des arités

1e définition par les HIT à la Coq HOTT

 Copied from Coq Hott HIT.Coeq
 *)
(* pour l'instant on l'ignore. *)

(*
  Module Export Coeq.



    Local Notation C := hset_Precategory.
    (* Context (C:Precategory). *)
    Local Notation PARITY := (arity_Precategory C).
    Local Notation BREP := (brep_disp C).

    Local Notation "## F" := (pr1 (pr1 (F:BREP _)))(at level 3).

    Private Inductive Quot {a b: PARITY} (F:PARITY ⟦ a, b ⟧) (R:BREP a) (c:ob C) : UU :=
    | quot : pr1 (## R c) → Quot F R c .

    Arguments quot [_ _] _ [_ _] _.





    Axiom isaset_quotient : forall {a b} (F:PARITY ⟦ a, b ⟧) (R:BREP a) c, isaset (Quot F R c).

    Definition equivc  {a b} (F:PARITY ⟦ a, b ⟧) {R:BREP a} {c:ob C} (x y:pr1 (## R c)) :=
                                  (Π (S:BREP b) ( f : R -->[F] S),
                                                   pr1 (pr1 f) c x = pr1 (pr1 f) c y).


    Axiom cp : forall {a b} (F:PARITY ⟦ a, b ⟧) (R:BREP a)  {c:ob C} {x y:pr1 (## R c) },
        equivc F  x y -> quot F  x = quot F  y.

    (* Local Notation Quotient := (Quot F R). *)
    (* Local Notation quotient := (quot F ). *)


    Definition Quotient_ind {a b} (F:PARITY ⟦ a, b ⟧) (R:BREP a) {c} (P : Quot F R c → Type)
               (coeq' : Π a, P (quot _ a))
               (cp' : Π x y (Rxy : equivc F x y), transportb P (cp F R Rxy) (coeq' y) = coeq' x)
      : Π w, P w
      := fun w => match w with quot _  a => fun _ => coeq' a end cp'.

    (* quel est l'axiome équivalent à celui-ci ??
    Axiom Quotient_ind_beta_cp
      : forall {c} (P : @Quotient c → Type)
          (coeq' : forall a, P (quotient a))
          (cp' : Π x y (Rxy : equivc x y), transportb P (cp Rxy) (coeq' y) = coeq' x)
          (cp' : ∀ b, (cp b) # (coeq' (f b)) = coeq' (g b))
          x y,
        apD (Quotient_ind P coeq' cp') (cp b) = cp' b.
*)

  End Coeq.

*)



(*
A morphism of arity F : a -> b induces a functor between representation Rep(b) -> Rep(a)

In this section we construct the left adjoint of this functor (which is defined whenever
F is an epimorphism)
 *)
Section leftadjoint.


  Local Notation C := hset_Precategory.
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
    intros c.
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

    Definition u_data :
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
