(**

- Custom notion of equality between diagrams (eq_diag) over the same graph

 Definition of a specific notion of equality (eq_diag) between
diagrams to circumvent the fact that axiom of functional extensionality
stops reduction with the standard equality.

- Various proofs about equals diagrams : they define the same limits/colimits.
This is used to switch between the pointwise definition of a diagram on vector
and the definition of the pointwise diagram.



Using functional extensionality, eq_diag is equivalent to equality.

The main interest is the proof that lims/colims are the same for two 
eq_diag diagrams.

Example in case the graph is an equalizer graph.

Let C,D be two categories. Let J be the following diagram
<<
 F --> G
   -->
>>

Let x be an object of C.
We have the following diagram J' :
<<

F x --> G x
    --> 

>>

However J' is not definitionally equal to diagram_pointwise J x.

The proof that it is eq_diag equal to J' allows to convert the colimit of one
diagram into another, and the colimits arrows are really computing, which
is not the case if one would abruptly use the proof of 'raw' equality between J'
and diagram_pointwise J x

 *)



  (*

Je veux expliquer ici pourquoi je pense qu'avec l'univalence
computationnelle je n'ai plus
besoin de mon égalité spécifique entre diagrammes eq_diag en prenant
 l'exemple du transport de cone pour un produit binaire

Soit g un graphe discret (sans arrête), qu'on identifie avec le type
de ses sommets.

Ici on prend l'exemple d'un graphe à 2 sommets A et B :
  g := A + B

Soit C une catégorie, qu'on identifie avec le type de ses objets.
On note C⟦X,Y⟧ le type des morphismes entre les objets X, Y de C

Le type des diagrammes de g vers C est le suivant : g -> C

Le type des cones sur un diagrame J est le suivant :
   cone J = Σ (c:C), Π x:g, C⟦c, J x⟧

Supposons que j'ai une égalité entre deux diagrammes : e : J = J'
Alors j'ai une fonction f : cone J -> cone J'
que je définis par f co := (pr1 co, fun x => transport _ e (pr2 co x))

'transport' est la fonction de transport.
Le premier argument est le type à transporter, le second l'égalité à utiliser,
et le troisième le terme à transporter.

Un type vaut mieux qu'un long discours :
transport : Π (X : UU) (P : X → UU) (x x' : X), x = x' → P x → P x'
(UU == Type)

Maintenant, Supposons que pour démontrer que J=J', j'ai utilisé l'axiome
d'égalité extensionnelle des fonctions : e := funextfun H
funextfun est l'axiome d'égalité extensionnelle et H est de type Π x, J x = J' x

En particulier, supposons que J A ≡ J' A et J B ≡ J' B convertiblement.
donc la preuve H consiste simplement à faire une disjonction de cas
sur le sommet
du graphe g (A ou B) et à appliquer eq_refl


Ce que je voudrais pour des raisons techniques et/ou pratiques,
c'est que  pr2 co A ≡ pr2 (f co) A et pr2 c B ≡ pr2 (f co) B convertiblement.

Bien sûr ce n'est pas le cas si l'univalence est un axiome.
En effet déplions un peu la chose pour le premier cas :

pr2 (f co) A ≡ transport (fun X => C⟦pr1 c, X⟧)
                              (funextfun H) (pr2 co A)

C'est clair que ça va pas calculer en coq normal. Voyons pourquoi cela
devrait se réduire vers pr2 co A dans le cas où l'univalence calcule
(cubicaltt il paraît).

Partons d'un exemple plus simple.

J'ai une preuve e que deux fonctions (J J' : A+B -> T)
 sont égales via égalité extensionnelle e= funextfun H,
via une simple disjonction de cas suivi de eq_refl.

J'ai un terme de type t : J A.
J'ai envie que transport (fun X => X A) (funextfun H) t ≡ t convertiblement

D'après le lemme d'UniMaths transportf_funextfun, j'anticipe que avec
l'univalence
qui calcule, on aurait (à vérifier si c'est vrai dans cubicaltt par exemple)
    transport (fun X => X A) (funextfun H) t ≡ transport (fun X => X)
(H A) t convertiblement

Mais qu'est ce que H A sinon eq_refl ? et donc
  transport (fun X => X) (H A) t ≡ t convertiblement

(Question à laquelle je n'ai pas réfléchi : est-ce qu'avec
l'univalence computationnnelle, ça calculerait si je définissais la
fonction directement par f co := transport _ e co ?

Oui,je pense, à condition d'ajouter la règle apparemment bénine que les
transports triviaux réduisent (ie si P x ne dépend pas de x en fait dans
transportf P _ _)

Y'a -til cette règle dans Cubicaltt ?



    *) 


Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.CategoryTheory.Epis.

Require Import UniMath.CategoryTheory.limits.EffectiveEpis.

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

Require Import UniMath.Ktheory.Utilities.


Set Automatic Introduction.


Lemma is_exists_unique {A : UU} {B : A → UU} (H : ∃! a : A, B a) :
  B ( pr1 (iscontrpr1 H)).
Proof.
  exact(pr2 (pr1 H)).
Qed.


Lemma transport_swap: Π {X Y : UU} (P : X -> Y → UU) {x x':X} {y  y' : Y}
                        (e : x = x') (e' : y = y') (p : P x y),
                  transportf (fun a => P _ a) e' (transportf (fun a => P a _) e p) =
                  transportf (fun a => P a _) e (transportf (fun a => P _ a) e' p) .
  intros.
  destruct e.
  destruct e'.
  apply idpath.
Qed.


(* stolen from TypeTheory/Display_Cats/Auxiliary.v *)
(** Very handy for reasoning with “dependent paths” — e.g. for algebra in displayed categories.  TODO: perhaps upstream to UniMath?

Note: similar to [transportf_pathsinv0_var], [transportf_pathsinv0'], but not quite a special case of them, or (as far as I can find) any other library lemma.
*)
Lemma transportf_transpose {X : UU} {P : X → UU}
  {x x' : X} (e : x = x') (y : P x) (y' : P x')
: transportb P e y' = y -> y' = transportf P e y.
Proof.
  intro H; destruct e; exact H.
Defined.


Definition eq_diag  {C : Precategory} {g : graph} (d d' : diagram g C) :=
  Σ (eq_v : Π v: vertex g, dob d v = dob d' v), Π (v v':vertex g) (f:edge v v'),
  transportf (fun obj => C⟦obj, dob d v'⟧)  (eq_v v) (dmor d f) =
  transportb (fun obj => C⟦_, obj⟧) (eq_v v') (dmor d' f).

Lemma eq_is_eq_diag {C : Precategory} {g : graph} (d d' : diagram g C)  :
  d = d' -> eq_diag d d'.
Proof.
  intro e.
  induction e.
  exists (fun x => idpath _).
  exact (fun x y z => idpath _).
Qed.

Lemma transportf2_comp  {X  : UU} (P : X -> X → UU) (x x'  : X)
      (ex : x = x')  (t:P x x) :
  transportf (fun y => P y y) ex t = transportf (fun y => P y x') ex
                                             (transportf (fun y => P x y) ex t).
Proof.
  now induction ex.
Qed.

Lemma eq_diag_is_eq {C : Precategory} {g : graph} (d d' : diagram g C) :
  eq_diag d d' -> d = d'.
Proof.
  intros [eqv autreq].
  use total2_paths.
  - apply funextfun.
    intro v.
    apply eqv.
  - rewrite (transportf2_comp
               (λ x y : vertex g → C, Π a b : vertex g, edge a b →
                                                        C ⟦ y a, x b ⟧)).  
    match goal with |- transportf ?Pf ?x1 (transportf ?Pf2 ?s1 ?s2 )  = _ =>
                    set (e := x1);
                      set (P := Pf);
                      set (P2 := Pf2);
                      set (tp2:=transportf P2 s1 s2);
                      set (trp := transportf P x1 tp2)
    end.
    change (trp = pr2 d').
    unfold trp.
    apply funextsec.
    intro v; apply funextsec; intro v'.    
    apply funextsec; intro ed.
    specialize (autreq v v' ed).
    rewrite  <- (pathsinv0inv0 (eqv v)) in autreq.
    symmetry in autreq.
    apply transportf_transpose in autreq.
    unfold dmor in autreq.
    rewrite autreq.
    rewrite pathsinv0inv0.
    etrans.
    symmetry.
    apply (  transport_map (P:=P) (Q:=_) (fun x tp => tp  v v' ed)).
    etrans.
    apply (transportf_funextfun (fun x => C⟦ pr1 d' v,x⟧)).
    apply maponpaths.
    etrans.
    symmetry.
    apply (  transport_map (P:=P2) (Q:=_) (fun x tp => tp  v v' ed)).
    apply (transportf_funextfun (fun x => C⟦ x,pr1 d v'⟧)).
Qed.

(* We don't want to use the equivalence with bare identity to show the 
symmetry because we want computation (Defined) *)
Lemma sym_eq_diag  {C : Precategory} {g : graph} (d d' : diagram g C) :
  eq_diag d d' -> eq_diag d' d.
Proof.
  intros eq_d.
  set (eq_d1 := pr1 eq_d).
  set (eq_d2 := pr2 eq_d).
  use tpair.
  intro v.    
  apply (! (eq_d1 v)).
  cbn.
  intros v v' f.
  specialize (eq_d2 v v' f).
  symmetry.
  unfold transportb.
  rewrite pathsinv0inv0.
  apply (transportf_transpose (P:=(λ obj : C, C ⟦ obj, dob d' v' ⟧))).
  assert (eq_d2':=transportf_transpose (P:=(precategory_morphisms (dob d' v)))
                                       _ _ _ (! eq_d2)).
  rewrite eq_d2'.
  unfold transportb; rewrite pathsinv0inv0.
  apply (transport_swap (fun a b => C⟦b,a⟧)).
Defined.

Lemma eq_diag_mkcocone  :
  Π {C : Precategory} {g : graph} {d : diagram g C}       
    (d' : diagram g C)
    (heq_d: eq_diag d d')
    {c : C} (cc:cocone d c),
  cocone d' c.
Proof.           
  clear.
  intros.
  destruct heq_d as [heq heq2].
  use mk_cocone.
  intro v.
  use (transportf (fun obj => C⟦obj,_⟧ ) (heq v)); simpl.
  apply (coconeIn cc).
  abstract(
      intros u v e; simpl;
      rewrite <- ( coconeInCommutes cc u v e);
      apply (pathscomp0 (b:=transportb (precategory_morphisms (dob d' u)) (heq v) (dmor d' e) ;; (coconeIn cc v)));
      [
        unfold transportb; (set (z:= ! heq v));
        rewrite <- (pathsinv0inv0 (heq v));
        symmetry;
        apply transport_compose|];

      etrans; [
        apply cancel_postcomposition;
        symmetry; apply heq2|];
      clear;
      now destruct (heq u)).
Defined.


(* The dual proof *)
Lemma eq_diag_mkcone  :
  Π {C : Precategory} {g : graph} {d : diagram g C}       
    (d' : diagram g C)
    (heq_d: eq_diag d d')
    {c : C} (cc:cone d c),
  cone d' c.
Proof.           
  clear.
  intros.
  set (heq := pr1 heq_d).
  set (heq2 := pr2 heq_d).
  use mk_cone.
  intro v.
  apply (transportf (fun obj => C⟦_,obj⟧ ) (heq v) (coneOut cc v)).
    abstract(
      intros u v e; simpl;      
      rewrite <- ( coneOutCommutes cc u v e);
      etrans;[
        apply transport_compose|];
      rewrite transport_target_postcompose;
      apply cancel_precomposition;
      apply transportf_transpose;
      etrans;[
        apply (transport_swap (fun a b => C⟦a,b⟧))|];
      etrans;[
        apply maponpaths;
        symmetry;
        apply heq2|];
      unfold heq;
      induction (pr1 heq_d u);
      apply idpath).
Defined.



Lemma eq_diag_islimcone:
  Π {C : Precategory} {g : graph} {d : diagram g C} 
    (d' : diagram g C)
    (eq_d : eq_diag d d')
    {c : C} {cc:cone d c}
    (islimcone : isLimCone _ _ cc) ,
  isLimCone _ _ (eq_diag_mkcone d' eq_d cc).
Proof.

  intros.
  set (eq_d1 := pr1 eq_d);
    set (eq_d2 := pr1 eq_d).
  set (eq_d' := sym_eq_diag _ _ eq_d).
  set (eq_d1' := pr1 eq_d').
  set (eq_d2' := pr2 eq_d').
    red.
  intros c' cc'.
  set (cc'2 := eq_diag_mkcone _ eq_d' cc').
  specialize (islimcone c' cc'2).
  apply (unique_exists (pr1 (pr1 islimcone))).
  - intro v.
    assert (islim := is_exists_unique islimcone v).
    cbn in islim.
    cbn.
    etrans.
    symmetry.
    apply transport_target_postcompose.
    etrans.
    apply maponpaths.
    apply islim.
    apply Utilities.transportfbinv.
  - intro y.
    apply impred_isaprop.
    intro t.
    apply homset_property.
  - intros y hy.
    apply (path_to_ctr _ _ islimcone).
    intro v; specialize (hy v).
    cbn.
    apply transportf_transpose.
    rewrite <- hy.
    etrans.
    unfold transportb.
    rewrite pathsinv0inv0.
    apply transport_target_postcompose.
    apply idpath.
Qed.

(** same proof : dual 
This proof could be deduced from the previous if there was a lemma 
that tells that colimits are limits in the dual category. Is there such one
Benedikt ?
*)
(* TODO refaire mieux en s'isnpirant de eq_diag_islimcone *)
Lemma eq_diag_iscolimcocone:
  Π {C : Precategory} {g : graph} {d : diagram g C} 
    (d' : diagram g C)
    (eq_d : eq_diag d d')
    {c : C} {cc:cocone d c}
    (islimcone : isColimCocone _ _ cc) ,
  isColimCocone _ _ (eq_diag_mkcocone d' eq_d cc).
Proof.
  intros.
  destruct eq_d as [eq_d1 eq_d2].
  set (eq_d := eq_d1,,eq_d2).
  set (eq_d'' := sym_eq_diag _ _ eq_d).
  set (eq_d1' := pr1 eq_d'').
  set (eq_d2' := pr2 eq_d'').
  set (eq_d'  := (eq_d1',,eq_d2'):eq_diag d' d).
  red.
  intros c' cc'.
  set (cc'2 := eq_diag_mkcocone _ eq_d' cc').
  specialize (islimcone c' cc'2).
  apply (unique_exists (pr1 (pr1 islimcone))).
  - intro v.
    assert (islim := is_exists_unique islimcone v).
    cbn in islim.
    cbn.
    etrans.
    rewrite <- (pathsinv0inv0 (eq_d1 v)).
    symmetry.
    apply transport_source_precompose.
    etrans.
    apply maponpaths.
    apply islim.
    cbn.
    now apply (Utilities.transportbfinv ( (λ x' : C, C ⟦ x', c' ⟧) )).
  - intro y.
    apply impred_isaprop.
    intro t.
    apply homset_property.
  - intros y hy.
    apply (path_to_ctr _ _ islimcone).
    intro v; specialize (hy v).
    revert hy.
    cbn.
    intro hy.
    apply (transportf_transpose (P:=(λ obj : C, C ⟦ obj, c' ⟧))).
    etrans.
    apply transport_source_precompose.      
    unfold transportb.
    rewrite pathsinv0inv0.
    apply hy.
Qed.




Definition eq_diag_liftcolimcocone
           {C : Precategory} {g : graph} {d : diagram g C} 
           (d' : diagram g C)
           (eq_d : eq_diag d d')
           (cc:ColimCocone d ) : ColimCocone d'
  := mk_ColimCocone _ _ _ (eq_diag_iscolimcocone _ eq_d
                                                 (isColimCocone_ColimCocone cc)).

Definition eq_diag_liftlimcone
           {C : Precategory} {g : graph} {d : diagram g C} 
           (d' : diagram g C)
           (eq_d : eq_diag d d')
           (cc:LimCone d ) : LimCone d'
  := mk_LimCone _ _ _ (eq_diag_islimcone _ eq_d
                                         (isLimCone_LimCone cc)).



