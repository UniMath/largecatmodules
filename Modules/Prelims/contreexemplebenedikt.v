Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.


Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.binproducts.
Require Import Modules.Prelims.eqdiag.

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


Set Automatic Introduction.

(* Mise en pratique de la description précédente *)
Section ContreExempleBenedikt.


    Variables (C D : Precategory) (A B: functor C D) (x:C).
    Let CD := (functor_Precategory C D).

    Definition diag1 := diagram_pointwise (homset_property _) (binproduct_diagram CD A B) x.
    Definition diag2 := binproduct_diagram _ (A x) (B x).

    
    Lemma eq1 : diag1 = diag2.
    Proof.
      use total2_paths.
      - apply funextfun.
        intro y.
        now destruct y.
      - apply funextsec.
        intros v.
        apply funextsec.
        intro v'.
        apply funextsec.
        intro h.
        now apply (Empty_set_rect ).
    Defined.

    Lemma eq2 : eq_diag diag1 diag2.
    Proof.
      use tpair.
      - now induction v.
      - cbn.
        intros ??.
        apply Empty_set_rect.
    Defined.
        

    Definition transport_eq {C':precategory} {g:graph} {J J':diagram g C'} (e:J=J') c:
      cone J c -> cone J' c.
    Proof.
      intro hcone.
      use tpair.
      -
        intro v.
        induction e.
        apply (pr1 hcone).
      - abstract (induction e;        apply (pr2 hcone)).
    Defined.

    
    Variables (c:D) (c1 : cone diag1 c).

    Definition c2_impossible : cone diag2 c := transport_eq eq1 _ c1.
    Definition c2_facile : cone diag2 c := eq_diag_mkcone _ eq2  c1.

    Lemma facile : coneOut c2_facile true = coneOut c1 true.
      reflexivity.
    Qed.

    Lemma impossible : coneOut c2_impossible true = coneOut c1 true.
      (*TODO vérifier que c'est bien l'égalité extensionnelle qui bloque *)
      cbn.
      reflexivity.
    Qed.

  End ContreExempleBenedikt.
