(* Definition of category of representations of a signature.
Not using displayed categories par flemme de définir les morphismes de signatures

 *)
(*

A signature is just a family of arities.
In the end, we would like to prove that any presentable signature is representable.
That is: let (O, (α_o, Θ^(n))_o) be a presentable signature (α_o is presentable
in the old sense and n is a natural number). Then there is an initial representation.

The plan is:
1) show that the category of representation of this signature
  is equivalent to the category of representation of the following raw signature
  (O, (α_o × Θ^n,Θ))
2) show that the category of representations of a signature (O, (β_o, Θ)) is
  equivalent to the category of representation of ∐ β_o
3) show that the the epis |Σ_o| -> β_o gather into an epi ∐ |Σ_o| → ∐ β_o
4) use the representability result for presentable half-arities.


Step 2) implies show that the category of half-arities have
arbitrary coproducts

This looks like quite a load of work. I wonder if it is really needed to formalize
all these steps, or just the first one, even for a signature with a single arity.
What do you think ?

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.LModules.

Require Import Modules.Signatures.aritiesalt.
Require Import Modules.Signatures.FullSignatures.

Definition signature C := ∑ (O : hSet), O -> FullArity C.

Definition base_of_sig {C} (S : signature C) : hSet := pr1 S.
Local Notation O := base_of_sig.

Definition ar_of_sig {C} {S : signature C} : O S -> FullArity C := pr2 S.
Local Notation α := ar_of_sig.

(** A representation of a signature is a representation of each of its component *)
Definition rep_sig {C} (S : signature C) :=
  ∑ R : Monad C, ∏ (o : O S), LModule_Mor R (dom (α o) R) (codom (α o) R).

Coercion Monad_from_rep_sig {C} {S : signature C} (X : rep_sig S) : Monad C := pr1 X.

Definition rep_sig_τ {C} {S : signature C} {X : rep_sig S} : ∏ (o : O S), _ := pr2 X.

Definition rep_ar_from_sig {C} {S : signature C} (X : rep_sig S) (o : O S) :
  rep_ar _ (α o) := (Monad_from_rep_sig X) ,, rep_sig_τ o.

(* Definition of a morphism of representations of a signature, using the existing
definitino about arities *)
Definition rep_a_sig_mor {C} {S : signature C } (M N : rep_sig S) :=
  ∑ g:Monad_Mor M N, ∏ (o : O S) , rep_ar_mor_law C (rep_ar_from_sig M o)
                                                  (rep_ar_from_sig N o) (identity _) g.

Coercion monad_morphism_from_rep_a_sig_mor {C} {S : signature C } {M N : rep_sig S}
         (X : rep_a_sig_mor M N) : Monad_Mor M N := pr1 X.

Definition rep_a_sig_mor_ax  {C} {S : signature C } {M N : rep_sig S}
           (X : rep_a_sig_mor M N) := pr2 X.

Definition rep_ar_mor_from_sig {C} {S : signature C } {M N : rep_sig S}
         (X : rep_a_sig_mor M N) (o : O S) : rep_ar_mor_mor C (rep_ar_from_sig M o)
                                                            (rep_ar_from_sig N o)
                                                            (identity _) :=
   
  (X : Monad_Mor _ _),, rep_a_sig_mor_ax X o.


Lemma isaset_rep_a_sig_mor {C} {S : signature C } (M : rep_sig S) (N : rep_sig S)  :
  isaset (rep_a_sig_mor  M N ).
Proof.
  intros.
  apply isaset_total2 .
  - apply has_homsets_Monad.
  - intros.
    apply isasetaprop.
    apply impred_isaprop.
    intros ?.
    apply isaprop_rep_ar_mor_law.
Qed.

Lemma rep_sig_mor_mor_equiv {C} (S : signature C) (A B:rep_sig S)
       (f g :rep_a_sig_mor A B) : 
  (∏ c, ((f : Monad_Mor _ _):nat_trans _ _) c = (g : Monad_Mor _ _) c) -> f = g.
Proof.
  intros.
  use (invmap (subtypeInjectivity _ _ _ _  )). 
  - intros ?.
    apply impred_isaprop.
    intros ?.
    apply isaprop_rep_ar_mor_law.
  - use (invmap (Monad_Mor_equiv _ _  _  )).  
     +  apply homset_property.
     +  apply nat_trans_eq.
        apply homset_property.
        assumption.
Qed.

Definition rep_sig_ob_mor {C} (S : signature C) : precategory_ob_mor :=
  precategory_ob_mor_pair (rep_sig S) (rep_a_sig_mor (S := S)).

Open Scope cat.

Definition rep_sig_id  {C} {S : signature C}  (R : rep_sig S) :
  rep_a_sig_mor R R.
Proof.
  exists (Monad_identity _).
  intro o.
  apply rep_id_law.
Defined.

Lemma rep_sig_comp_law  {C} {S : signature C}  {X Y Z : rep_sig S}
           (f : rep_a_sig_mor X Y) (g : rep_a_sig_mor Y Z) :
  ∏ o : O S, rep_ar_mor_law C (rep_ar_from_sig X o) (rep_ar_from_sig Z o)
                            (identity (α o)) (compose (C:=category_Monad C) (f : Monad_Mor _ _) (g : Monad_Mor _ _)).
Proof.
  intro o.
  assert (h := rep_comp_law _ _ _ _ (identity (α o)) (identity (α o))
                            (rep_ar_from_sig X o)
                            (rep_ar_from_sig Y o)
                            (rep_ar_from_sig Z o)
                            (rep_ar_mor_from_sig f o)
                            (rep_ar_mor_from_sig g o)
         ).
  rewrite id_left in h.
  exact h.
Qed.

  
Definition rep_sig_comp  {C} {S : signature C}  {X Y Z : rep_sig S}
           (f : rep_a_sig_mor X Y) (g : rep_a_sig_mor Y Z) :
  rep_a_sig_mor X Z :=
  (compose (C:=category_Monad C) (f : Monad_Mor _ _) (g : Monad_Mor _ _))
    ,, ( rep_sig_comp_law f g).

Definition rep_sig_precat_data {C} (S: signature C) : precategory_data :=
  precategory_data_pair (rep_sig_ob_mor S) rep_sig_id (λ a b c : rep_sig_ob_mor S, rep_sig_comp).

Lemma rep_sig_is_precat {C} (S : signature C)  : is_precategory
                                                   (rep_sig_precat_data S).
Proof.
  use make_is_precategory_one_assoc.
  - intros a b f.
(*  We don't need the pointwise version actually but who cares *)
    apply rep_sig_mor_mor_equiv.
    intro c.
    apply id_left.
  - intros a b f.
    apply rep_sig_mor_mor_equiv.
    intro c.
    apply id_right.
  - intros.
    apply rep_sig_mor_mor_equiv.
    intros ?.
    apply assoc.
Qed.

Definition precategory_rep_sig {C} (S : signature C) :=
  make_precategory _ (rep_sig_is_precat S).

