/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp

/-! # Content induction composition

The all-module comparison needed by `DeformedActionAssembly.md` §5 identifies
successive right-append induction with block induction. It is the existing
balanced induction composition isomorphism followed by the equality induced
by word associativity. Both directions are even, and naturality includes odd
module maps. Common-target content proofs are explicit. No crossing relation
on composites or triple coherence is asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u

private theorem appendFamily_map_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

private theorem appendFamily_add_heq {ι : Type*} (A : ι → Type*)
    [∀ i, Add (A i)] {i j : ι} (h : i = j)
    {a c : A i} {b d : A j} (hab : HEq a b) (hcd : HEq c d) :
    HEq (a + c) (b + d) := by
  cases h
  cases hab
  cases hcd
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem appendPair_assoc (v w σ τ : List I) :
    ((v ++ σ) ++ τ, (w ++ σ) ++ τ) = (v ++ (σ ++ τ), w ++ (σ ++ τ)) := by
  simp only [List.append_assoc]

/-- This is a statement about linear maps, not signed composition: no parity
restriction on the coefficient tensor is needed. -/
theorem rightContext_append_heq (σ τ v w : List I) (f : hom D Sc cutoff v w) :
    HEq (rightContext D Sc cutoff τ (v ++ σ) (w ++ σ)
      (rightContext D Sc cutoff σ v w f))
      (rightContext D Sc cutoff (σ ++ τ) v w f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    exact (heq_of_eq (((rightContext D Sc cutoff τ (v ++ σ) (w ++ σ)).comp
      (rightContext D Sc cutoff σ v w)).map_add f g)).trans
      ((appendFamily_add_heq (fun z : List I × List I => hom D Sc cutoff z.1 z.2)
        (appendPair_assoc v w σ τ) hf hg).trans
        (heq_of_eq ((rightContext D Sc cutoff (σ ++ τ) v w).map_add f g).symm))
  | tmul a f =>
    have hf : HEq ((f ▷ (pres D Sc).obj (ob D σ)) ▷ (pres D Sc).obj (ob D τ))
        (f ▷ (pres D Sc).obj (ob D (σ ++ τ))) :=
      (conj_eqToHom_iff_heq _ _
        (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
        (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc w σ τ))).1
        (whiskerRight_whiskerRight_list D Sc f σ τ)
    exact appendFamily_map_heq
      (A := fun z : List I × List I =>
        (pres D Sc).obj (ob D z.1) ⟶ (pres D Sc).obj (ob D z.2))
      (B := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
      (fun _ g => a ⊗ₜ[k] g) (appendPair_assoc v w σ τ) hf

variable (N : ℕ)

theorem truncatedRightContext_append_heq (σ τ v w : List I)
    (f : TruncatedOld D Sc cutoff N v w) :
    HEq (truncatedRightContext D Sc cutoff N τ (v ++ σ) (w ++ σ)
      (truncatedRightContext D Sc cutoff N σ v w f))
      (truncatedRightContext D Sc cutoff N (σ ++ τ) v w f) := by
  obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v w).mkQ_surjective f
  simp only [truncatedRightContext_mk]
  exact appendFamily_map_heq
    (A := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (B := fun z : List I × List I => TruncatedOld D Sc cutoff N z.1 z.2)
    (fun z => (truncatedIdeal D Sc cutoff N z.1 z.2).mkQ)
    (appendPair_assoc v w σ τ) (rightContext_append_heq D Sc cutoff σ τ v w f)

private theorem contentWord_ext {β : Multiset I}
    {v w : ContentCategory D Sc cutoff N β} (h : v.obj.word = w.obj.word) : v = w := by
  rcases v with ⟨⟨v⟩, hv⟩
  rcases w with ⟨⟨w⟩, hw⟩
  cases h
  rfl

/-- Independent target proofs are allowed: proof irrelevance identifies them. -/
theorem contentAppend_comp_eq (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentAppend D Sc cutoff N β σ ⋙
        contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h =
      contentAppendTo D Sc cutoff N β (σ ++ τ) γ h' := by
  apply Functor.hext
  · intro v
    exact contentWord_ext D Sc cutoff N (List.append_assoc v.obj.word σ τ)
  · intro v w f
    exact truncatedRightContext_append_heq D Sc cutoff N σ τ v.obj.word w.obj.word f

/-- Its components are equality morphisms, hence even, and retain every
coefficient parity. No artificial triviality/nontriviality assumptions. -/
def contentAppendAssocIso (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentAppend D Sc cutoff N β σ ⋙
        contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h ≅
      contentAppendTo D Sc cutoff N β (σ ++ τ) γ h' :=
  eqToIso (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')

/-- Equality of append functors induces equality of their balanced induction functors. -/
private theorem induction_eq {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K) :
    BalancedInduction.induction (k := k) J = BalancedInduction.induction K := by
  subst K
  rfl

private def inductionCompOfEq
    {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [L.Additive] [L.Linear k] [IsSuperfunctor k L] (e : J ⋙ K = L) :
    BalancedInduction.induction J ⋙ BalancedInduction.induction K ≅
      BalancedInduction.induction (k := k) L :=
  BalancedInduction.inductionComp J K ≪≫ eqToIso (induction_eq _ _ e)

/-- Parity of both directions of an ordinary natural comparison. -/
def EvenComparisonAt {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} (e : F ≅ G) (M : C) : Prop :=
  e.hom.app M ∈ parity (R := k) (F.obj M) (G.obj M) 0 ∧
  e.inv.app M ∈ parity (R := k) (G.obj M) (F.obj M) 0

private theorem inductionCompOfEq_mem
    {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (L : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [L.Additive] [L.Linear k] [IsSuperfunctor k L] (e : J ⋙ K = L)
    (M : Superfunctor k C (SVec k)) :
    EvenComparisonAt (k := k) (inductionCompOfEq J K L e) M := by
  subst L
  simpa only [EvenComparisonAt, inductionCompOfEq, eqToIso_refl, Iso.trans_refl] using
    And.intro (BalancedInduction.inductionComp_hom_mem J K M)
      (BalancedInduction.inductionComp_inv_mem J K M)

/-- Successive induction, with the final content transport made explicit. -/
def contentInductionComp (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentInduction D Sc cutoff N β σ ⋙
        contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h ≅
      contentInductionTo D Sc cutoff N β (σ ++ τ) γ h' :=
  inductionCompOfEq
    (contentAppend D Sc cutoff N β σ)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')

/-- Both directions are even on every module. -/
theorem contentInductionComp_mem (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentInductionComp D Sc cutoff N β σ τ γ h h') M :=
  inductionCompOfEq_mem
    (contentAppend D Sc cutoff N β σ)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h') M

/-- Naturality includes every supernatural module map, including odd maps. -/
theorem contentInductionComp_naturality (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {M L : ContentModules D Sc cutoff N β} (f : M ⟶ L) :
    (contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h).map
        ((contentInduction D Sc cutoff N β σ).map f) ≫
        (contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app L =
      (contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app M ≫
        (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h').map f :=
  (contentInductionComp D Sc cutoff N β σ τ γ h h').hom.naturality f

/-- The raising-functor pair comparison, with no common-content recasting of the composite. -/
def contentEPairComparison (β : Multiset I) (i j : I) :
    contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j ≅
      contentInductionTo D Sc cutoff N β [i,j]
        ((β + ([i] : Multiset I)) + ([j] : Multiset I))
        (by rw [add_assoc]; rfl) :=
  contentInductionComp D Sc cutoff N β [i] [j] _ rfl _

end OddMath.QuiverHecke.ELVOld
