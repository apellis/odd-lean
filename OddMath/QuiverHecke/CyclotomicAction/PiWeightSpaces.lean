/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierFamily
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerContent
import OddMath.SKM.RouquierPiSCat
import StringDiagrams.Super.PiTwo

/-!
# Π-structures on the cyclotomic weight spaces

The weight spaces of the cyclotomic factor family are products of full subcategories of module
supercategories `A-SMod-k`, which are Π-supercategories (Brundan–Ellis, *Monoidal
supercategories*, arXiv:1603.05928v3, Example 1.8). Content support is cut out by an even
idempotent, so it is preserved by the parity shift `Π`
(`heightContentSupported_piObj`); full subcategories closed under `Π` and products of
Π-supercategories are Π-supercategories (`fullPiSupercategory`, `productPiSupercategory`).
Hence every weight space is a Π-supercategory (`globalWeightSpacePi`), and the factor family
`globalRouquierFamily` is a super Rouquier family in `Π-𝔖ℭ𝔞𝔱` (`globalPiRouquierFamily`), where
the morphism supercategories are Π-supercategories, as the swapped Hom construction requires.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v w t

section Full
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] [Supercategory k C] (P : ObjectProperty C)

/-- `Π` on a full subcategory closed under `Π`, with the same `ζ`. -/
@[instance_reducible]
def fullPiSupercategory [PiSupercategory k C]
    (hP : ∀ M, P M → P ((PiSupercategory.pi (R := k)).obj M)) :
    PiSupercategory k P.FullSubcategory :=
  PiSupercategory.ofIso (fun M => ⟨(PiSupercategory.pi (R := k)).obj M.obj, hP _ M.property⟩)
    (fun M =>
      { hom := ⟨(PiSupercategory.ζ (R := k) M.obj).hom⟩
        inv := ⟨(PiSupercategory.ζ (R := k) M.obj).inv⟩
        hom_inv_id := InducedCategory.hom_ext (PiSupercategory.ζ (R := k) M.obj).hom_inv_id
        inv_hom_id := InducedCategory.hom_ext (PiSupercategory.ζ (R := k) M.obj).inv_hom_id })
    (fun M => PiSupercategory.ζ_hom_mem (R := k) M.obj)

end Full

section Product
variable {k : Type u} [CommRing k] {A : Type t}
  (C : A → Type v) [∀ a, Category.{w} (C a)] [∀ a, Preadditive (C a)]
  [∀ a, Linear k (C a)] [∀ a, Supercategory k (C a)]

/-- `Π` on a product of Π-supercategories, componentwise. -/
@[instance_reducible]
def productPiSupercategory [∀ a, PiSupercategory k (C a)] : PiSupercategory k (∀ a, C a) :=
  PiSupercategory.ofIso (fun M a => (PiSupercategory.pi (R := k)).obj (M a))
    (fun M =>
      { hom := fun a => (PiSupercategory.ζ (R := k) (M a)).hom
        inv := fun a => (PiSupercategory.ζ (R := k) (M a)).inv
        hom_inv_id := funext fun a => (PiSupercategory.ζ (R := k) (M a)).hom_inv_id
        inv_hom_id := funext fun a => (PiSupercategory.ζ (R := k) (M a)).inv_hom_id })
    (fun M a => PiSupercategory.ζ_hom_mem (R := k) (M a))

end Product

section Bimodule
variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A] {B : Type w} [Ring B]
  [Algebra k B] {𝒜 : ZMod 2 → Submodule k A} {ℬ : ZMod 2 → Submodule k B} [GradedAlgebra 𝒜]

/-- An even element acts on `Π V` as on `V`. -/
theorem piObj_lact_apply_of_even (V : SuperBimodule 𝒜 ℬ) {e : A} (he : e ∈ 𝒜 0)
    (m : V.toSVec) : (SuperBimodule.piObj V).lact e m = V.lact e m := by
  rw [SuperBimodule.piObj_lact_of_mem V he]
  change (sign k 0 • V.lact e) m = _
  rw [sign_zero, one_smul]

end Bimodule

section Weight
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- Content support is preserved by the parity shift: the content idempotent is even. -/
theorem heightContentSupported_piObj (n : ℕ) (β : Multiset I) (M : HeightModules D Sc a ha n)
    (hM : heightContentSupported D Sc a ha n β M) :
    heightContentSupported D Sc a ha n β ((PiSupercategory.pi (R := k)).obj M) := by
  cases n with
  | zero => exact hM
  | succ n =>
    intro m
    exact (piObj_lact_apply_of_even M (cyclotomicContentIdempotent_parity D Sc a ha n β) m).trans
      (hM m)

/-- Each content supercategory is a Π-supercategory. -/
@[instance_reducible]
def globalContentPi (β : Multiset I) : PiSupercategory k (GlobalContentModules D Sc a ha β) :=
  fullPiSupercategory _ fun M hM => heightContentSupported_piObj D Sc a ha β.card β M hM

variable (Λ x : X)

/-- Each weight space is a Π-supercategory, componentwise. -/
@[instance_reducible]
def globalWeightSpacePi : PiSupercategory k (globalWeightSpace D Sc a ha Λ x) :=
  letI := fun β : WeightBlocks D Λ x => globalContentPi D Sc a ha β.1
  productPiSupercategory _

end Weight

section Family
variable {I k : Type u} {X : Type u} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (Λ : X)

/-- **The cyclotomic factor family in `Π-𝔖ℭ𝔞𝔱`**, relative to local inversion: the family
`globalRouquierFamily` with the Π-structures `globalWeightSpacePi` on its weight spaces. -/
def globalPiRouquierFamily
    (L : ∀ (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂),
      GlobalLocalInversion D Sc a ha Λ i h₁ h₂) :
    SKM.RouquierFamily (k := k) (B := PiSCat.{u, u, u + 1} k) D :=
  (globalRouquierFamily D Sc a ha Λ L).toPiSCat fun x => globalWeightSpacePi D Sc a ha Λ x

end Family

end OddMath.QuiverHecke.CyclotomicAction
