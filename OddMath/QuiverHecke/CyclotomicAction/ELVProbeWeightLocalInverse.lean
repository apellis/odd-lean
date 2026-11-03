import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightSupportedInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightInverseProducts
import OddMath.SKM.AugmentedInverseNaturality

/-! # The prescribed OLD probe inverses on entire weight fibres

Brundan–Ellis (1.13)–(1.14): occupied and missing coordinate inverses
assemble on every output block. The finite window is the categorical
height throughout the weight fibre. The resulting inverse is natural
in the whole input weight module, with all entries retained.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
section Recovery
universe u₀ v₀ w₀
variable {k : Type w₀} {C A : Type u₀} [CommRing k]
  [Category.{v₀} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{v₀} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A} {p : ZMod 2} {q : ℕ → ZMod 2} {m : ℕ}

private theorem total_supernatural (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => f.total X) := by
  simpa only [OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf] using f.isSupernatural p

private theorem recover_component (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (f.isSupernatural p).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact (OddMath.HomogeneousSuperfunctorIso.homogeneous_total (f.isSupernatural p) X).trans
    (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf X).symm

private theorem recover_total (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (total_supernatural f hf).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact OddMath.HomogeneousSuperfunctorIso.homogeneous_total (total_supernatural f hf) X

private def exactFromFamily (f : G ⟶ F) (g : ℕ → (H ⟶ F))
    (hf : f ∈ parity (R := k) G F p) (hg : ∀ n, g n ∈ parity (R := k) H F (q n))
    (J : ∀ X, SKM.SuperSumInvFrom (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvFrom (k := k) f g p q m := by
  have K := SKM.SuperSumInvFrom.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K

private def exactToFamily (f : F ⟶ G) (g : ℕ → (F ⟶ H))
    (hf : f ∈ parity (R := k) F G p) (hg : ∀ n, g n ∈ parity (R := k) F H (q n))
    (J : ∀ X, SKM.SuperSumInvTo (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvTo (k := k) f g p q m := by
  have K := SKM.SuperSumInvTo.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K
end Recovery

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "F₁" => probeOldF D Sc m i Λ h₁
local notation "F₂" => probeOldF D Sc m i Λ h₂
local notation "φ" => SKM.rouquierMate (probeOldActionAdjunction D Sc m i Λ h₁)
  (probeOldActionAdjunction D Sc m i Λ h₂) (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
local notation "UnitField" n => SKM.SuperAdjunction.unit (probeOldActionAdjunction D Sc m i Λ h₂) ≫
  SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ F₂
local notation "CapField" n => F₁ ◁ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₁) n ≫
  SKM.SuperAdjunction.counit (probeOldActionAdjunction D Sc m i Λ h₁)

/-- All occupied and missing coordinates supply the same unit inverse window. -/
theorem probeOldWeightLocalUnitInverse_nonempty
    (M : ProbeOldWeightProduct D Sc m Λ x₁)
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M)
      (fun n => (UnitField n).total M) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (UnitField n).total M δ) (D.parity i)
        (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightSupportedUnitInverse_nonempty D Sc m i Λ h₁ h₂ β hcutoff hh M
    · exact probeOldWeightAbsentUnitInverse_nonempty D Sc m i Λ h₁ h₂ δ hcutoff hδ M
  exact ⟨SKM.SuperSumInvFrom.pi (fun δ => Classical.choice (h δ))⟩

/-- The cap inverse also includes the missing zero-height coordinates. -/
theorem probeOldWeightLocalCapInverse_nonempty
    (M : ProbeOldWeightProduct D Sc m Λ x₁)
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M)
      (fun n => (CapField n).total M) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (CapField n).total M δ) (D.parity i)
        (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightSupportedCapInverse_nonempty D Sc m i Λ h₁ h₂ β hcutoff hh M
    · exact probeOldWeightAbsentCapInverse_nonempty D Sc m i Λ h₁ h₂ δ hcutoff hδ hh M
  exact ⟨SKM.SuperSumInvTo.pi (fun δ => Classical.choice (h δ))⟩

theorem probeOldWeightUnitPower_mem (n : ℕ) :
    (UnitField n) ∈ parity (R := k) _ _ ((n : ZMod 2) * D.parity i) := by
  have hd := SKM.rouquierPower_mem (probeOldActionDot_mem D Sc m i Λ h₂) n
  simpa only [zero_add] using
    comp_mem (probeOldActionAdjunction D Sc m i Λ h₂).unit_mem
      (TwoSupercategory.whiskerRight_mem F₂ hd)

theorem probeOldWeightCapPower_mem (n : ℕ) :
    (CapField n) ∈ parity (R := k) _ _ ((n : ZMod 2) * D.parity i) := by
  have hd := SKM.rouquierPower_mem (probeOldActionDot_mem D Sc m i Λ h₁) n
  simpa only [add_zero] using comp_mem (TwoSupercategory.whiskerLeft_mem F₁ hd)
    (probeOldActionAdjunction D Sc m i Λ h₁).counit_mem

/-- The whole natural unit inverse uses the literal chosen forward fields. -/
theorem probeOldWeightLocalUnitFamily_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) (φ) (fun n => UnitField n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) :=
  ⟨exactFromFamily (φ) (fun n => UnitField n)
    (probeOldWeightRouquierMate_mem D Sc m i Λ h₁ h₂)
    (probeOldWeightUnitPower_mem D Sc m i Λ h₂)
    (fun M => Classical.choice
      (probeOldWeightLocalUnitInverse_nonempty D Sc m i Λ h₁ h₂ M hcutoff hh))⟩

/-- The whole natural cap inverse uses the literal chosen forward fields. -/
theorem probeOldWeightLocalCapFamily_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) (φ) (fun n => CapField n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) :=
  ⟨exactToFamily (φ) (fun n => CapField n)
    (probeOldWeightRouquierMate_mem D Sc m i Λ h₁ h₂)
    (probeOldWeightCapPower_mem D Sc m i Λ h₁)
    (fun M => Classical.choice
      (probeOldWeightLocalCapInverse_nonempty D Sc m i Λ h₁ h₂ M hcutoff hh))⟩

end OddMath.QuiverHecke
