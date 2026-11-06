import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierData

/-! # The exact quadratic fields of the bundled OLD probe generator data

Brundan–Ellis (1.7): disconnected and connected equations in the literal
RouquierMulticolour quadZero/quadNe format. The bundled crossing is retained
and its distinct branch is identified with the proved positive crossing.
No multicolour action record or unproved presentation field is constructed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "T" => probeOldRouquierData D Sc' m Λ

/-- The disconnected quadratic field for the actual bundled probe generators. -/
theorem probeOldRouquierData_quadZero (hij : i ≠ j) (hd : D.d i j = 0) :
    (T).cross i j h₁ h₂ h₃ h₄ ≫ (T).cross j i h₃ h₄ h₁ h₂ = (Sc.t i j : k) • 𝟙 _ := by
  change probeOldActionCross D Sc' m Λ i j h₁ h₂ h₃ h₄ ≫
    probeOldActionCross D Sc' m Λ j i h₃ h₄ h₁ h₂ = _
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij,
    probeOldActionCross_distinct D Sc' m Λ j i hij.symm,
    probeOldActionDistinctCross_quadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij]
  simp only [orderedPairOperatorPolynomial, (D.d_eq_zero_iff i j).mp hd, ite_true]
  rw [Sc.t_symm_of_d_eq_zero j i ((D.d_eq_zero_iff i j).mp hd)]
  rfl

/-- The connected quadratic field, with the exact ordered whiskered powers and original Sc. -/
theorem probeOldRouquierData_quadNe (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    (T).cross i j h₁ h₂ h₃ h₄ ≫ (T).cross j i h₃ h₄ h₁ h₂ =
      (Sc.t i j : k) • ((T).E j h₁ ◁ SKM.rouquierPower ((T).dot i h₂) (D.dn i j)) +
      (Sc.t j i : k) • (SKM.rouquierPower ((T).dot j h₁) (D.dn j i) ▷ (T).E i h₂) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • (SKM.rouquierPower ((T).dot j h₁) q ▷ (T).E i h₂ ≫
          (T).E j h₁ ◁ SKM.rouquierPower ((T).dot i h₂) p) := by
  dsimp only [probeOldRouquierData]
  change probeOldActionCross D Sc' m Λ i j h₁ h₂ h₃ h₄ ≫
    probeOldActionCross D Sc' m Λ j i h₃ h₄ h₁ h₂ = _
  rw [probeOldActionCross_distinct D Sc' m Λ i j hij,
    probeOldActionCross_distinct D Sc' m Λ j i hij.symm,
    probeOldActionDistinctCross_quadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij]
  have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).mpr h)
  have hL (n : ℕ) := SKM.whiskerLeft_rouquierPower (k := k)
    (B := PiSCat.{u,u,u + 1} k) (probeOldE D Sc' m j Λ h₁) (probeOldActionDot D Sc' m i Λ h₂) n
  have hR (n : ℕ) := SKM.whiskerRight_rouquierPower (k := k)
    (B := PiSCat.{u,u,u + 1} k) (probeOldActionDot D Sc' m j Λ h₁) (probeOldE D Sc' m i Λ h₂) n
  simp only [orderedPairOperatorPolynomial, hd', ite_false]
  simp_rw [hL, hR]
  simp only [End.mul_def]
  rw [Finset.sum_comm]
  simp only [Sc.s_symm j i]
  abel
end OddMath.QuiverHecke
