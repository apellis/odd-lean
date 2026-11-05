import OddMath.QuiverHecke.HalfTurn.CoefficientGenerators
import Mathlib.LinearAlgebra.Quotient.Basic
import OddMath.QuiverHecke.HalfTurn.Homogeneous
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceQuotientComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePowerComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory

/-! # The half-turn in literal old cyclotomic Homs

SwappedVacuumCoordinates §§5–6. These maps land in the existing old category
with reversed words and twisted parameters. The exact source presentation
kernel, rather than an assumed evaluation kernel, gives bounded detection.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full half-turn followed by the actual old cyclotomic quotient. -/
def halfTurnOldHom (s t : List I) :
    (coefficientObj D Sc s ⟶ coefficientObj D Sc t) →ₗ[k]
      ((⟨t.reverse⟩ : ELVOld.OldCategory D (parameterTwist D Sc) cutoff) ⟶ ⟨s.reverse⟩) :=
  sourceToOldHom D (parameterTwist D Sc) cutoff t.reverse s.reverse ∘ₗ htCoef D Sc s t

/-- The actual reversed old Hom map has exactly the transformed boundary
kernel. No vacuum evaluation or action-faithfulness premise occurs. -/
theorem halfTurnOldHom_ker (s t : List I) :
    LinearMap.ker (halfTurnOldHom D Sc cutoff s t) =
      TransformedIdeal D Sc cutoff ∅ s t := by
  rw [halfTurnOldHom, LinearMap.ker_comp, sourceToOldHom_ker]
  exact comap_htCoef_elvRelationSpan D Sc cutoff s t

private theorem sourceToOldHom_comp {s t r : List I}
    (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t)
    (g : coefficientObj D Sc t ⟶ coefficientObj D Sc r) :
    sourceToOldHom D Sc cutoff s r (f ≫ g) =
      ELVOld.oldComp D Sc cutoff s t r
        (sourceToOldHom D Sc cutoff s t f) (sourceToOldHom D Sc cutoff t r g) := by
  change (ELVOld.ideal D Sc cutoff s r).mkQ (elvQuotientMap D Sc cutoff _ _ (f ≫ g)) = _
  rw [elvQuotientMap_comp]
  rfl

/-- Signed chronological composition in the literal old target Homs uses
full coefficient-plus-affine parity. -/
theorem halfTurnOldHom_comp {s t r : List I} {p q : ZMod 2}
    {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    {g : coefficientObj D Sc t ⟶ coefficientObj D Sc r}
    (hf : f ∈ Supercategory.parity (R := k) _ _ p)
    (hg : g ∈ Supercategory.parity (R := k) _ _ q) :
    halfTurnOldHom D Sc cutoff s r (f ≫ g) = SKM.zsign k (p * q) •
      (halfTurnOldHom D Sc cutoff t r g ≫ halfTurnOldHom D Sc cutoff s t f) := by
  change sourceToOldHom D (parameterTwist D Sc) cutoff r.reverse s.reverse
    (htCoef D Sc s r (f ≫ g)) = _
  rw [htCoef_comp D Sc hf hg, map_smul, sourceToOldHom_comp]
  rfl

/-- Bounded source windows survive in literal old cyclotomic Homs. -/
theorem halfTurnOldHom_injective_on_extendedAtMost {s t : List I} {d N : ℕ}
    (hN : ∀ i, N ≤ cutoff i) (hd : d + 2 * s.length.choose 2 < N) :
    Function.Injective (fun x : ExtendedAtMost D Sc s t d =>
      halfTurnOldHom D Sc cutoff s t x.val) := by
  intro x y hxy
  apply transformedIdeal_quotient_injective_on_extendedAtMost D Sc (T := ∅) hN
    (by intro a ha; cases ha) hd
  apply (Submodule.Quotient.eq _).mpr
  rw [← halfTurnOldHom_ker D Sc cutoff s t]
  change halfTurnOldHom D Sc cutoff s t (x.val - y.val) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

/-- Literal old Hom detection at the prescribed reservoir schedule. -/
theorem halfTurnOldHom_reservoir_injective (μ : X) (s t : List I) (d : ℕ) :
    Function.Injective (fun x : ExtendedAtMost D Sc s t d =>
      halfTurnOldHom D Sc (reservoirLevel D μ s d) s t x.val) :=
  halfTurnOldHom_injective_on_extendedAtMost D Sc _
    (vacuumCutoff_le_reservoirLevel D μ s d) (by simp [vacuumCutoff])

private theorem elementaryPowers_parity (L : I × ℕ → ℕ) :
    ∀ a ∈ (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j),
      ∃ p, CoefParity D p a := by
  rintro a ⟨j, rfl⟩
  refine ⟨0, ?_⟩
  have h : ∀ n : ℕ, CoefParity D 0 (SKM.SYM.e D k j.1 j.2 ^ n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using coefParity_one (k := k) D
    | succ n ih =>
      rw [pow_succ]
      have he : CoefParity D 0 (SKM.SYM.e D k j.1 j.2) := coefParity_e D j.1 j.2
      have hh : CoefParity D (0 + 0) (SKM.SYM.e D k j.1 j.2 ^ n * SKM.SYM.e D k j.1 j.2) :=
        CoefParity.mul D ih he
      exact hh
  exact h (L j)

/-- The complete actual first-boundary plus literal elementary-power preimage
under U is the prescribed transformed ideal. It retains the original power
exponents and does not replace them by a weighted ideal. -/
theorem halfTurn_oldElementaryPowers_preimage (L : I × ℕ → ℕ) (s t : List I) :
    (ELVOld.ideal D (parameterTwist D Sc) cutoff t.reverse s.reverse ⊔
        ELVOld.elementaryPowerHomSpan D (parameterTwist D Sc) cutoff L t.reverse s.reverse).comap
      (elvQuotientMap D (parameterTwist D Sc) cutoff (coefficientObj D (parameterTwist D Sc) t.reverse)
        (coefficientObj D (parameterTwist D Sc) s.reverse) ∘ₗ htCoef D Sc s t) =
      TransformedIdeal D Sc cutoff
        (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) s t := by
  rw [Submodule.comap_comp, ELVOld.comap_oldIdeal_sup_elementaryPowers]
  exact comap_htCoef_elvRelationSpan_sup D Sc cutoff _ (elementaryPowers_parity D L) s t

end OddMath.QuiverHecke
