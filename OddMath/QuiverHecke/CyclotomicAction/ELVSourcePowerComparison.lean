import OddMath.QuiverHecke.CyclotomicAction.ELVSourceQuotientComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerSandwich
import OddMath.QuiverHecke.HalfTurn.CoefficientGenerators

/-! # Literal coefficient generators in the actual old presentation kernel

SwappedVacuumCoordinates §§5–6 and the literal power ideal of
SwappedNondegeneracy §2. This compares two-sided coefficient spans inside
existing full ELV Hom modules. The first-boundary ideal remains the literal
old ideal, and powers are the actual elementary coefficient powers.
-/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The actual full-coefficient two-sided span of specified scalar generators
in old coefficient Homs, before the strand cyclotomic ideal is imposed. -/
def coefficientGeneratorHomSpan
    (S : Set (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) (s t : List I) :
    Submodule k (hom D Sc cutoff s t) :=
  Submodule.span k {f | ∃ v : List I, v.length = s.length ∧ ∃ a ∈ S,
    ∃ x : hom D Sc cutoff s v, ∃ y : hom D Sc cutoff v t,
      x ≫ (a ⊗ₜ[k] (𝟙 ((pres D Sc).obj (ob D v))) : hom D Sc cutoff v v) ≫ y = f}

/-- The actual coefficient-generator span is the image of its full source
span. Both context multipliers are lifted through the surjective quotient. -/
theorem map_coefficientGeneratorSpan (T : Set (SKM.SYM D k)) (s t : List I) :
    (CoefficientGeneratorSpan D Sc T s t).map
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      coefficientGeneratorHomSpan D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff '' T) s t := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, a, ha, x, y, rfl⟩
    change elvQuotientMap D Sc cutoff _ _
      (x ≫ sourceCoefficientHom D Sc a (𝟙 _) ≫ y) ∈
        coefficientGeneratorHomSpan D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff '' T) s t
    rw [elvQuotientMap_comp, elvQuotientMap_comp, elvQuotientMap_source]
    exact Submodule.subset_span ⟨v, hv, SKM.SYM.elvCoefficientQuotient D cutoff a,
      ⟨a, ha, rfl⟩, _, _, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, a, ⟨a', ha', rfl⟩, x, y, rfl⟩
    obtain ⟨x', hx⟩ := elvQuotientMap_surjective D Sc cutoff s v x
    obtain ⟨y', hy⟩ := elvQuotientMap_surjective D Sc cutoff v t y
    refine ⟨x' ≫ sourceCoefficientHom D Sc a' (𝟙 _) ≫ y',
      Submodule.subset_span ⟨v, hv, a', ha', x', y', rfl⟩, ?_⟩
    rw [elvQuotientMap_comp, elvQuotientMap_comp, elvQuotientMap_source, hx, hy]

/-- The full old ideal and the specified scalar ideal together have precisely
the full source presentation plus the same coefficient generators as preimage. -/
theorem comap_oldIdeal_sup_coefficientGenerators (T : Set (SKM.SYM D k)) (s t : List I) :
    (ideal D Sc cutoff s t ⊔ coefficientGeneratorHomSpan D Sc cutoff
        (SKM.SYM.elvCoefficientQuotient D cutoff '' T) s t).comap
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVRelationSpan D Sc cutoff s t ⊔ CoefficientGeneratorSpan D Sc T s t := by
  rw [← map_elvRelationSpan_eq_oldIdeal D Sc cutoff s t,
    ← map_coefficientGeneratorSpan D Sc cutoff T s t, ← Submodule.map_sup]
  apply Submodule.comap_map_eq_self
  rw [elvQuotientMap_ker_eq_coefficientRelationSpan]
  exact (elvCoefficientRelationSpan_le D Sc cutoff s t).trans le_sup_left

/-- The literal elementary-power contribution in existing old coefficient Homs. -/
abbrev elementaryPowerHomSpan (L : I × ℕ → ℕ) (s t : List I) :=
  coefficientGeneratorHomSpan D Sc cutoff
    (Set.range fun a => elementaryCoefficients (k := k) D cutoff a ^ L a) s t

private theorem elementaryPower_image (L : I × ℕ → ℕ) :
    SKM.SYM.elvCoefficientQuotient (k := k) D cutoff ''
        Set.range (fun a : I × ℕ => SKM.SYM.e D k a.1 a.2 ^ L a) =
      Set.range (fun a => elementaryCoefficients (k := k) D cutoff a ^ L a) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (map_pow (SKM.SYM.elvCoefficientQuotient D cutoff) _ _).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, map_pow (SKM.SYM.elvCoefficientQuotient D cutoff) _ _⟩

/-- The presentation preimage for the paper's literal powers. In particular,
no equality between a weighted ideal and a power ideal is used. -/
theorem comap_oldIdeal_sup_elementaryPowers (L : I × ℕ → ℕ) (s t : List I) :
    (ideal D Sc cutoff s t ⊔ elementaryPowerHomSpan D Sc cutoff L s t).comap
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVRelationSpan D Sc cutoff s t ⊔
        CoefficientGeneratorSpan D Sc
          (Set.range fun a : I × ℕ => SKM.SYM.e D k a.1 a.2 ^ L a) s t := by
  have h := comap_oldIdeal_sup_coefficientGenerators D Sc cutoff
    (Set.range fun a : I × ℕ => SKM.SYM.e D k a.1 a.2 ^ L a) s t
  rw [elementaryPower_image] at h
  exact h

end OddMath.QuiverHecke.ELVOld
