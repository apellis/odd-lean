/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirSourceCoordinates
import OddMath.QuiverHecke.ReservoirWeights

/-! # Cofinal regular vacuum windows at a prescribed weight

Ports the simultaneous weight and word-window choice of
`Categorification/KLR/Unfurling/GenericVacuumCoordinates.lean` and
`Categorification/KLR/Unfurling/GenericVacuumWordCoordinates.lean`.
The extended weights have literal difference `(μ,0)`, and the regular action
is on the connected ELV quotient. The categorical comparison identifying
these modules with evaluation of the fused vacuum is not asserted here.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory
open ReservoirWeights
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- One choice simultaneously realizes the fixed external weight, both
cofinal cutoffs, and an injective regular cyclic observation on the entire
bounded joint window. No number of spectator strands occurs in the bound. -/
theorem exists_regular_vacuum_window (μ : X) (t t' : List I) (d : ℕ) :
    ∃ (m N : ℕ) (μp μm : X × (I → ℤ)),
      μm - μp = (μ, 0) ∧
      (∀ i, (pairingExtension D).h i μp = probeLevel (fun j => D.h j μ) m i) ∧
      (∀ i, (pairingExtension D).h i μm = reservoirLevel (fun j => D.h j μ) m i) ∧
      (∀ i, N ≤ reservoirLevel (fun j => D.h j μ) m i ∧
        N ≤ probeLevel (fun j => D.h j μ) m i) ∧
      d + 2 * t.length.choose 2 < N ∧
      Function.Injective (fun f : ExtendedAtMost D Sc t t' d =>
        reservoirPostcomp D Sc (reservoirLevel (fun j => D.h j μ) m) f.val
          (reservoirRegularGenerator D Sc (reservoirLevel (fun j => D.h j μ) m) t)) := by
  obtain ⟨m, N, hN, hb⟩ := observation_bound (fun j => D.h j μ) d t.length
  obtain ⟨μp, μm, hw, hp, hm⟩ := exists_extended_weights D μ m
  exact ⟨m, N, μp, μm, hw, hp, hm, hN, hb,
    reservoirRegular_injective_on_window D Sc _ (fun i => (hN i).1) hb⟩

/-- The regular cyclic family with balanced reservoir levels jointly detects
all affine morphisms with arbitrary ordered coefficient products. -/
theorem balanced_regular_vacuums_detect (μ : X) (t t' : List I)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : ∀ m, reservoirPostcomp D Sc (reservoirLevel (fun j => D.h j μ) m) f
      (reservoirRegularGenerator D Sc (reservoirLevel (fun j => D.h j μ) m) t) = 0) :
    f = 0 := by
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc t t' f
  obtain ⟨m, N, hN, hb⟩ := observation_bound (fun j => D.h j μ) d t.length
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc
    (cutoff := reservoirLevel (fun j => D.h j μ) m) (t := t) (t' := t')
    (d := d) (fun i => (hN i).1) hb
  have hz : (ELVRelationSpan D Sc (reservoirLevel (fun j => D.h j μ) m) t t').mkQ f = 0 := by
    simpa only [reservoirPostcomp_generator] using hf m
  exact congrArg Subtype.val (hinj (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa using hz))

/-- A window defined at every strand number, including cutoffs too small
for a positive C0 window. The zero window requires no sign correction. -/
def regularVacuumWindow (m n : ℕ) : ℕ := 2 * m - 2 * n.choose 2 - 1

/-- The regular windows cover every requested active word and degree. -/
theorem regularVacuumWindow_covers (h : I → ℤ) (n d : ℕ) :
    ∃ m N, d ≤ regularVacuumWindow m n ∧
      (∀ i, N ≤ reservoirLevel h m i) ∧ d + 2 * n.choose 2 < N := by
  let m := d + 2 * n.choose 2 + 1
  refine ⟨m, 2 * m, ?_, ?_, ?_⟩
  · unfold regularVacuumWindow
    omega
  · intro i
    simp only [reservoirLevel]
    omega
  · omega

/-- The complete cofinal regular family has source-order recovery even at
small cutoffs. Only the positive windows use the C0 splitting. -/
theorem regularVacuumWindow_coordinates {K : Type u} [Field K] (S : SKM.Scalars D K)
    (h : I → ℤ) (m : ℕ) (t t' : List I) :
    ∃ recover : ReservoirQuotient D S (reservoirLevel h m) t t' →ₗ[K]
        ReservoirQuotient D S (reservoirLevel h m) t t',
      ∀ (a : SKM.SYM D K)
        (f : (pres D S).obj (ob D t) ⟶ (pres D S).obj (ob D t')),
        sourceCoefficientHom D S a f ∈
          ExtendedAtMost D S t t' (regularVacuumWindow m t.length) →
        recover (reservoirPostcomp D S (reservoirLevel h m) (sourceCoefficientHom D S 1 f)
          (reservoirPostcomp D S (reservoirLevel h m) (sourceCoefficientHom D S a (𝟙 _))
            (reservoirRegularGenerator D S (reservoirLevel h m) t))) =
          (ELVRelationSpan D S (reservoirLevel h m) t t').mkQ
            (sourceCoefficientHom D S a f) := by
  by_cases hz : regularVacuumWindow m t.length = 0
  · refine ⟨LinearMap.id, ?_⟩
    intro a f hf
    rw [hz] at hf
    simp only [LinearMap.id_apply, reservoirPostcomp_generator, reservoirPostcomp_mk,
      ← reservoirSourceOrder_source]
    rw [reservoirSourceOrder_zero_window D S hf]
  · apply exists_reservoir_source_coordinates D S _ _ _ _ (N := 2 * m)
    · intro i
      simp only [reservoirLevel]
      omega
    · unfold regularVacuumWindow at *
      omega

end OddMath.QuiverHecke
