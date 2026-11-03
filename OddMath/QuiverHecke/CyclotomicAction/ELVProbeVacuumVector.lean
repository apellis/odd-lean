import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendSpecialization
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport

/-! # The nonzero empty vector of the regular probe

The probe vacuum T₀ in `SwappedActionAssembly.md`, F2, is the genuine
height-zero regular module. Its empty word-idempotent vector is nonzero
by the original affine empty-word PBW coordinate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private def emptyProbeNF : NFIdx ([] : List I) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private theorem affineEmptyIdentity_ne_zero [Nontrivial k] :
    (𝟙 ((pres D Sc).obj (ob D []))) ≠ 0 := by
  rw [← ELVOld.vacuum_nf D Sc (emptyProbeNF (I := I)), ← basisNF_apply]
  exact (basisNF D Sc [] []).ne_zero (emptyProbeNF (I := I))

variable [Fintype I] (m : I → ℕ)

/-- The original empty object in the old scalar-probe source category. -/
def probeOldVacuumObject : ELVOld.OldContentCategory D Sc (probeCutoff D m) [] :=
  ⟨⟨[]⟩, List.Perm.refl _⟩

/-- The literal regular height-zero probe, with its existing old Hom action. -/
abbrev probeOldVacuumRegular :=
  probeOldModule D m Sc [] (SuperBimodule.regular
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) 0))

/-- The actual empty word idempotent, as a vector of its fixed submodule. -/
def probeOldVacuumVector :
    (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m) :=
  ⟨probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m), by
    change probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) *
      probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) =
        probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m)
    change Hn.wordIdempotent (vacuumWord (I := I)) * Hn.wordIdempotent (vacuumWord (I := I)) =
      Hn.wordIdempotent (vacuumWord (I := I))
    exact Hn.wordIdempotent_sq _⟩

/-- The height-zero matrix entry is the nonzero original empty PBW identity. -/
theorem probeOldVacuumVector_ne_zero [Nontrivial k] : probeOldVacuumVector D Sc m ≠ 0 := by
  intro hz
  have he := congrArg Subtype.val hz
  change Hn.wordIdempotent (vacuumWord (I := I)) = 0 at he
  have hh := congrArg (fun f : Hn D Sc 0 => f (vacuumWord, vacuumWord)) he
  simp only [Hn.wordIdempotent, OddMath.FiniteHomMatrix.idem, OddMath.FiniteHomMatrix.single,
    DFinsupp.single_eq_same, DFinsupp.zero_apply] at hh
  exact affineEmptyIdentity_ne_zero D Sc hh

end OddMath.QuiverHecke
