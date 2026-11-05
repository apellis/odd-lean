import OddMath.QuiverHecke.CyclotomicAction.ELVProbeContentSpecialization
import OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGrading

/-! # Parity of the actual all-height scalar probe entries
The untruncated old ELV quotient specializes to the existing graded height
algebra. This is the parity input for restriction of actual probe modules.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

/-- The all-height quotient map preserves the prescribed super grading. -/
theorem probeHeightMk_parity (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    {p : ZMod 2} {x : Hn D Sc n} (hx : x ∈ affineParity D Sc n p) :
    probeHeightMk D m Sc n x ∈ heightParity D Sc a ha n p := by
  cases n with
  | zero => exact hx
  | succ n => exact cyclotomicMk_parity D Sc a ha n hx

/-- Actual old quotient entries retain total super parity, including exterior
coefficients that the scalar specialization sends to zero. -/
theorem elvProbeHeightWordEntry_parity (ha : CyclotomicPolynomialParity D a)
    {n : ℕ} (s t : Word I n) {p : ZMod 2}
    {f : ELVOld.Old D Sc cut s.val t.val}
    (hf : f ∈ ELVOld.oldParity D Sc cut s.val t.val p) :
    elvProbeHeightWordEntry D m Sc s t f ∈ heightParity D Sc a ha n p := by
  obtain ⟨f, hf, rfl⟩ := hf
  rw [elvProbeHeightWordEntry_mk]
  apply probeHeightMk_parity D m Sc ha n
  exact FiniteHomMatrix.single_mem_component t s
    ((elvProbeAffineSpecialization D m Sc).map_mem hf)

/-- The canonical probe parity proof supplies the preceding bridge directly. -/
theorem elvProbeHeightWordEntry_probeParity {n : ℕ} (s t : Word I n)
    {p : ZMod 2} {f : ELVOld.Old D Sc cut s.val t.val}
    (hf : f ∈ ELVOld.oldParity D Sc cut s.val t.val p) :
    elvProbeHeightWordEntry D m Sc s t f ∈
      heightParity D Sc a (probePolynomial_parity D m) n p :=
  elvProbeHeightWordEntry_parity D m Sc (probePolynomial_parity D m) s t hf

/-- The specialized rectangular entry lands in its actual target word summand. -/
theorem elvProbeHeightWordEntry_target {n : ℕ} (s t : Word I n)
    (f : ELVOld.Old D Sc cut s.val t.val) :
    probeHeightMk D m Sc n (Hn.wordIdempotent t) *
      elvProbeHeightWordEntry D m Sc s t f = elvProbeHeightWordEntry D m Sc s t f := by
  rw [← elvProbeHeightWordEntry_id D m Sc t,
    ← elvProbeHeightWordEntry_comp D m Sc s t t]
  obtain ⟨f, rfl⟩ := (ELVOld.ideal D Sc cut s.val t.val).mkQ_surjective f
  rw [ELVOld.oldComp_mk, Category.comp_id]

end OddMath.QuiverHecke
