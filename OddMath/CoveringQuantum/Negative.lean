import OddMath.CoveringQuantum.SuperCount.Count
import OddMath.CoveringQuantum.Twistor.Nondegenerate
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Negative-sign nondegeneracy over a field

At `π = -1` the radical of the form on `'f` is the Serre ideal for every super Cartan datum with
finitely many simple roots (`SuperCartanDatum.serreIdeal_neg_one_eq_radical_of_transcendental`,
from the π = -1 Serre count of `OddMath.CoveringQuantum.SuperCount.Count`), so the form on the
Serre presentation is nondegenerate. This is a field theorem, not yet the generic covering-ring
theorem.
-/

noncomputable section
namespace OddMath.CoveringQuantum.SuperCartanDatum

variable {k I : Type*} [Field k] [CharZero k] [DecidableEq I] [Finite I]
  (C : SuperCartanDatum I) (q : kˣ)
  (hq : Transcendental ℚ (q : k))

include hq in
/-- Nondegeneracy at the negative sign over a characteristic-zero field with transcendental
parameter, for finitely many simple roots. -/
theorem serreForm_neg_one_nondegenerate_of_transcendental :
    (C.serreForm q (-1) (by simp)).Nondegenerate :=
  (C.serreForm_nondegenerate_iff_ideal_eq q (-1) (by simp)).mpr
    (C.serreIdeal_neg_one_eq_radical_of_transcendental hq)

end OddMath.CoveringQuantum.SuperCartanDatum
