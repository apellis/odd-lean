import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponents
import OddMath.SKM.RouquierHomPostNaturalInverse

/-! # Input-module naturality of the induction matrix fields

Brundan–Ellis (1.13)–(1.14) require the ordinary unit/dot columns,
dot/counit rows, and signed crossing mate to be natural in every input
module map. These families are proved before any quotient specialization.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {q : ZMod 2} {δ : ∀ s, A.obj s ⟶ A.obj s} (hδ : IsSupernatural k q δ)

/-- Dot powers retain signed naturality for arbitrary homogeneous input maps. -/
theorem dotEnd_power_supernatural (n : ℕ) :
    IsSupernatural k (n • q) (F := induction A) (G := induction A)
      (fun M => dotEnd A hδ M ^ n) := by
  have hd := transformComponent_supernatural hδ
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
      (isSupernatural_id (R := k) (F := induction A))
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, dotEnd] using hd.comp ih

/-- The given ordinary unit followed by each dot power is supernatural. -/
theorem unitDotColumn_supernatural (n : ℕ) :
    IsSupernatural k (n • q) (F := 𝟭 (Superfunctor k C (SVec k)))
      (G := induction A ⋙ restriction A) (fun M => unitDotColumn A hδ M n) := by
  have hu := isSupernatural_of_natTrans (R := k) (adjunctionUnit A) (adjunctionUnit_mem A)
  simpa only [zero_add, unitDotColumn, adjunction] using hu.comp
    ((dotEnd_power_supernatural A hδ n).whiskerRight (restriction A))

end OddMath.QuiverHecke.ELVOld.BalancedInduction
