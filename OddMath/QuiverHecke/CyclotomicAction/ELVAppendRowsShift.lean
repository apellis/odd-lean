/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRows
/-!
# Moving powers on append common rows

The moving central dot or square translates the last-strand exponent and
leaves every old quotient coefficient unchanged, including exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace AppendIdx
variable {i : I} {v w : List I}
def shift (x : AppendIdx i v w) (d : ℕ) : AppendIdx i v w :=
  ⟨(d + x.1.1, x.1.2), x.2⟩
end AppendIdx
namespace ELVOld
theorem appendTail_shift {i : I} {v w : List I} (x : AppendIdx i v w) (d : ℕ) :
    (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ d : End _) ≫ appendTail D Sc x =
      appendTail D Sc (x.shift d) := by
  have hl : x.oldTarget.length = v.length := by simp [AppendIdx.oldTarget]
  rw [dotE_pow, appendTail, cl_comp]
  apply cl_eq_cl
  simp only [AppendIdx.shift, List.replicate_add, List.map_append, List.append_assoc,
    List.map_replicate, hl]

end ELVOld
end OddMath.QuiverHecke
