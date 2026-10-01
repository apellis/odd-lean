import OddMath.Frontier.EQOnhDGRing
import DG.HalfGraded.Diagonal

/-!
# The diagonal half-grading on the existing odd nilHecke dg ring

The ordinary dg ring `EQOnhDG.ONH n` is the integral odd nilHecke algebra on
`n + 2` strands. Its grading is half the Ellis–Qi `q`-degree. Applying the
published diagonal bridge restores the bidegrees `deg(xᵢ) = (2, 1)` and
`deg(∂ᵢ) = (-2, 1)`, and the unchanged differential has bidegree `(2, 1)`.
The formulas `d(xᵢ) = xᵢ²` and `d(∂ᵢ) = 1` come from the existing dg-ring instance.

This is a ring-level consumer of `HalfGradedDGRing.ofDGRing`, not a comparison
of derived module categories or an integral nilHecke Grothendieck-group computation.
No compact generator, tensor-product formula, or later Ellis–Qi categorification
headline is asserted here.
-/

noncomputable section

namespace OddMath.Frontier.EQDiagonal

open DG DG.HalfGradedDGRing EQOnhDG

/-- The existing dg `ONH_{n+2}` with its diagonal half-grading. -/
abbrev onh (n : ℕ) : HalfGradedDGRing (ONH n) 2 := ofDGRing (ONH n)

/-- Ordinary degree `k` becomes internal degree `2k` and parity `k mod 2`. -/
theorem onh_hgrading (n : ℕ) (k : ℤ) :
    (onh n).hgrading (2 * k, (k : ZMod 2)) = DG.grading (M := ONH n) k :=
  ofDGRing_hgrading (ONH n) k

/-- The actual nilHecke dot has bidegree `(2, 1)`. -/
theorem onh_x_mem (n : ℕ) (j : Fin (n + 2)) :
    ONH.x j ∈ (onh n).hgrading (2, 1) := by
  simpa using (show ONH.x j ∈ (onh n).hgrading (2 * 1, ((1 : ℤ) : ZMod 2)) by
    rw [onh_hgrading]; exact ONH.x_mem_grading j)

/-- The actual nilHecke crossing has bidegree `(-2, 1)`. -/
theorem onh_del_mem (n : ℕ) (i : Fin (n + 1)) :
    ONH.del i ∈ (onh n).hgrading (-2, 1) := by
  simpa using (show ONH.del i ∈ (onh n).hgrading (2 * (-1), ((-1 : ℤ) : ZMod 2)) by
    rw [onh_hgrading]; exact ONH.del_mem_grading i)

/-- The bridge preserves the actual differential, not just its degree. -/
theorem onh_hd (n : ℕ) : (onh n).hd = DG.d := rfl

/-- Ellis–Qi (3.1) remains the dot differential in the half-grading. -/
theorem onh_hd_x (n : ℕ) (j : Fin (n + 2)) :
    (onh n).hd (ONH.x j) = ONH.x j * ONH.x j := ONH.d_x j

/-- Ellis–Qi Proposition 3.3 remains the crossing differential in the half-grading. -/
theorem onh_hd_del (n : ℕ) (i : Fin (n + 1)) :
    (onh n).hd (ONH.del i) = 1 := ONH.d_del i

/-- The same nilHecke differential raises internal degree by `2` and flips parity. -/
theorem onh_hd_mem {n : ℕ} {a : ONH n} {j : ℤ} {p : ZMod 2}
    (ha : a ∈ (onh n).hgrading (j, p)) :
    (onh n).hd a ∈ (onh n).hgrading (j + 2, p + 1) :=
  (onh n).hd_mem ha

end OddMath.Frontier.EQDiagonal
