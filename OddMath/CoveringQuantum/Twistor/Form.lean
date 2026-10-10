import OddMath.CoveringQuantum.PreF.GaugeForm
import OddMath.CoveringQuantum.Twistor.Scalars

/-!
# The twisting comparison of free half-algebra forms

The ordered phase map intertwines the free forms at `π = -1` and `π = 1`,
with parameter changed from `q` to `tq`, where `t² = -1`. This proves the
correspondence of their radicals. Transport of the Serre ideal remains a
separate obligation before this gives nondegeneracy of the Serre presentation.
-/

noncomputable section

namespace OddMath.CoveringQuantum.SuperCartanDatum

variable {I k : Type*} [LinearOrder I] [CommRing k]
  (C : SuperCartanDatum I) (q t : kˣ)

/-- The diagonal map on the free half algebra determined by the ordered phases. -/
def freeTwist : PreF k I ≃ₗ[k] PreF k I :=
  PreF.wordGauge (fun i j ↦ t ^ C.twistPhi i j)

variable (hC : C.BarConsistent) (ht : t ^ 2 = -1)

include hC ht in
/-- The ordered map intertwines the two free forms at the two signs. -/
theorem form_freeTwist (x y : PreF k I) :
    C.form q (-1) (C.freeTwist t x) y = C.form (t * q) 1 x (C.freeTwist t y) := by
  have hχ : ∀ i j, C.chi q (-1) i j = C.chi (t * q) 1 i j *
      ((t ^ C.twistPhi i j : kˣ) : k) * ((t ^ C.twistPhi j i)⁻¹ : kˣ) := by
    intro i j
    simpa only [Units.val_mul, mul_assoc] using (C.chi_twist hC q t ht i j).symm
  have hn : C.norm q (-1) = C.norm (t * q) 1 :=
    funext fun i ↦ (C.norm_twist hC q t ht i).symm
  unfold form freeTwist
  rw [PreF.form_wordGauge _ _ _ hχ, hn]

include hC ht in
/-- The free twisting map identifies the two form radicals. -/
theorem freeTwist_mem_radical_iff (x : PreF k I) :
    C.freeTwist t x ∈ PreF.radical (C.chi q (-1)) (C.norm q (-1)) ↔
      x ∈ PreF.radical (C.chi (t * q) 1) (C.norm (t * q) 1) := by
  rw [PreF.mem_radical_iff, PreF.mem_radical_iff]
  constructor
  · intro hx y
    obtain ⟨z, rfl⟩ := (C.freeTwist t).surjective y
    rw [← C.form_freeTwist q t hC ht]
    exact hx z
  · intro hx y
    rw [C.form_freeTwist q t hC ht]
    exact hx _

end OddMath.CoveringQuantum.SuperCartanDatum
