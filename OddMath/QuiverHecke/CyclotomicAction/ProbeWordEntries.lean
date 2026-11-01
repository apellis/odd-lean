import OddMath.QuiverHecke.CyclotomicAction.ProbeWordCorner

/-! # Rectangular cyclotomic entries and probe cancellation

The distinct-colour step of `InvertibleDotProbe.md` §3 uses crossings
between different word corners. A dot is a unit in its own corner, not
a left-regular element of the entire cyclotomic algebra. The cancellation
below retains the actual word idempotents and rectangular entries.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

def cyclotomicWordEntry {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) : CyclotomicAlgebra D Sc a n :=
  cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f)

theorem cyclotomicWordEntry_id {n : ℕ} (s : Word I (n + 1)) :
    cyclotomicWordEntry D Sc a s s (𝟙 _) = cyclotomicWordIdempotent D Sc a s := rfl

theorem cyclotomicWordEntry_comp {n : ℕ} (s t u : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) (g : wordObj D Sc t ⟶ wordObj D Sc u) :
    cyclotomicWordEntry D Sc a s u (f ≫ g) =
      cyclotomicWordEntry D Sc a t u g * cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n _ =
    cyclotomicMk D Sc a n _ * cyclotomicMk D Sc a n _
  rw [← map_mul, FiniteHomMatrix.single_mul_single]

theorem cyclotomicWordEntry_left_support {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordIdempotent D Sc a t * cyclotomicWordEntry D Sc a s t f =
      cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single t t (𝟙 _)) *
    cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) = _
  rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.comp_id]
  rfl

theorem cyclotomicWordEntry_right_support {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordEntry D Sc a s t f * cyclotomicWordIdempotent D Sc a s =
      cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) *
    cyclotomicMk D Sc a n (FiniteHomMatrix.single s s (𝟙 _)) = _
  rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.id_comp]
  rfl

/-- A unit of the actual target word corner cancels on every element of
its row, including rectangular entries with another source word. -/
theorem cyclotomicWordCorner_unit_mul_eq_zero {n : ℕ} (s : Word I (n + 1))
    (u : CyclotomicWordCorner D Sc a s) (hu : IsUnit u)
    (z : CyclotomicAlgebra D Sc a n)
    (hs : cyclotomicWordIdempotent D Sc a s * z = z)
    (hz : u.val * z = 0) : z = 0 := by
  rcases hu with ⟨U, rfl⟩
  have hinv := congrArg
    (fun b : CyclotomicWordCorner D Sc a s => b.val) U.inv_val
  change U.inv.val * U.val.val = cyclotomicWordIdempotent D Sc a s at hinv
  have h := congrArg (fun b : CyclotomicAlgebra D Sc a n => U.inv.val * b) hz
  change U.inv.val * (U.val.val * z) = U.inv.val * 0 at h
  rw [← mul_assoc, hinv, hs, mul_zero] at h
  exact h

/-- The crossing image already has the target support required for corner
unit cancellation; no source-column regularity assumption is added. -/
theorem cyclotomicWordEntry_unit_cancel {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (u : CyclotomicWordCorner D Sc a t) (hu : IsUnit u)
    (z : CyclotomicAlgebra D Sc a n)
    (hz : u.val * (cyclotomicWordEntry D Sc a s t f * z) = 0) :
    cyclotomicWordEntry D Sc a s t f * z = 0 := by
  apply cyclotomicWordCorner_unit_mul_eq_zero D Sc a t u hu _ ?_ hz
  rw [← mul_assoc, cyclotomicWordEntry_left_support]

/-- The distinct-colour probe kernel argument on the actual rectangular
crossing entries. The supplied equations are the literal dot slide and
the quadratic polynomial separated into its unit leading term and a
right multiple of the next dot; their construction remains separate. -/
theorem cyclotomicWordEntry_distinct_kernel {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (g : wordObj D Sc t ⟶ wordObj D Sc s)
    (v : CyclotomicWordCorner D Sc a s) (w : CyclotomicWordCorner D Sc a t)
    (lead : CyclotomicWordCorner D Sc a s) (hw : IsUnit w) (hlead : IsUnit lead)
    (R : CyclotomicAlgebra D Sc a n) (eps : k)
    (slide : w.val * cyclotomicWordEntry D Sc a s t f =
      eps • (cyclotomicWordEntry D Sc a s t f * v.val))
    (quadratic : cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f =
      lead.val + R * v.val)
    (z : CyclotomicWordCorner D Sc a s) (hz : v * z = 0) : z = 0 := by
  have hvz := congrArg (fun b : CyclotomicWordCorner D Sc a s => b.val) hz
  change v.val * z.val = 0 at hvz
  have ha : cyclotomicWordEntry D Sc a s t f * z.val = 0 := by
    apply cyclotomicWordEntry_unit_cancel D Sc a s t f w hw
    rw [← mul_assoc, slide, smul_mul_assoc, mul_assoc, hvz, mul_zero, smul_zero]
  have hlead_z : lead.val * z.val = 0 := by
    have h := congrArg (fun b : CyclotomicAlgebra D Sc a n => b * z.val) quadratic
    rw [mul_assoc, ha, mul_zero, add_mul, mul_assoc, hvz, mul_zero, add_zero] at h
    exact h.symm
  have hs := ((Subsemigroup.mem_corner_iff
    (cyclotomicWordIdempotent_idem D Sc a s)).mp z.property).1
  have hzero := cyclotomicWordCorner_unit_mul_eq_zero D Sc a s lead hlead z.val hs hlead_z
  apply Subtype.ext
  change z.val = 0
  exact hzero

end OddMath.QuiverHecke
