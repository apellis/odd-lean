import OddMath.QuiverHecke.CyclotomicAction.ProbeWordEntries

/-! # Direct units from rectangular probe crossings

Both signed dot slides and the quadratic remainder give left and right
inverses in the actual source word corner. Finite-dimensionality is not
used. The explicit quadratic remainder and slide hypotheses remain to be
instantiated for the actual distinct-colour crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

/-- Travel from the source word through a target-corner element and back.
The result lies in the literal source corner by the crossing supports. -/
def cyclotomicWordEntry_sandwich {n : ℕ} (s t : Word I (n+1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (g : wordObj D Sc t ⟶ wordObj D Sc s)
    (w : CyclotomicWordCorner D Sc a t) : CyclotomicWordCorner D Sc a s :=
  ⟨cyclotomicWordEntry D Sc a t s g * w.val *
      cyclotomicWordEntry D Sc a s t f, by
    apply (Subsemigroup.mem_corner_iff (cyclotomicWordIdempotent_idem D Sc a s)).mpr
    constructor
    · rw [← mul_assoc, ← mul_assoc, cyclotomicWordEntry_left_support]
    · rw [mul_assoc, cyclotomicWordEntry_right_support]⟩

/-- Separate left and right positive-dot remainders suffice; they need not
coincide or commute with the following dot. -/
theorem cyclotomicWordEntry_distinct_isUnit_twoRemainders {n : ℕ} (s t : Word I (n+1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t)
    (g : wordObj D Sc t ⟶ wordObj D Sc s)
    (v : CyclotomicWordCorner D Sc a s) (w : CyclotomicWordCorner D Sc a t)
    (lead Rright Rleft : CyclotomicWordCorner D Sc a s)
    (hw : IsUnit w) (hlead : IsUnit lead)
    (slide : w.val * cyclotomicWordEntry D Sc a s t f =
      cyclotomicWordEntry D Sc a s t f * v.val)
    (slide' : v.val * cyclotomicWordEntry D Sc a t s g =
      cyclotomicWordEntry D Sc a t s g * w.val)
    (quadratic_right : cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f =
      lead.val + Rright.val * v.val)
    (quadratic_left : cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f =
      lead.val + v.val * Rleft.val) : IsUnit v := by
  rcases hw with ⟨W, rfl⟩
  rcases hlead with ⟨U, rfl⟩
  let Cr := cyclotomicWordEntry_sandwich D Sc a s t f g (↑(W⁻¹)) - Rright
  let Cl := cyclotomicWordEntry_sandwich D Sc a s t f g (↑(W⁻¹)) - Rleft
  have hwi : W.inv.val * W.val.val = cyclotomicWordIdempotent D Sc a t :=
    congrArg (fun z : CyclotomicWordCorner D Sc a t => z.val) W.inv_val
  have hiw : W.val.val * W.inv.val = cyclotomicWordIdempotent D Sc a t :=
    congrArg (fun z : CyclotomicWordCorner D Sc a t => z.val) W.val_inv
  have hCv : Cr * v = U.val := by
    apply Subtype.ext
    change (cyclotomicWordEntry D Sc a t s g * W.inv.val *
      cyclotomicWordEntry D Sc a s t f - Rright.val) * v.val = U.val.val
    calc
      _ = cyclotomicWordEntry D Sc a t s g *
          (W.inv.val * (cyclotomicWordEntry D Sc a s t f * v.val)) -
          Rright.val * v.val := by noncomm_ring
      _ = cyclotomicWordEntry D Sc a t s g *
          (W.inv.val * (W.val.val * cyclotomicWordEntry D Sc a s t f)) -
          Rright.val * v.val := by rw [slide]
      _ = cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f -
          Rright.val * v.val := by
        rw [← mul_assoc W.inv.val, hwi, cyclotomicWordEntry_left_support]
      _ = U.val.val := by rw [quadratic_right]; noncomm_ring
  have hvC : v * Cl = U.val := by
    apply Subtype.ext
    change v.val * (cyclotomicWordEntry D Sc a t s g * W.inv.val *
      cyclotomicWordEntry D Sc a s t f - Rleft.val) = U.val.val
    calc
      _ = (v.val * cyclotomicWordEntry D Sc a t s g) * W.inv.val *
          cyclotomicWordEntry D Sc a s t f - v.val * Rleft.val := by noncomm_ring
      _ = (cyclotomicWordEntry D Sc a t s g * W.val.val) * W.inv.val *
          cyclotomicWordEntry D Sc a s t f - v.val * Rleft.val := by rw [slide']
      _ = cyclotomicWordEntry D Sc a t s g * cyclotomicWordEntry D Sc a s t f -
          v.val * Rleft.val := by
        rw [mul_assoc (cyclotomicWordEntry D Sc a t s g), hiw,
          cyclotomicWordEntry_right_support]
      _ = U.val.val := by rw [quadratic_left]; noncomm_ring
  let l := U.inv * Cr
  let r := Cl * U.inv
  have hl : l * v = 1 := by
    change (U.inv * Cr) * v = 1
    rw [mul_assoc, hCv, U.inv_val]
  have hr : v * r = 1 := by
    change v * (Cl * U.inv) = 1
    rw [← mul_assoc, hvC, U.val_inv]
  have hlr : l = r := by
    calc
      l = l * (v * r) := by rw [hr, mul_one]
      _ = (l * v) * r := (mul_assoc _ _ _).symm
      _ = r := by rw [hl, one_mul]
  exact ⟨⟨v, r, hr, by rw [← hlr]; exact hl⟩, rfl⟩

end OddMath.QuiverHecke
