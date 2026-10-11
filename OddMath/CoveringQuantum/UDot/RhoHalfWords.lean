import OddMath.CoveringQuantum.UDot.Sigma

/-!
# Adjoint reversal on actual modified half words

The adjoint map of [BE2, arXiv:1701.04133v2, (9.8)] restricts to the
nonunital modified algebra. Its effect on a half word is reversal, exchange
of signs and multiplication by a unit. No formula for a full modified form
is assumed here.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot
open MulOpposite
variable {k I X : Type*} [CommRing k] [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (q : kˣ) (π : k)

/-- The actual linear adjoint map on the nonunital algebra. -/
def rhoModified (hπ : π ^ 2 = 1) : modified D q π →ₗ[k] modified D q π where
  toFun x := ⟨(rho D q π hπ x).unop, rho_mem_modified D q π hπ x.property⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_rhoModified (hπ : π ^ 2 = 1) (x : modified D q π) :
    (rhoModified D q π hπ x : CoveringUDot k D q π) = (rho D q π hπ x).unop := rfl

theorem rhoModified_mul (hπ : π ^ 2 = 1) (x y : modified D q π) :
    rhoModified D q π hπ (x * y) = rhoModified D q π hπ y * rhoModified D q π hπ x :=
  Subtype.ext (rho_mul (D := D) (q := q) hπ x.val y.val)

@[simp] theorem rhoModified_rhoModified (hπ : π ^ 2 = 1) (x : modified D q π) :
    rhoModified D q π hπ (rhoModified D q π hπ x) = x :=
  Subtype.ext (rho_rho (D := D) (q := q) hπ x.val)

/-- Reversing a half word under the adjoint introduces a unit coefficient.
This existential version does not choose a formula for that coefficient. -/
theorem rho_halfWord_unit (hπ : π ^ 2 = 1) (positive : Bool) (w : List I) (μ : X) :
    ∃ c : kˣ, (rho D q π hπ (halfWord D q π positive w μ)).unop =
      (c : k) • halfWord D q π (!positive) w.reverse
        (μ + halfWeight D positive (PreF.wordWeight w)) := by
  induction w with
  | nil => exact ⟨1, by simp [halfWord]⟩
  | cons i w ih =>
    obtain ⟨c, hc⟩ := ih
    let ν := μ + halfWeight D positive (PreF.wordWeight w)
    let z : ℤ := if positive then -(D.d i * (D.h i ν + 1)) else D.d i * (D.h i ν - 1)
    refine ⟨c * q ^ z, ?_⟩
    have hg : (rho D q π hπ (halfGen D q π positive i ν)).unop =
        qp q z • halfGen D q π (!positive) i (ν + halfRoot D positive i) := by
      cases positive <;> simp [halfGen, halfRoot, z, rho_E, rho_F, sub_eq_add_neg]
    have hs (b : Bool) (j : I) (η : X) :
        halfWord D q π b [j] η = halfGen D q π b j η := by
      simp only [halfWord, PreF.wordWeight_nil, halfWeight_zero, add_zero]
      exact (halfGen_mem_block D q π b j η).2
    have hn : halfRoot D (!positive) i = -halfRoot D positive i := by
      cases positive <;> simp [halfRoot]
    rw [halfWord, rho_mul, hc]
    change (c : k) • halfWord D q π (!positive) w.reverse ν *
      (rho D q π hπ (halfGen D q π positive i ν)).unop = _
    rw [hg, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [List.reverse_cons, halfWord_append, hs, PreF.wordWeight_cons,
      PreF.wordWeight_nil, halfWeight_add, halfWeight_single, add_zero, Units.val_mul, qp, hn]
    congr 2
    · congr 1
      dsimp [ν]
      abel
    · congr 1
      dsimp [ν]
      abel

end OddMath.CoveringQuantum.UDot
