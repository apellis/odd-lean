import OddMath.SKM.BWWPresentation
import NonVacuity.BWWScalars

/-! # The Kac–Moody 2-supercategory with Brundan–Wang–Webster parameters

On the datum of `NonVacuity.BWWScalars`: the presentation with `Qᵢⱼ = u³ + v³ + 1` is
parity-homogeneous and is `SKM.pres` of the underlying parameters; over the Brundan–Ellis
parameters `u³ + uv² + v³` it is `SKM.pres`. The constant term `1` is a pure monomial.
-/

noncomputable section
namespace NonVacuity.BWWKacMoodyPresentation
open OddMath OddMath.SKM NonVacuity.BWWScalars

example : (SKM.presBWW datum constantTerm).IsParityHomogeneous :=
  SKM.isParityHomogeneous_presBWW datum constantTerm

example : SKM.presBWW datum scalars.toBWW = SKM.pres datum scalars :=
  SKM.presBWW_toBWW scalars

example : SKM.presBWW datum constantTerm = SKM.pres datum constantTerm.toScalars :=
  SKM.presBWW_eq_pres constantTerm

example : scalars.toBWW.NoPure :=
  ((ScalarData.toBWW_homogeneous_iff scalars).mpr homogeneous).noPure

/-- The constant term is a pure monomial. -/
example : ¬constantTerm.NoPure := by
  intro h
  have := h true false 0 0 (by decide) (by rw [dn_ne (by decide)]; norm_num)
    (by rw [dn_ne (by decide)]; norm_num) (Or.inl rfl)
  simp [constantTerm, support] at this

example : (∑ p ∈ Finset.range (datum.dn true false + 1),
      ∑ q ∈ Finset.range (datum.dn false true + 1), constantTerm.c true false p q • (1 : ℚ)) =
    (constantTerm.t true false : ℚ) • 1 + (constantTerm.t false true : ℚ) • 1 +
      (∑ p ∈ Finset.range (datum.dn true false), constantTerm.c true false p 0 • (1 : ℚ) +
        ∑ q ∈ Finset.Ioo 0 (datum.dn false true), constantTerm.c true false 0 q • (1 : ℚ)) +
      ∑ p ∈ Finset.Ioo 0 (datum.dn true false), ∑ q ∈ Finset.Ioo 0 (datum.dn false true),
        constantTerm.c true false p q • (1 : ℚ) :=
  constantTerm.sum_box_eq (i := true) (j := false) (by decide) (by rw [d_ne (by decide)]; decide)
    fun _ _ => 1

end NonVacuity.BWWKacMoodyPresentation
