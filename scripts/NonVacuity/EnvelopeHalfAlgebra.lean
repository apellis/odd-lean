import OddMath

/-! # Brundan–Ellis, Theorem 11.3: `γ̄ : f_𝒜 ≅ K₀(Ḣ_{q,π})`

The covering datum of `𝔬𝔰𝔭(1|2)` (rank one, `a = 2`, `d = 1`, the simple root odd, which is
bar-consistent), on the weight lattice `ℤ`, with scalars `t = 1`, `s = 0` over `ℚ`.
-/

noncomputable section
open OddMath OddMath.QuiverHecke OddMath.CoveringQuantum

namespace NonVacuity.EnvelopeHalfAlgebra

/-- The covering Cartan datum of rank one with `a = 2`, `d = 1` and an odd simple root. -/
def cartan : SuperCartanDatum Unit where
  a := Matrix.of fun _ _ ↦ 2
  isGCM :=
    { diag := fun _ ↦ rfl
      offDiag_nonpos := fun i j h ↦ absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ ↦ Iff.rfl }
  d := fun _ ↦ 1
  d_pos := fun _ ↦ one_pos
  d_mul_symm := fun _ _ ↦ rfl
  parity := fun _ ↦ 1
  even_of_odd := fun _ _ _ ↦ even_two

theorem barConsistent : cartan.BarConsistent := fun _ ↦ Nat.cast_one

/-- `𝔬𝔰𝔭(1|2)` on the weight lattice `ℤ`: simple root `2`, `⟨h, μ⟩ = μ`. -/
def datum : RootDatum Unit ℤ where
  toSuperCartanDatum := cartan
  cd :=
    { root := fun _ ↦ 2
      coroot := fun _ ↦ LinearMap.id
      coroot_root_self := fun _ ↦ rfl }
  coroot_root _ _ := rfl

def scalars : SKM.Scalars datum.toSKM ℚ where
  t := fun _ _ ↦ 1
  t_self := fun _ ↦ rfl
  t_symm_of_d_eq_zero := fun _ _ _ ↦ rfl
  s := fun _ _ _ _ ↦ 0
  s_symm := fun _ _ _ _ ↦ rfl
  s_eq_zero := fun _ _ _ _ _ ↦ rfl
  two_isUnit := fun _ ↦ isUnit_iff_ne_zero.mpr (by norm_num)

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h ↦ absurd rfl h

/-- **BE2 Theorem 11.3** for `𝔬𝔰𝔭(1|2)`: the isomorphism sends `θ^{(3)}` to `[P(i^{(3)})]`. -/
example : theorem_11_3 datum scalars homogeneous barConsistent
    ⟨dpF datum () 3, dpF_mem_fA datum () 3⟩ = dpCls datum scalars homogeneous () 3 :=
  theorem_11_3_dpF datum scalars homogeneous () 3 barConsistent

example : Function.Bijective (theorem_11_3 datum scalars homogeneous barConsistent) :=
  (theorem_11_3 datum scalars homogeneous barConsistent).bijective

end NonVacuity.EnvelopeHalfAlgebra
