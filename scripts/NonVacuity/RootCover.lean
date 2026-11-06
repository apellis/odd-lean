import OddMath.SKM.RootCoverUnits

/-! # Non-vacuity: the units `c_{λ;i}` on affine `A₁` and on its root cover

Affine `A₁` with weight lattice `ℤ²`, coroots the coordinate projections and simple roots
`α₀ = (2, -2)`, `α₁ = (-2, 2)`, so `α₀ + α₁ = 0`. With `t₀₁ = 2`, `t₁₀ = 1` over `ℚ` there are no
units `c_{λ;i}` with the shift law of Brundan–Ellis (1.17); on the root cover they exist.
-/

noncomputable section

namespace NonVacuity.RootCover

open OddMath.SKM OddMath.SKM.RootCover

/-- Affine `A₁` on `ℤ²` with dependent simple roots. -/
def affA1 : Datum (Fin 2) (Fin 2 → ℤ) where
  cd :=
    { root := ![![2, -2], ![-2, 2]]
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by fin_cases i <;> rfl }
  isGCM :=
    { diag := fun i => by fin_cases i <;> rfl
      offDiag_nonpos := fun i j h => by
        fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide
      zero_comm := fun i j => by fin_cases i <;> fin_cases j <;> decide }
  parity := fun _ => 0
  even_of_odd := fun _ _ h => absurd h (by decide)

theorem affA1_d (i j : Fin 2) (hij : i ≠ j) : affA1.d i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

/-- `t₀₁ = 2` and all other `tᵢⱼ = 1`. -/
def affA1t (i j : Fin 2) : ℚˣ := if i = 0 ∧ j = 1 then Units.mk0 2 two_ne_zero else 1

/-- Parameters on affine `A₁` with `t₀₁ = 2`, `t₁₀ = 1` and `sᵢⱼ^{pq} = 0`. -/
def affA1Sc : Scalars affA1 ℚ where
  t := affA1t
  t_self := fun i => by fin_cases i <;> rfl
  t_symm_of_d_eq_zero := fun i j h => by
    by_cases hij : i = j
    · rw [hij]
    · exact absurd h (affA1_d i j hij)
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr two_ne_zero

theorem affA1_roots : affA1.α 0 + affA1.α 1 = 0 := by
  funext i
  fin_cases i <;> rfl

/-- No units with the shift law exist for these parameters. -/
theorem isEmpty_cScalars : IsEmpty (CScalars affA1Sc) := by
  refine ⟨fun cs => ?_⟩
  have h := congrArg Units.val (cs.t_mul_t_eq_one affA1_roots 0)
  norm_num [affA1Sc, affA1t] at h

/-- On the root cover they exist. -/
example : Nonempty (CScalars (coverScalars affA1 affA1Sc)) :=
  nonempty_cScalars_rootCover affA1 affA1Sc

end NonVacuity.RootCover
