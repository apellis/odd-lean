import OddMath.SKM.BWWScalars

/-! # Brundan–Wang–Webster parameters

Two even vertices with Cartan entries `-3`. The polynomial `Qᵢⱼ(u, v) = u³ + v³ + 1` has a
constant term, so it is a Brundan–Wang–Webster parameter system that is not homogeneous and
does not come from Brundan–Ellis parameters. The polynomial `Qᵢⱼ(u, v) = u³ + uv² + v³` comes
from homogeneous Brundan–Ellis parameters, and (H) recovers them.
-/

noncomputable section
namespace NonVacuity.BWWScalars
open OddMath OddMath.SKM

/-- Two even vertices with Cartan entries `-3`. -/
def datum : Datum Bool (Bool → ℤ) where
  cd := {
    root := fun j i => if i = j then 2 else -3
    coroot := fun i => LinearMap.proj i
    coroot_root_self := fun i => by simp }
  isGCM := {
    diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j hij
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => 0
  even_of_odd := by
    intro i j h
    exact absurd h (by decide)

theorem d_ne {i j : Bool} (h : i ≠ j) : datum.d i j = 3 := by
  cases i <;> cases j <;> first | exact absurd rfl h | rfl

theorem dn_ne {i j : Bool} (h : i ≠ j) : datum.dn i j = 3 := by
  simp [Datum.dn, d_ne h]

/-- The exponents of the monomials `u³`, `v³` and `1`. -/
def support (p q : ℕ) : Prop := (p = 3 ∧ q = 0) ∨ (p = 0 ∧ q = 3) ∨ (p = 0 ∧ q = 0)

instance (p q : ℕ) : Decidable (support p q) := by unfold support; infer_instance

/-- `Qᵢⱼ(u, v) = u³ + v³ + 1`. -/
def constantTerm : BWWScalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  c := fun i j p q => if i ≠ j ∧ support p q then 1 else 0
  c_symm := by
    intro i j p q
    have : support p q ↔ support q p := by unfold support; omega
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h, this]
  c_parity := by
    intro i j p q h
    simp [datum] at h
  c_self := by intro i p q; simp
  c_corner := by intro i j hij; simp [hij, dn_ne hij, support]
  c_outside := by
    intro i j p q h
    by_cases hij : i = j
    · simp [hij]
    · rw [dn_ne hij, dn_ne (Ne.symm hij)] at h
      have : ¬support p q := by unfold support; omega
      simp [this]
  c_top := by
    intro i j q hq
    by_cases hij : i = j
    · simp [hij]
    · have : ¬support (datum.dn i j) q := by rw [dn_ne hij]; unfold support; omega
      simp [this]
  two_isUnit := by intro _; norm_num

/-- The constant term violates (1.31). -/
example : ¬constantTerm.Homogeneous := by
  intro hh
  have := hh true false 0 0 (by decide) (by rw [d_ne (by decide)]; norm_num)
    (by rw [d_ne (by decide)]; norm_num) (by simp [constantTerm, support])
  rw [d_ne (by decide), d_ne (by decide)] at this
  norm_num at this

/-- `Qᵢⱼ(u, v) = u³ + uv² + v³` as Brundan–Ellis parameters: only `s^{12}` and `s^{21}`. -/
def scalars : Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun i j p q => if i ≠ j ∧ p + q = 3 then 1 else 0
  s_symm := by
    intro i j p q
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h, add_comm]
  s_eq_zero := by
    intro i j p q h
    simp [datum] at h
  two_isUnit := by intro _; norm_num

theorem homogeneous : scalars.Homogeneous := by
  intro i j p q _ _ _ _ hs
  have h : i ≠ j ∧ p + q = 3 := by
    by_contra h
    exact hs (by simp [scalars, h])
  obtain ⟨hij, hpq⟩ := h
  rw [d_ne hij, d_ne (Ne.symm hij)]
  have : (p : ℤ) + q = 3 := by exact_mod_cast hpq
  linear_combination 3 * this

/-- (H) applied to `scalars.toBWW`. -/
example : ∃ Sc₀ : Scalars datum ℚ, Sc₀.Homogeneous ∧ Sc₀.toBWW = scalars.toBWW :=
  BWWScalars.Homogeneous.exists_eq_toBWW
    ((ScalarData.toBWW_homogeneous_iff scalars).mpr homogeneous)

end NonVacuity.BWWScalars
