import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterQCorrection
import OddMath.QuiverHecke.SwappedAssembly.QuadNe
import Mathlib.Algebra.Category.ModuleCat.Basic
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory OddMath.SKM Finset
open OddMath.QuiverHecke.SwappedAssembly
open RepeatedOuterQCorrection

section General
universe u
variable {k I X : Type u} [CommRing k] [AddCommGroup X]
  {D : Datum I X} (Sc : Scalars D k)
  {C : Type*} [Category C] [Preadditive C] [Linear k C] {V : C}

example (A x y z : End V) (i j : I)
    (hxz : x*z = zsign k (D.parity i) • (z*x))
    (hzy : z*y = zsign k (D.parity i*D.parity j) • (y*z))
    (hA0 : D.parity i = 0 → A*(x-z) = 1)
    (hA1 : D.parity i = 1 → A*(x*x-z*z) = x-z) :
    zsign k (D.parity i*D.parity j) •
        (A*(ProbeReservoir.qExpr Sc x y i j - ProbeReservoir.qExpr Sc z y i j)) =
      (∑ a ∈ range (D.dn i j),
        (zsign k (D.parity i*(D.parity j+a))*(Sc.t i j : k)) •
          (x^(D.dn i j-1-a)*z^a)) +
      ∑ b ∈ Ioo 0 (D.dn i j), ∑ c ∈ Ioo 0 (D.dn j i), ∑ a ∈ range b,
        (zsign k (D.parity i*(D.parity j+a))*Sc.s i j b c) •
          (x^(b-1-a)*y^c*z^a) :=
  qExpr_correction Sc A x y z i j hxz hzy hA0 hA1

example (x y z : End V) (i j : I) (hd : D.d i j = 0) :
    ProbeReservoir.qExpr Sc x y i j - ProbeReservoir.qExpr Sc z y i j = 0 :=
  qExpr_disconnected_difference Sc x y z i j hd

/-- The literal chronological monomial in CrossBraid, independently of qExpr. -/
example (x y z : End V) (a b c : ℕ) :
    x^(b-1-a)*y^c*z^a =
      ProbeReservoir.compPow z a ≫ ProbeReservoir.compPow y c ≫
        ProbeReservoir.compPow x (b-1-a) := by
  simp only [ProbeReservoir.compPow_eq_pow, End.mul_def]
end General

namespace NonVacuity.RepeatedOuterQCorrection
/-- An even affine rank-two datum, with a nonzero interior coefficient. -/
def datum : Datum Bool ℤ where
  cd := {
    root := fun i => if i then -1 else 1
    coroot := fun i => (if i then -2 else 2) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    coroot_root_self := by intro i; cases i <;> norm_num }
  isGCM := {
    diag := by intro i; cases i <;> norm_num [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j h
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => 0
  even_of_odd := by intros i j h; exact False.elim (zero_ne_one h)

def scalars : Scalars datum (ZMod 9) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 1
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := by intros i j p q h; simp [datum] at h
  two_isUnit := by rintro ⟨i, hi⟩; simp [datum] at hi

/-- Apply the headline to a nonzero categorical End algebra over a nonfield,
with a nonzero interior term. All dot and denominator hypotheses are discharged. -/
example :
    ProbeReservoir.qExpr scalars (1 : End (ModuleCat.of (ZMod 9) (ZMod 9))) 1 false true -
      ProbeReservoir.qExpr scalars 0 1 false true = 1 + 1 := by
  have h := qExpr_correction scalars
    (1 : End (ModuleCat.of (ZMod 9) (ZMod 9))) 1 1 0 false true
    (by simp [datum]) (by simp)
    (by intro _; simp) (by intro h; simp [datum] at h)
  have hI : Ioo (0 : ℕ) 2 = {1} := by decide
  simpa [datum, Datum.dn, Datum.d, Datum.h, Datum.α, zsign, scalars,
    Finset.sum_range_succ, hI] using h

/-- Odd middle dots need not commute with the right outer dot. Even supported
powers, rather than the dots themselves, commute. -/
example (n : ℕ) :
    let x : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, -2]
    let z : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![2/3, -1/3; -1/3, -2/3]
    zsign ℚ (1*1) • (A*((1:ℚ) • ((x^(2*n)-z^(2*n))*x^2))) =
      ∑ a ∈ range (2*n), (zsign ℚ (1*(1+a))*(1:ℚ)) •
        (x^(2*n-1-a)*x^2*z^a) := by
  dsimp only
  apply weighted_middle (pi := 1) (pj := 1)
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [zsign, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [zsign, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h; exact False.elim (one_ne_zero h)
  · intro _
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · intro _; exact ⟨n, by omega⟩
  · intro _; exact ⟨1, rfl⟩

example : (let y : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, -2]
    let z : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
    z*y ≠ y*z) := by
  dsimp only
  intro h
  have he := congrArg (fun M => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at he
end NonVacuity.RepeatedOuterQCorrection

#print axioms qExpr_correction
#print axioms supported_middle_commute
#print axioms weighted_middle

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterQCorrection
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == owner then
      for name in env.header.moduleData[i]!.constNames do
        count := count + 1
        if name.getRoot == `_private then
          privateCount := privateCount + 1
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
  if count == 0 then
    throwError "Missing owned module {owner}"
  logInfo m!"{owner}: audited {count} declarations ({privateCount} private); standard axioms only"
