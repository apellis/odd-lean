/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SerreClass
import OddMath.QuiverHecke.SplitComplexIso

/-!
# Proposition 11.2: the isomorphism in `Ḣ_{q,π}`

Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang, arXiv:1202.2769v2,
Theorem 5.9), as printed: for `i ≠ j` and `n = d_ij + 1`,

`⊕_{k} Π^{k|i|} P(i^{(n-2k)} j i^{(2k)}) ≅ ⊕_{k} Π^{k|i| + |i||j|} P(i^{(n-2k-1)} j i^{(2k+1)})`,

the sums over `0 ≤ 2k ≤ n` and `0 ≤ 2k + 1 ≤ n`. Here `term sy hc i j M a` is the summand
`Q^{sh a} Π^{par a} (i^a j i^{M-a}, e_a)` of `Ḣ_{q,π}`, the projective
`Π^{par a} P(i^{(a)} j i^{(M-a)})` of BE2 (`OddMath.QuiverHecke.SerreComplex.term`; its idempotent
`e_a` is `1_{i^{(a)}} ⊗ 1_j ⊗ 1_{i^{(M-a)}}`, `eIdem_eq_tailT`, `hcls_dp_mul`). With
`r = M - a`, the parity shift is `par (M - 2k) = k|i|` (`par_sub_two_mul`) and
`par (M - (2k+1)) = k|i| + |i||j|` (`par_sub_two_mul_add_one`), so `nonempty_iso_even_odd`,
the sum over even `r` of `term (M - r)` against the sum over odd `r`, is the printed statement.
The split complex of `OddMath.QuiverHecke.SerreComplex.split` gives the isomorphism
(`OddMath.QuiverHecke.SplitComplex.IsSplitK.nonempty_revSum_iso`). Its class form is
`class_even_eq_odd`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SerreComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X} {k : Type w}
  [CommRing k] {Sc : SKM.Scalars D k}

theorem cast_choose_two_two_mul (n : ℕ) : (((2 * n).choose 2 : ℕ) : ZMod 2) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Nat.choose_succ_succ', Nat.choose_one_right,
      Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast [ih]
    generalize (n : ZMod 2) = x
    revert x; decide

theorem cast_choose_two_two_mul_add_one (n : ℕ) :
    (((2 * n + 1).choose 2 : ℕ) : ZMod 2) = n := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]
  push_cast [cast_choose_two_two_mul]
  generalize (n : ZMod 2) = x
  revert x; decide

/-- The parity shift of the term with `r = 2n` is `n|i|`. -/
theorem par_sub_two_mul {i j : I} {M n : ℕ} (h : 2 * n ≤ M) :
    par D i j M (M - 2 * n) = n * D.parity i := by
  rw [par, Nat.sub_sub_self h, cast_choose_two_two_mul]
  push_cast
  rw [show ((2 : ZMod 2)) = 0 from rfl]
  ring

/-- The parity shift of the term with `r = 2n + 1` is `n|i| + |i||j|`. -/
theorem par_sub_two_mul_add_one {i j : I} {M n : ℕ} (h : 2 * n + 1 ≤ M) :
    par D i j M (M - (2 * n + 1)) = n * D.parity i + D.parity i * D.parity j := by
  rw [par, Nat.sub_sub_self h, cast_choose_two_two_mul_add_one]
  push_cast
  rw [show ((2 : ZMod 2)) = 0 from rfl]
  ring

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- **BE2 Proposition 11.2** (HW Theorem 5.9): for `i ≠ j` and `M = d_ij + 1`, in `Ḣ_{q,π}`,
`⊕_{r even} term (M - r) ≅ ⊕_{r odd} term (M - r)`, that is,
`⊕_k Π^{k|i|} P(i^{(M-2k)} j i^{(2k)}) ≅ ⊕_k Π^{k|i|+|i||j|} P(i^{(M-2k-1)} j i^{(2k+1)})`
(`par_sub_two_mul`, `par_sub_two_mul_add_one`). -/
theorem nonempty_iso_even_odd {i j : I} {M : ℕ} (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    Nonempty ((⨁ fun r : SplitComplex.terms M true => term sy hc i j M (M - r.1)) ≅
      ⨁ fun r : SplitComplex.terms M false => term sy hc i j M (M - r.1)) := by
  obtain ⟨c, h0, hs, ht⟩ := exists_scalars (D := D) (Sc := Sc) hij hM
  have h : SplitComplex.IsSplitK M (fun a _ => term sy hc i j M a) _ _ :=
    (split sy hc hij hM c h0 hs ht).isSplitK
  exact h.nonempty_revSum_iso

end OddMath.QuiverHecke.SerreComplex
