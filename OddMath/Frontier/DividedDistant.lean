import OddMath.Frontier.AllRankDivided

/-! # Actual all-rank distant divided anticommutation
EKL arXiv:1111.1320v1, Proposition 2.1 (2.9), p.4.
All generators, including spectators and repeated letters, are retained.
-/
namespace OddMath.Frontier.DividedDistant
open OddMath.SkewPolynomial (SkewPolynomial generator)
open PbwL2 PbwL3 AllRankDivided
variable {n : ℕ}

/-- Left-generator induction on the actual model, via the genuine presentation.
The strengthened free-algebra predicate handles arbitrary products, not just letters. -/
theorem generator_induction {m : ℕ} (P : SkewPolynomial m → Prop)
    (h1 : P 1) (ha : ∀ f g, P f → P g → P (f+g))
    (hz : ∀ (c : ℤ) f, P f → P (c • f))
    (hx : ∀ k f, P f → P (generator k * f)) (f : SkewPolynomial m) : P f := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective m f
  induction x using Quotient.inductionOn' with
  | h w =>
      change P (evalAlg m w)
      have hh : ∀ g, P g → P (evalAlg m w * g) := by
        induction w using FreeAlgebra.induction with
        | grade0 r =>
            intro g hg
            rw [AlgHom.commutes]
            simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using hz r g hg
        | grade1 k =>
            intro g hg
            rw [evalAlg_ι]
            exact hx k g hg
        | add a b ia ib =>
            intro g hg
            rw [map_add, add_mul]
            exact ha _ _ (ia g hg) (ib g hg)
        | mul a b ia ib =>
            intro g hg
            rw [map_mul, mul_assoc]
            exact ia _ (ib g hg)
      simpa only [mul_one] using hh 1 h1

/-- Separation makes the two active pairs disjoint, in either orientation. -/
theorem separated_endpoints (i j : Fin (n+1))
    (h : i.val+1<j.val ∨ j.val+1<i.val) :
    i.castSucc ≠ j.castSucc ∧ i.castSucc ≠ j.succ ∧
      i.succ ≠ j.castSucc ∧ i.succ ≠ j.succ := by
  constructor
  · intro e; have := congrArg Fin.val e; simp only [Fin.coe_castSucc] at this; omega
  constructor
  · intro e; have := congrArg Fin.val e
    simp only [Fin.coe_castSucc, Fin.val_succ] at this; omega
  constructor
  · intro e; have := congrArg Fin.val e
    simp only [Fin.coe_castSucc, Fin.val_succ] at this; omega
  · intro e; have := congrArg Fin.val e; simp only [Fin.val_succ] at this; omega

/-- The anticommutator passes through every generator with the unsigned
composite permutation. The spectator branch is universally quantified. -/
theorem distant_generator_recursion (i j : Fin (n+1))
    (h : i.val+1<j.val ∨ j.val+1<i.val) (k : Fin (n+2))
    (f : SkewPolynomial (n+2)) :
    divided i (divided j (generator k * f)) +
      divided j (divided i (generator k * f)) =
    generator (Equiv.swap i.castSucc i.succ (Equiv.swap j.castSucc j.succ k)) *
      (divided i (divided j f) + divided j (divided i f)) := by
  obtain ⟨hll, hlr, hrl, hrr⟩ := separated_endpoints i j h
  by_cases hki : k = i.castSucc
  · subst k
    simp only [divided_spectator_mul j _ hll hlr, map_neg, neg_mul,
      divided_left_mul, map_sub,
      divided_spectator_mul j _ hrl hrr,
      Equiv.swap_apply_of_ne_of_ne hll hlr, Equiv.swap_apply_left]
    noncomm_ring
  by_cases hki' : k = i.succ
  · subst k
    simp only [divided_spectator_mul j _ hrl hrr, map_neg, neg_mul,
      divided_right_mul, map_sub,
      divided_spectator_mul j _ hll hlr,
      Equiv.swap_apply_of_ne_of_ne hrl hrr, Equiv.swap_apply_right]
    noncomm_ring
  by_cases hkj : k = j.castSucc
  · subst k
    simp only [divided_spectator_mul i _ hll.symm hrl.symm, map_neg, neg_mul,
      divided_left_mul, map_sub,
      divided_spectator_mul i _ hlr.symm hrr.symm,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hlr.symm hrr.symm]
    noncomm_ring
  by_cases hkj' : k = j.succ
  · subst k
    simp only [divided_spectator_mul i _ hlr.symm hrr.symm, map_neg, neg_mul,
      divided_right_mul, map_sub,
      divided_spectator_mul i _ hll.symm hrl.symm,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hll.symm hrl.symm]
    noncomm_ring
  · simp only [divided_spectator_mul j _ hkj hkj',
      divided_spectator_mul i _ hki hki', map_neg, neg_mul,
      Equiv.swap_apply_of_ne_of_ne hkj hkj', Equiv.swap_apply_of_ne_of_ne hki hki']
    noncomm_ring

/-- EKL Proposition 2.1 (2.9) on the actual operators, in every rank. -/
theorem divided_distant (i j : Fin (n+1))
    (h : i.val+1<j.val ∨ j.val+1<i.val) (f : SkewPolynomial (n+2)) :
    divided i (divided j f) + divided j (divided i f) = 0 := by
  apply generator_induction (fun f => divided i (divided j f) + divided j (divided i f) = 0)
  · simp only [divided_one, map_zero, add_zero]
  · intro a b ha hb
    simp only [map_add]
    calc
      _ = (divided i (divided j a) + divided j (divided i a)) +
          (divided i (divided j b) + divided j (divided i b)) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  · intro c a ha
    simp only [map_smul, ← smul_add, ha, smul_zero]
  · intro k a ha
    rw [distant_generator_recursion i j h, ha, mul_zero]

theorem divided_distant_neg (i j : Fin (n+1))
    (h : i.val+1<j.val ∨ j.val+1<i.val) (f : SkewPolynomial (n+2)) :
    divided i (divided j f) = -divided j (divided i f) :=
  eq_neg_of_add_eq_zero_left (divided_distant i j h f)

theorem divided_distant_comp (i j : Fin (n+1))
    (h : i.val+1<j.val ∨ j.val+1<i.val) :
    (divided i).comp (divided j) + (divided j).comp (divided i) = 0 := by
  apply LinearMap.ext
  intro f
  exact divided_distant i j h f

/-- Actual downstream kernel preservation, with no assumed divided relation. -/
theorem divided_kernel_preserved (i j : Fin (n+1))
    (h : i.val+1<j.val ∨ j.val+1<i.val) (f : SkewPolynomial (n+2))
    (hf : divided i f = 0) : divided i (divided j f) = 0 := by
  rw [divided_distant_neg i j h, hf, map_zero, neg_zero]

end OddMath.Frontier.DividedDistant
