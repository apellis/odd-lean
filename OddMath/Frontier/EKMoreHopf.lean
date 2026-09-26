import OddMath.Frontier.OddLRGapsHopf
import OddMath.Frontier.EKPrimitives
import OddMath.Frontier.EKFreeCoproduct

/-!
# [EK] §1, p. 3, and §2.3, pp. 18–19: (co)commutativity and the maps `ψ₁, ψ₂, ψ₃`

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2. `Λ = Q` is the integral radical quotient at `q = −1`, `Λ′ = A` the free
algebra on `h₁, h₂, …` (`h₀ = 1`), `π : Λ′ → Λ` the quotient map.

* p. 3: "`Λ₋₁` is a Hopf superalgebra which is neither cocommutative nor commutative as a
  superalgebra" (`ek_p3_not_cocommutative_not_commutative`): `Δ` is fixed neither by the super
  flip nor by the ordinary flip, and `Λ` is neither supercommutative nor commutative.
* p. 18: "`ψ₂` … algebra involution (not a coalgebra homomorphism)" holds
  (`ek_p18_psi2_not_coalgebra`).
* p. 18: "`ψ₃` … superalgebra anti-involution (not a coalgebra homomorphism)" is **false**:
  `Δψ₃ = (ψ₃ ⊗ ψ₃)Δ` and `εψ₃ = ε` (`ek_p18_psi3_coalgebra_hom`,
  `ek_p18_psi3_printed_false`).
* p. 19: "All three of these maps lift to `Λ′` at `q = −1`": `ψ₁` lifts to the algebra
  automorphism `h_n ↦ e_n` of `Λ′` (`psi1_lift`), `ψ₂` to the algebra involution
  `h_n ↦ (−1)^{C(n+1,2)} h_n` (`psi2Free`, `psi2_lift`), and `ψ₃` to the linear involution
  `psi3Free` of `Λ′` with `psi3Free(h_n) = h_n`,
  `psi3Free(h_α h_β) = (−1)^{|α||β|} psi3Free(h_β) psi3Free(h_α)` and `π ∘ psi3Free = ψ₃ ∘ π`;
  in particular `psi3Free` preserves the radical, i.e. the defining relations (`ek_p19_psi3_lift`).
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators TensorProduct

namespace OddMath.Frontier.EKMore
open CompleteElementary (A hWord)
open EKRadicalQuotient (Q pi quotientCounit)
open EKCoideal (quotientCoproduct)
open EKAutomorphisms (psi2 psi3 s wordSign)
open EKPresentation (psi1)
open EKFreeCoproduct (W wordBasis partWord)

/-! ## p. 3: neither cocommutative nor commutative -/

/-- [EK] p. 3: `Λ₋₁` is neither (super)cocommutative nor (super)commutative. -/
theorem ek_p3_not_cocommutative_not_commutative :
    (¬ ∀ x : Q, OddLRGaps.superFlip (quotientCoproduct x) = quotientCoproduct x) ∧
    (¬ ∀ x : Q, TensorProduct.comm ℤ Q Q (quotientCoproduct x) = quotientCoproduct x) ∧
    ¬ OddLRGaps.SuperCommutativeQ ∧ ¬ (∀ x y : Q, x * y = y * x) :=
  ⟨OddLRGaps.not_superCocommutative, OddLRGaps.not_cocommutative,
    OddLRGaps.not_superCommutative_Q,
    fun hc => EKPresentationControls.noncommuting_control (hc _ _)⟩

/-! ## p. 18: coalgebra properties of `ψ₂` and `ψ₃` -/

/-- [EK] p. 18: `ψ₂` is not a coalgebra homomorphism. -/
theorem ek_p18_psi2_not_coalgebra :
    ¬ ∀ x : Q, quotientCoproduct (psi2 x) = OddLRMisc.psi2Tensor (quotientCoproduct x) :=
  fun hc => OddLRMisc.psi2_not_coalgebra (hc _)

theorem hPartition_mem (μ : YoungDiagram) :
    EKPartitionSpanning.hPartition μ ∈ EKIntegralBases.degreePiece μ.card := by
  have h := (EKIntegralBases.degreeHBasis μ.card ⟨μ, rfl⟩).2
  rwa [EKIntegralBases.degreeHBasis_apply] at h

/-- `ψ₃` preserves the counit. -/
theorem counit_psi3 (x : Q) : quotientCounit (psi3 x) = quotientCounit x := by
  induction x using EKPairingAdjoint.basis_induction EKIntegralBases.hBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb μ r =>
    rw [map_zsmul, map_zsmul, map_zsmul]
    congr 1
    rw [EKIntegralBases.hBasis_apply]
    by_cases hμ : μ.card = 0
    · have hnil : μ.rowLens = [] := by
        have hs := EKIntegralBases.rowLens_sum μ
        rw [hμ] at hs
        cases hl : μ.rowLens with
        | nil => rfl
        | cons a t =>
          have ha := μ.pos_of_mem_rowLens a (by rw [hl]; exact List.mem_cons_self)
          rw [hl, List.sum_cons] at hs
          omega
      have h1 : EKPartitionSpanning.hPartition μ = 1 := by
        rw [EKPartitionSpanning.hPartition, hnil]; rfl
      have h2 : psi3 (1 : Q) = 1 := by
        have := EKAutomorphisms.psi3_word []
        simpa [wordSign] using this
      rw [h1, h2]
    · have hd := hPartition_mem μ
      rw [EKPrimitives.counit_degree_pos (Nat.pos_of_ne_zero hμ) (EKAutomorphisms.psi3_degree hd),
        EKPrimitives.counit_degree_pos (Nat.pos_of_ne_zero hμ) hd]

/-- [EK] p. 18: `ψ₃` **is** a coalgebra homomorphism: `Δψ₃ = (ψ₃ ⊗ ψ₃)Δ` and `εψ₃ = ε`. -/
theorem ek_p18_psi3_coalgebra_hom :
    (∀ x : Q, quotientCoproduct (psi3 x) = OddLRMisc.psi3Tensor (quotientCoproduct x)) ∧
    ∀ x : Q, quotientCounit (psi3 x) = quotientCounit x :=
  ⟨OddLRMisc.psi3_coproduct, counit_psi3⟩

/-- [EK] p. 18: the printed "`ψ₃` (not a coalgebra homomorphism)" is false. -/
theorem ek_p18_psi3_printed_false :
    ¬ ∃ x : Q, quotientCoproduct (psi3 x) ≠ OddLRMisc.psi3Tensor (quotientCoproduct x) :=
  fun ⟨x, hx⟩ => hx (OddLRMisc.psi3_coproduct x)

/-! ## p. 19: lifts to `Λ′` -/

theorem pi_hWord' (α : List ℕ) : pi (hWord α) = (α.map EKElementaryQuotient.h).prod := by
  rw [hWord, map_list_prod, List.map_map]; rfl

theorem hWord_append (α β : List ℕ) : hWord (α ++ β) = hWord α * hWord β := by
  rw [hWord, hWord, hWord, List.map_append, List.prod_append]

theorem wordBasis_eq_hWord (w : W) : wordBasis w = hWord (w.toList.map (· + 1)) := by
  refine FreeMonoid.inductionOn' w ?_ ?_
  · rw [EKFreeCoproduct.wordBasis_one]; rfl
  · intro x xs ih
    rw [EKFreeCoproduct.wordBasis_mul, EKFreeCoproduct.wordBasis_of, ih, FreeMonoid.toList_of_mul,
      List.map_cons, hWord, hWord, List.map_cons, List.prod_cons]

theorem wordSign_append (α β : List ℕ) : wordSign (α ++ β) = wordSign α * wordSign β := by
  rw [wordSign, wordSign, wordSign, List.map_append, List.prod_append]

/-- Lift of `ψ₁` ([EK] p. 19): the algebra automorphism `h_n ↦ e_n` of `Λ′`. -/
theorem psi1_lift (x : A) :
    pi (CompleteChangeOfGenerators.completeToElementary x) = psi1 (pi x) :=
  (EKPresentation.psi1_pi x).symm

/-- Lift of `ψ₂` to `Λ′`: `h_n ↦ (−1)^{C(n+1,2)} h_n`. -/
def psi2Free : A →ₐ[ℤ] A := FreeAlgebra.lift ℤ (fun i => s (i + 1) • FreeAlgebra.ι ℤ i)

theorem psi2Free_h (n : ℕ) : psi2Free (CompleteElementary.h n) = s n • CompleteElementary.h n := by
  cases n with
  | zero => simp [CompleteElementary.h]
  | succ n => simp [psi2Free, CompleteElementary.h]

theorem psi2Free_hWord (α : List ℕ) : psi2Free (hWord α) = wordSign α • hWord α := by
  induction α with
  | nil => simp [hWord, wordSign]
  | cons a α ih =>
    rw [hWord, List.map_cons, List.prod_cons, map_mul, ← hWord, ih, psi2Free_h,
      smul_mul_smul_comm]
    rfl

/-- Lift of `ψ₂` ([EK] p. 19): `π ∘ psi2Free = ψ₂ ∘ π`. -/
theorem psi2_lift (x : A) : pi (psi2Free x) = psi2 (pi x) := by
  have h : (EKRadicalQuotient.piAlg.comp psi2Free : A →ₐ[ℤ] Q) =
      (psi2.toRingHom.toIntAlgHom.comp EKRadicalQuotient.piAlg) := by
    apply FreeAlgebra.hom_ext
    funext i
    have h1 := psi2Free_h (i + 1)
    have h2 := EKAutomorphisms.psi2_h (i + 1)
    simp only [Function.comp_apply, AlgHom.comp_apply]
    change pi (psi2Free (CompleteElementary.h (i + 1))) = psi2 (pi (CompleteElementary.h (i + 1)))
    rw [h1, map_zsmul]
    exact h2.symm
  exact congrArg (fun f : A →ₐ[ℤ] Q => f x) h

/-- Ordinary reversal of words in `Λ′`. -/
def revFree : A →ₐ[ℤ] Aᵐᵒᵖ := FreeAlgebra.lift ℤ (fun i => MulOpposite.op (FreeAlgebra.ι ℤ i))

def revFreeL : A →ₗ[ℤ] A := (MulOpposite.opLinearEquiv ℤ).symm.toLinearMap ∘ₗ revFree.toLinearMap

theorem revFreeL_hWord (α : List ℕ) : revFreeL (hWord α) = hWord α.reverse := by
  induction α with
  | nil => simp [revFreeL, hWord]
  | cons a α ih =>
    have hh : revFreeL (CompleteElementary.h a) = CompleteElementary.h a := by
      cases a with
      | zero => simp [revFreeL, CompleteElementary.h]
      | succ a => simp [revFreeL, revFree, CompleteElementary.h]
    have hm : ∀ x y : A, revFreeL (x * y) = revFreeL y * revFreeL x := by
      intro x y; simp [revFreeL]
    rw [hWord, List.map_cons, List.prod_cons, hm, ← hWord, ih, hh, List.reverse_cons,
      hWord_append]
    simp [hWord]

/-- Degree twist `x ↦ (−1)^{C(d+1,2)} x` on the degree-`d` part of `Λ′`. -/
def twistFree : A →ₗ[ℤ] A :=
  wordBasis.constr ℤ (fun w => s (EKFreeCoproduct.degree w) • wordBasis w)

theorem twistFree_hWord (α : List ℕ) : twistFree (hWord α) = s α.sum • hWord α := by
  rw [← EKFreeCoproduct.partWord_value, twistFree, Basis.constr_basis,
    EKFreeCoproduct.partWord_degree]

/-- Lift of `ψ₃` to `Λ′` ([EK] p. 19): degree twist after reversal after `ψ₂`. -/
def psi3Free : A →ₗ[ℤ] A := twistFree ∘ₗ revFreeL ∘ₗ psi2Free.toLinearMap

theorem psi3Free_hWord (α : List ℕ) :
    psi3Free (hWord α) = (s α.sum * wordSign α) • hWord α.reverse := by
  change twistFree (revFreeL (psi2Free (hWord α))) = _
  rw [psi2Free_hWord, map_zsmul, revFreeL_hWord, map_zsmul, twistFree_hWord, List.sum_reverse,
    smul_smul, mul_comm (wordSign α)]

theorem psi3Free_h (n : ℕ) : psi3Free (CompleteElementary.h n) = CompleteElementary.h n := by
  have h := psi3Free_hWord [n]
  simp only [hWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.sum_cons, List.sum_nil, add_zero, List.reverse_singleton, wordSign,
    EKAutomorphisms.s_square, one_smul] at h
  exact h

/-- Super anti-multiplicativity of the lift on words. -/
theorem psi3Free_mul_hWord (α β : List ℕ) :
    psi3Free (hWord α * hWord β) =
      (-1 : ℤ) ^ (α.sum * β.sum) • (psi3Free (hWord β) * psi3Free (hWord α)) := by
  rw [← hWord_append, psi3Free_hWord, psi3Free_hWord, psi3Free_hWord, smul_mul_smul_comm,
    ← hWord_append, List.reverse_append, smul_smul, List.sum_append, wordSign_append,
    EKAutomorphisms.s_add]
  congr 1
  ring

theorem psi3Free_involutive (x : A) : psi3Free (psi3Free x) = x := by
  have h : psi3Free ∘ₗ psi3Free = LinearMap.id := by
    apply wordBasis.ext
    intro w
    rw [LinearMap.comp_apply, LinearMap.id_apply, wordBasis_eq_hWord, psi3Free_hWord, map_zsmul,
      psi3Free_hWord, List.reverse_reverse, List.sum_reverse, EKAutomorphisms.wordSign_reverse,
      smul_smul]
    have hs : (s (w.toList.map (· + 1)).sum * wordSign (w.toList.map (· + 1))) *
        (s (w.toList.map (· + 1)).sum * wordSign (w.toList.map (· + 1))) = 1 := by
      calc _ = (s (w.toList.map (· + 1)).sum * s (w.toList.map (· + 1)).sum) *
            (wordSign (w.toList.map (· + 1)) * wordSign (w.toList.map (· + 1))) := by ring
        _ = 1 := by rw [EKAutomorphisms.s_square, EKAutomorphisms.wordSign_square, mul_one]
    rw [hs, one_smul]
  exact congrArg (fun f : A →ₗ[ℤ] A => f x) h

/-- `π ∘ psi3Free = ψ₃ ∘ π`. -/
theorem psi3_lift (x : A) : pi (psi3Free x) = psi3 (pi x) := by
  have h : (EKRadicalQuotient.piAlg.toLinearMap ∘ₗ psi3Free : A →ₗ[ℤ] Q) =
      (psi3.toLinearMap ∘ₗ EKRadicalQuotient.piAlg.toLinearMap) := by
    apply wordBasis.ext
    intro w
    rw [LinearMap.comp_apply, LinearMap.comp_apply, wordBasis_eq_hWord, psi3Free_hWord]
    change pi _ = psi3 (pi _)
    rw [map_zsmul, pi_hWord', pi_hWord']
    exact (EKAutomorphisms.psi3_word _).symm
  exact congrArg (fun f : A →ₗ[ℤ] Q => f x) h

/-- [EK] p. 19: `ψ₃` lifts to `Λ′`: a linear involution of `Λ′` fixing every `h_n`, super
anti-multiplicative on words, compatible with `π`, and preserving the radical. -/
theorem ek_p19_psi3_lift :
    (∀ n, psi3Free (CompleteElementary.h n) = CompleteElementary.h n) ∧
    (∀ α β : List ℕ, psi3Free (hWord α * hWord β) =
      (-1 : ℤ) ^ (α.sum * β.sum) • (psi3Free (hWord β) * psi3Free (hWord α))) ∧
    (∀ x, psi3Free (psi3Free x) = x) ∧ (∀ x, pi (psi3Free x) = psi3 (pi x)) ∧
    ∀ x ∈ EKRadicalQuotient.radical, psi3Free x ∈ EKRadicalQuotient.radical := by
  refine ⟨psi3Free_h, psi3Free_mul_hWord, psi3Free_involutive, psi3_lift, fun x hx => ?_⟩
  have h0 : pi x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have h1 : pi (psi3Free x) = 0 := by rw [psi3_lift, h0, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

end OddMath.Frontier.EKMore
