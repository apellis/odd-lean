/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.Transfer
import OddMath.CoveringQuantum.UDot.TensorGram.MixedIntegration
import OddMath.CoveringQuantum.UDot.ContextualCommutator
import OddMath.CoveringQuantum.UDot.ContextualExchange
import OddMath.CoveringQuantum.UDot.SesquilinearForm
import Categorification.QuantumGroup.UDotSymm
import Categorification.QuantumGroup.UDotOmega
import Categorification.QuantumGroup.UDotSerreF

/-!
# The forms of Brundan–Ellis and of Khovanov–Lauda on `U̇` agree for even data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 10.1 and
A. D. Lauda, M. Khovanov, KL III (arXiv:0807.3250), Prop. 2.2: when every colour is even, the
form `(E_a 1_μ, E_b 1_μ)` on mixed words of `U̇_{q,π}`, specialized at `π = 1`
(`specializeOne`), is the KL III form `B ℓ (E_a 1_λ) (E_b 1_λ)` with `ℓ i = ⟨hᵢ, μ⟩`
(`specializeOne_wordForm`). Both forms satisfy the same transfer rule for a letter
(`wordForm_cons_E`, `wordForm_cons_F`, `B_rhoE`), the same commutation rule for `E_i F_j`
(`sesquilinearForm_context_EF`, `φ_comm`) and agree on positive words (`specializeOne_form`), so
the comparison follows by normal ordering (`normal_induction`). No change of the variable `q` is
needed: both are Lusztig's conventions at `v = q⁻¹`.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open OddMath.CoveringQuantum OddMath.CoveringQuantum.UDot.GenericTensor
  OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram Categorification.QuantumGroup.UDot

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (R : CoveringQuantum.RootDatum I X)

/-- The KL III weight functional `ℓ i = ⟨hᵢ, μ⟩` of `μ`. -/
def ell (μ : X) : I → ℤ := fun i => R.h i μ

/-- The KL III form on `'U 1_λ` for the weight `μ`, with `q = qK` and `(θᵢ, θᵢ) = (1 - qᵢ²)⁻¹`. -/
def klForm (μ : X) :=
  B (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ)

omit [DecidableEq I] [DecidableEq X] in
theorem A_catCartan (i j : I) : A (catCartan R) i j = R.h i (R.α j) := by
  have h := compatible_catCartan R i j
  rw [CoveringQuantum.RootDatum.toSKM_α, CoveringQuantum.RootDatum.toSKM_h] at h
  exact h.symm

omit [DecidableEq I] [DecidableEq X] in
/-- The KL III left weight of `E_t 1_λ` is the left weight `μ + |t|` of the mixed word. -/
theorem wl_ell (μ : X) (t : List (Bool × I)) (i : I) :
    wl (catCartan R) (ell R μ) t i = R.h i (μ + shift R t) := by
  induction t with
  | nil => simp [wl_nil, ell, shift]
  | cons l t ih =>
    obtain ⟨b, j⟩ := l
    simp only [wl_cons]
    rw [ih, A_catCartan]
    cases b <;> simp only [shift, UDot.halfRoot, sgn_true, sgn_false, ite_true, ite_false,
      Bool.false_eq_true, map_add, map_neg] <;> ring

theorem specializeOne_qp (z : ℤ) :
    specializeOne (UDot.qp Coefficients.q z) = qp KL3.qK z :=
  specializeOne_qUnit_zpow z

/-- At `π = 1` the covering quantum integers are the ordinary ones. -/
theorem qpInt_one_eq_qbr {K : Type*} [Field K] (t : Kˣ)
    (ht : (t : K) - ((t⁻¹ : Kˣ) : K) ≠ 0) (n : ℤ) : qpInt t (1 : K) n = qbr t n := by
  have hnat : ∀ m : ℕ, qpInt t (1 : K) m = qbr t m := by
    intro m
    rw [qpInt_ofNat, qpNat_one_eq_qInt, qbr, eq_div_iff ht]
    have h := LieLean.QuantumGroup.qInt_mul_sub (v := (t : K)) m
    rw [inv_pow] at h
    simp only [zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    linear_combination h
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact hnat m
  · rw [qpInt_neg (one_pow 2), one_pow, one_mul, hnat, qbr_neg]

omit [DecidableEq I] [DecidableEq X] in
theorem specializeOne_bar_qpInt (i : I) (n : ℤ) :
    specializeOne (Coefficients.bar (qpInt (R.qi Coefficients.q i) (1 : Coefficients.Ring) n)) =
      qbr (qi (catCartan R) KL3.qK i) n := by
  have hbq : Units.map Coefficients.bar.toMonoidHom Coefficients.q = Coefficients.q⁻¹ :=
    Units.ext (by rw [Units.coe_map]; exact Coefficients.bar_q)
  have hqi : Units.map Coefficients.bar.toMonoidHom (R.qi Coefficients.q i) =
      (R.qi Coefficients.q i)⁻¹ := by
    simp only [SuperCartanDatum.qi, map_pow, hbq, inv_pow]
  rw [map_qpInt, hqi, map_one, qpInt_inv (one_pow 2), one_pow, one_mul]
  change specializeOne.toRingHom _ = _
  have hsq : Units.map specializeOne.toRingHom.toMonoidHom (R.qi Coefficients.q i) =
      qi (catCartan R) KL3.qK i := by
    rw [qi, di_catCartan, zpow_natCast, SuperCartanDatum.qi, map_pow]
    congr 1
    exact specializeOne_qUnit
  rw [map_qpInt, hsq, map_one]
  exact qpInt_one_eq_qbr _ (qi_sub_inv_ne_zero (catCartan R) KL3.qK KL3.hqK i) n

/-- For even data, `ψ` fixes every mixed word. -/
theorem psiModified_algebraWord (heven : ∀ i, R.parity i = 0) (μ : X)
    (w : List (Bool × I)) : psiModified R (algebraWord R μ w) = algebraWord R μ w := by
  induction w with
  | nil => apply Subtype.ext; simp [algebraWord]
  | cons g w ih =>
    rw [algebraWord, psiModified_mul, ih]
    congr 1
    apply Subtype.ext
    obtain ⟨b, i⟩ := g
    cases b <;> simp [UDot.halfGen, CoveringQuantum.RootDatum.parl, heven]

/-- The comparison on positive words: both are the half form. -/
theorem specializeOne_wordForm_posW (μ : X) (u v : List I) :
    specializeOne (wordForm R μ (posW u) (posW v)) = klForm R μ (ew (posW u)) (ew (posW v)) := by
  have hp : ∀ w : List I, algebraWord R μ (posW w) =
      UDot.positiveHalf R Coefficients.q Coefficients.pi μ
        (R.toSerreF Coefficients.q Coefficients.pi (PreF.monomial Coefficients.Ring w)) :=
    fun w => (UDot.PositiveComparison.algebraWord_pos_eq R μ w).trans
      (UDot.NormalizedMixedComparison.word_positive R w μ)
  have hk : ∀ w : List I,
      (ew (posW w) : Free (RatFunc ℚ) I) =
        posF (Categorification.QuantumGroup.PreF.word (FreeMonoid.ofList w)) := fun w => by
    rw [posF_word, FreeMonoid.toList_ofList]
  rw [wordForm, hp, hp, sesquilinearForm_positiveHalf, UDot.GenericVerma.halfBar_monomial,
    SuperCartanDatum.serreForm_toSerreF, specializeOne_form, hk, hk, klForm, B_posF_posF]

/-- The comparison on `(F_c E_u 1_μ, E_v 1_μ)`, moving the `F`'s to the right. -/
theorem specializeOne_wordForm_negW_posW (heven : ∀ i, R.parity i = 0) (μ : X)
    (c u v : List I) :
    specializeOne (wordForm R μ (negW c ++ posW u) (posW v)) =
      klForm R μ (ew (negW c ++ posW u)) (ew (posW v)) := by
  induction c generalizing v with
  | nil => simpa using specializeOne_wordForm_posW R μ u v
  | cons j c ih =>
    have h := ih (j :: v)
    show specializeOne (wordForm R μ ((false, j) :: (negW c ++ posW u)) (posW v)) =
      klForm R μ (ew ((false, j) :: (negW c ++ posW u))) (ew (posW v))
    rw [wordForm_cons_F R μ j (heven j), map_mul, specializeOne_qp,
      show ((true, j) :: posW v : List (Bool × I)) = posW (j :: v) from rfl, h, klForm,
      B_rhoE, rhoE_ew, map_smul, smul_eq_mul]
    simp only [Bool.not_false]
    congr 2
    rw [wl_ell, di_catCartan, sgn_false]
    ring

theorem specializeOne_wordForm_comm_self (heven : ∀ i, R.parity i = 0) (μ : X)
    (a b : List (Bool × I)) (i : I)
    (h1 : specializeOne (wordForm R μ (a ++ (false, i) :: (true, i) :: b) []) =
      φ (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ)
        (ew (a ++ (false, i) :: (true, i) :: b)))
    (h2 : specializeOne (wordForm R μ (a ++ b) []) =
      φ (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ) (ew (a ++ b))) :
    specializeOne (wordForm R μ (a ++ (true, i) :: (false, i) :: b) []) =
      φ (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ)
          (ew (a ++ (false, i) :: (true, i) :: b)) +
        qbr (qi (catCartan R) KL3.qK i) (wl (catCartan R) (ell R μ) b i) *
          φ (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ) (ew (a ++ b)) := by
  have h := sesquilinearForm_context_EF R μ a b i
  have hp : R.pii Coefficients.pi i = 1 := by simp [SuperCartanDatum.pii, heven i]
  rw [hp, one_mul, sub_eq_iff_eq_add, mixed_word_physical_weight] at h
  change wordForm R μ _ [] = _ * wordForm R μ (a ++ b) [] + wordForm R μ _ [] at h
  rw [h, map_add, map_mul, h1, h2, specializeOne_bar_qpInt, wl_ell]
  ring

theorem specializeOne_wordForm_comm_ne (heven : ∀ i, R.parity i = 0) (μ : X)
    (a b : List (Bool × I)) (i j : I) (hij : i ≠ j)
    (h1 : specializeOne (wordForm R μ (a ++ (false, j) :: (true, i) :: b) []) =
      φ (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ)
        (ew (a ++ (false, j) :: (true, i) :: b))) :
    specializeOne (wordForm R μ (a ++ (true, i) :: (false, j) :: b) []) =
      φ (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ)
        (ew (a ++ (false, j) :: (true, i) :: b)) := by
  have h := sesquilinearForm_context_EF_ne R μ a b i j hij
  simp only [heven, mul_zero, ZMod.val_zero, pow_zero, one_mul] at h
  change wordForm R μ _ [] = wordForm R μ _ [] at h
  rw [h, h1]

/-- The comparison on `(E_w 1_μ, 1_μ)`: both are the functional `φ`. -/
theorem specializeOne_wordForm_nil (heven : ∀ i, R.parity i = 0) (μ : X)
    (w : List (Bool × I)) :
    specializeOne (wordForm R μ w []) =
      φ (catCartan R) KL3.qK (KL3.cK (catCartan R)) (ell R μ) (ew w) := by
  induction w using normal_induction with
  | hN c b =>
    have h := specializeOne_wordForm_negW_posW R heven μ c b []
    rw [posW_nil, ew_nil] at h
    rw [h, klForm, B_symm, B_one_left]
  | hS a i j b h1 h2 =>
    rw [φ_comm]
    by_cases hij : j = i
    · subst hij
      simp only [↓reduceIte]
      exact specializeOne_wordForm_comm_self R heven μ a b _ h1 h2
    · simp only [hij, ↓reduceIte, add_zero]
      exact specializeOne_wordForm_comm_ne R heven μ a b i j (Ne.symm hij) h1

/-- **The forms agree.** For even data, the Brundan–Ellis form on mixed words, specialized at
`π = 1`, is the KL III form: `(E_a 1_μ, E_b 1_μ)|_{π=1} = B ℓ (E_a 1_λ) (E_b 1_λ)`. -/
theorem specializeOne_wordForm (heven : ∀ i, R.parity i = 0) (μ : X)
    (a b : List (Bool × I)) :
    specializeOne (wordForm R μ a b) = klForm R μ (ew a) (ew b) := by
  induction a generalizing b with
  | nil =>
    have hs : wordForm R μ [] b = wordForm R μ b [] := by
      rw [wordForm, sesquilinearForm_psi_comm, psiModified_algebraWord R heven,
        psiModified_algebraWord R heven]
    rw [hs, specializeOne_wordForm_nil R heven, klForm, ew_nil, B_one_left]
  | cons l a ih =>
    obtain ⟨s, i⟩ := l
    cases s
    · rw [wordForm_cons_F R μ i (heven i), map_mul, ih, specializeOne_qp, klForm,
        B_rhoE, rhoE_ew, map_smul, smul_eq_mul]
      simp only [Bool.not_false]
      congr 2
      rw [wl_ell, di_catCartan, sgn_false]
      ring
    · rw [wordForm_cons_E R μ i, map_mul, ih, specializeOne_qp, klForm,
        B_rhoE, rhoE_ew, map_smul, smul_eq_mul]
      simp only [Bool.not_true]
      congr 2
      rw [wl_ell, di_catCartan, sgn_true]
      ring

end OddMath.SKM.EvenBridge
