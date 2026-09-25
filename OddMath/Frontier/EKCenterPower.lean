import OddMath.Frontier.EKCenterPowerControls
import OddMath.Frontier.EKPresentation
import Mathlib.Algebra.DualNumber

/-! EK 1107.5610v2 Proposition 3.4 (printed pp25–26), integral q = -1, in the
actual radical quotient `Q`.

`p k := (mBasis k (k)).val` is the integral dual (under `pairingEquiv`) of the
one-row complete element `h_(k)`.  Main theorem `center_iff`:
for every `k ≥ 1`, `(∀ y : Q, p k * y = y * p k) ↔ Even k`.

Proof route (not the source's route):
* even `k`: the functional `x ↦ ⟨x, p k⟩` equals `x ↦ snd (ψ x)` for the ring
  homomorphism `ψ : Q → ℤ[ε]`, `h_k ↦ ε`, other positive `h_n ↦ 0` (it kills the
  source relations because `k` is even).  Then the coproduct expansion of
  `⟨P*Y, w⟩ - ⟨Y*P, w⟩` has all crossing signs `+1` on the support and the
  complementary-split involution matches the two sums.
* odd `k ≥ 3`: `⟨h_k h_1, p*h_1⟩ = 1 ≠ -1 = ⟨h_k h_1, h_1*p⟩`.
* `k = 1`: control `p1 * h2 ≠ h2 * p1`. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKCenterPower
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient EKPairingMatrices
open EKDualBases EKIntegralBases DegreeShapes
open EKPartitionSpanning (hPartition)
open EKCenterPowerControls (pairing_mul_word pairing_mul_two pairing_h_two)

local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- The one-row shape `(k)`. -/
def rowShape (k : ℕ) : DegreeShape k :=
  ⟨YoungDiagram.ofRowLens [k] (List.sorted_singleton k),
    by rw [EKPartitionSpanning.card_ofRowLens]; simp⟩

theorem rowShape_rows (k : ℕ) (hk : 0 < k) : (rowShape k).val.rowLens = [k] :=
  YoungDiagram.rowLens_ofRowLens_eq_self (hw := List.sorted_singleton k) (by simp [hk])

/-- `p_k = m_(k)`, the integral dual of `h_(k)`. -/
def p (k : ℕ) : Q := (mBasis k (rowShape k)).val

theorem rows_iff (k : ℕ) (hk : 0 < k) (μ : YoungDiagram) :
    μ.rowLens = [k] ↔ μ = (rowShape k).val := by
  constructor
  · intro h
    apply YoungDiagram.equivListRowLens.injective
    apply Subtype.ext
    change μ.rowLens = (rowShape k).val.rowLens
    rw [h, rowShape_rows k hk]
  · rintro rfl; exact rowShape_rows k hk

/-! ### Degree orthogonality and the pairing against `p k` -/

theorem orth {a b : ℕ} (hab : a ≠ b) {x y : Q} (hx : x ∈ degreePiece a)
    (hy : y ∈ degreePiece b) : quotientPairing x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [quotientPairing_pi]
      exact pairing_degree_mismatch v.val w.val (by rw [v.property, w.property]; exact hab)
    | zero => simp
    | add y z _ _ h1 h2 => simp [h1, h2]
    | smul n y _ h1 => simp only [map_zsmul, h1, smul_zero]
  | zero => simp
  | add x z _ _ h1 h2 => simp [h1, h2]
  | smul n x _ h1 => simp only [map_zsmul, LinearMap.smul_apply, h1, smul_zero]

theorem hPartition_eq (μ : YoungDiagram) : hPartition μ = pi (hWord μ.rowLens) := by
  simp only [hPartition, hWord, map_list_prod, List.map_map]
  rfl

theorem pi_hWord_mem (α : List ℕ) : pi (hWord α) ∈ degreePiece α.sum := by
  rw [pi_hWord, degreePiece_eq_hPartition_span]
  exact word_mem_partitionPiece false α

theorem hPartition_mem (μ : YoungDiagram) : hPartition μ ∈ degreePiece μ.card := by
  rw [hPartition_eq, ← rowLens_sum]
  exact pi_hWord_mem _

open Classical in
theorem pair_hPartition_p (k : ℕ) (μ : YoungDiagram) :
    quotientPairing (hPartition μ) (p k) = if μ = (rowShape k).val then 1 else 0 := by
  by_cases hc : μ.card = k
  · have he := h_m k ⟨μ, hc⟩ (rowShape k)
    by_cases hμ : μ = (rowShape k).val
    · rw [if_pos (Subtype.ext hμ)] at he
      rw [if_pos hμ]; exact he
    · rw [if_neg (fun h => hμ (congrArg Subtype.val h))] at he
      rw [if_neg hμ]; exact he
  · rw [if_neg]
    · exact orth hc (hPartition_mem μ) (mBasis k (rowShape k)).property
    · intro he; apply hc; rw [he]; exact (rowShape k).property

/-! ### The dual-number character `ψ` (even `k`) -/

/-- `ψ_k : A → ℤ[ε]`, `h_k ↦ ε`, every other positive `h_n ↦ 0`. -/
def psi (k : ℕ) : A →ₐ[ℤ] DualNumber ℤ :=
  FreeAlgebra.lift ℤ (fun n : ℕ => if n + 1 = k then DualNumber.eps else 0)

theorem psi_h (k n : ℕ) :
    psi k (CompleteElementary.h n) = if n = 0 then 1 else if n = k then DualNumber.eps else 0 := by
  cases n with
  | zero => simp [CompleteElementary.h]
  | succ n => simp [CompleteElementary.h, psi]

theorem psi_relator (k : ℕ) (hk : Even k) (r : A) (hr : EKPresentation.Relator r) :
    psi k r = 0 := by
  cases hr with
  | even a b hab => simp [mul_comm]
  | odd a b hb hab =>
    have hk2 := Nat.even_iff.mp hk
    have hab2 := Nat.odd_iff.mp hab
    rcases Nat.even_or_odd a with ha | ha
    · have ha2 := Nat.even_iff.mp ha
      have h1 : psi k (CompleteElementary.h b) = 0 := by
        rw [psi_h, if_neg (by omega), if_neg (by omega)]
      have h2 : psi k (CompleteElementary.h (a + 1)) = 0 := by
        rw [psi_h, if_neg (by omega), if_neg (by omega)]
      simp [h1, h2]
    · simp only [map_sub, map_add, map_mul, map_zsmul, ha.neg_one_pow, neg_smul, one_smul, map_neg]
      ring

theorem psi_relIdeal (k : ℕ) (hk : Even k) (r : A) (hr : r ∈ EKPresentation.relIdeal) :
    psi k r = 0 := by
  rw [EKPresentation.relIdeal, EKPresentation.relTwoSided, TwoSidedIdeal.mem_asIdeal] at hr
  induction hr using TwoSidedIdeal.span_induction with
  | mem x hx => exact psi_relator k hk x hx
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

theorem psi_radical (k : ℕ) (hk : Even k) (x : A) (hx : x ∈ radical) : psi k x = 0 := by
  have h0 : pi x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have h1 : EKPresentation.toQ (EKPresentation.mk x) = EKPresentation.toQ 0 := by
    rw [EKPresentation.toQ_mk, map_zero]; exact h0
  have h2 := EKPresentation.toQ_bijective.1 h1
  exact psi_relIdeal k hk x (Ideal.Quotient.eq_zero_iff_mem.mp h2)

def psiQ (k : ℕ) (hk : Even k) : Q →+* DualNumber ℤ :=
  Ideal.Quotient.lift radical (psi k).toRingHom (fun x hx => psi_radical k hk x hx)

theorem psiQ_pi (k : ℕ) (hk : Even k) (x : A) : psiQ k hk (pi x) = psi k x := rfl

def delta (k : ℕ) (hk : Even k) : Q →ₗ[ℤ] ℤ :=
  (TrivSqZeroExt.sndHom ℤ ℤ).comp (psiQ k hk).toIntAlgHom.toLinearMap

theorem delta_apply (k : ℕ) (hk : Even k) (q : Q) : delta k hk q = (psiQ k hk q).snd := rfl

theorem psi_list (k : ℕ) (ℓ : List ℕ) (hpos : ∀ a ∈ ℓ, 0 < a) :
    (ℓ.map (fun n => psi k (CompleteElementary.h n))).prod =
      if ℓ = [] then 1 else if ℓ = [k] then DualNumber.eps else 0 := by
  induction ℓ with
  | nil => simp
  | cons a t ih =>
    have ha : 0 < a := hpos a (by simp)
    rw [List.map_cons, List.prod_cons, ih (fun b hb => hpos b (by simp [hb])), psi_h k a,
      if_neg (by omega)]
    by_cases hak : a = k
    · subst hak
      by_cases ht : t = []
      · simp [ht]
      · by_cases htk : t = [a]
        · simp [htk, DualNumber.eps_mul_eps]
        · simp [ht, htk]
    · simp [hak]

theorem delta_hWord (k : ℕ) (hk : Even k) (α : List ℕ) (hpos : ∀ a ∈ α, 0 < a) :
    delta k hk (pi (hWord α)) = if α = [k] then 1 else 0 := by
  rw [delta_apply]
  rw [psiQ_pi, hWord, map_list_prod, List.map_map]
  change ((α.map (fun n => psi k (CompleteElementary.h n))).prod).snd = _
  rw [psi_list k α hpos]
  split_ifs with h1 h2 h2 <;> simp_all

theorem delta_eq (k : ℕ) (hk0 : 0 < k) (hk : Even k) :
    delta k hk = quotientPairing.flip (p k) := by
  apply (hBasis).ext
  intro μ
  rw [hBasis_apply, LinearMap.flip_apply, pair_hPartition_p, hPartition_eq,
    delta_hWord k hk _ (fun a ha => μ.pos_of_mem_rowLens a ha)]
  by_cases hμ : μ = (rowShape k).val
  · rw [if_pos hμ, if_pos ((rows_iff k hk0 μ).mpr hμ)]
  · rw [if_neg hμ, if_neg (fun h => hμ ((rows_iff k hk0 μ).mp h))]

/-- Even `k`: pairing against `p k` is `snd ∘ ψ`. -/
theorem phi_pi (k : ℕ) (hk0 : 0 < k) (hk : Even k) (x : A) :
    quotientPairing (pi x) (p k) = (psi k x).snd := by
  have := LinearMap.congr_fun (delta_eq k hk0 hk) (pi x)
  rw [LinearMap.flip_apply] at this
  rw [← this]
  rfl

theorem pairing_lift {k : ℕ} {P : A} (hP : pi P = p k) (w : A) :
    pairing P w = quotientPairing (pi w) (p k) := by
  rw [pairing_symm, ← quotientPairing_pi, hP]

theorem psi_word {r : ℕ} (k : ℕ) (γ : Fin r → ℕ) :
    psi k (EKMixedPairing.word γ (fun _ => false)) = ∏ i, psi k (CompleteElementary.h (γ i)) := by
  simp [EKMixedPairing.word, EKMixedPairing.gen, map_list_prod, List.map_ofFn, List.prod_ofFn,
    Function.comp_def]

theorem support {r : ℕ} (k : ℕ) (γ : Fin r → ℕ)
    (hne : (psi k (EKMixedPairing.word γ (fun _ => false))).snd ≠ 0) (j : Fin r) :
    γ j = 0 ∨ γ j = k := by
  by_contra hc
  push_neg at hc
  apply hne
  rw [psi_word, Finset.prod_eq_zero (Finset.mem_univ j)]
  · simp
  · rw [psi_h, if_neg hc.1, if_neg hc.2]

theorem even_sum' {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, Even (f i)) :
    Even (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem crossCols_even_left {c : ℕ} (u v : Fin c → ℕ) (hu : ∀ j, Even (u j)) :
    Even (crossCols u v) := by
  unfold crossCols
  apply even_sum'; intro j _
  apply even_sum'; intro l _
  split_ifs
  · exact (hu j).mul_right _
  · exact Even.zero

theorem crossCols_even_right {c : ℕ} (u v : Fin c → ℕ) (hv : ∀ l, Even (v l)) :
    Even (crossCols u v) := by
  unfold crossCols
  apply even_sum'; intro j _
  apply even_sum'; intro l _
  split_ifs
  · exact (hv l).mul_left _
  · exact Even.zero

theorem sign_one_of_support {r : ℕ} (k : ℕ) (hk : Even k) (γ : Fin r → ℕ)
    (hne : (psi k (EKMixedPairing.word γ (fun _ => false))).snd ≠ 0) (j : Fin r) : Even (γ j) := by
  rcases support k γ hne j with h | h <;> rw [h]
  · exact Even.zero
  · exact hk

/-- Complementary-split involution `u ↦ β - u`. -/
def revSplit {c : ℕ} (β : Fin c → ℕ) : Splits β ≃ Splits β where
  toFun u j := Fin.rev (u j)
  invFun u j := Fin.rev (u j)
  left_inv u := by funext j; simp
  right_inv u := by funext j; simp

theorem upper_rev {c : ℕ} {β : Fin c → ℕ} (u : Splits β) :
    upper (revSplit β u) = lower u := by
  funext j
  simp only [upper, lower, revSplit, Equiv.coe_fn_mk, Fin.val_rev]
  omega

theorem lower_rev {c : ℕ} {β : Fin c → ℕ} (u : Splits β) :
    lower (revSplit β u) = upper u := by
  funext j
  have := (u j).isLt
  simp only [upper, lower, revSplit, Equiv.coe_fn_mk, Fin.val_rev]
  omega

/-- Even `k ≥ 1`: `p k` is central. -/
theorem central_of_even (k : ℕ) (hk0 : 0 < k) (hk : Even k) (y : Q) : p k * y = y * p k := by
  obtain ⟨P, hP⟩ := pi_surjective (p k)
  obtain ⟨Y, rfl⟩ := pi_surjective y
  rw [← hP, ← map_mul, ← map_mul]
  apply EKQuotientRelations.quotient_ext_words false
  intro r β
  rw [quotientPairing_pi, quotientPairing_pi, pairing_mul_word, pairing_mul_word]
  simp only [pairing_lift hP, phi_pi k hk0 hk]
  have hL : ∀ u : Splits β, (-1 : ℤ) ^ crossCols (upper u) (lower u) *
      ((psi k (EKMixedPairing.word (upper u) fun _ => false)).snd *
        pairing Y (EKMixedPairing.word (lower u) fun _ => false)) =
      (psi k (EKMixedPairing.word (upper u) fun _ => false)).snd *
        pairing Y (EKMixedPairing.word (lower u) fun _ => false) := by
    intro u
    by_cases h0 : (psi k (EKMixedPairing.word (upper u) fun _ => false)).snd = 0
    · simp [h0]
    · rw [(crossCols_even_left _ _ (sign_one_of_support k hk _ h0)).neg_one_pow, one_mul]
  have hR : ∀ u : Splits β, (-1 : ℤ) ^ crossCols (upper u) (lower u) *
      (pairing Y (EKMixedPairing.word (upper u) fun _ => false) *
        (psi k (EKMixedPairing.word (lower u) fun _ => false)).snd) =
      pairing Y (EKMixedPairing.word (upper u) fun _ => false) *
        (psi k (EKMixedPairing.word (lower u) fun _ => false)).snd := by
    intro u
    by_cases h0 : (psi k (EKMixedPairing.word (lower u) fun _ => false)).snd = 0
    · simp [h0]
    · rw [(crossCols_even_right _ _ (sign_one_of_support k hk _ h0)).neg_one_pow, one_mul]
  rw [Finset.sum_congr rfl (fun u _ => hL u), Finset.sum_congr rfl (fun u _ => hR u)]
  apply Fintype.sum_equiv (revSplit β)
  intro u
  rw [upper_rev, lower_rev, mul_comm]

/-! ### Odd `k` -/

theorem pi_hh_mem (a b : ℕ) :
    pi (CompleteElementary.h a * CompleteElementary.h b) ∈ degreePiece (a + b) := by
  have := pi_hWord_mem [a, b]
  simpa [hWord] using this

theorem phiP_mismatch {k : ℕ} {P : A} (hP : pi P = p k) (a b : ℕ) (hab : a + b ≠ k) :
    pairing P (CompleteElementary.h a * CompleteElementary.h b) = 0 := by
  rw [pairing_lift hP]
  exact orth hab (pi_hh_mem a b) (mBasis k (rowShape k)).property

theorem phiP_k {k : ℕ} {P : A} (hP : pi P = p k) (hk : 0 < k) :
    pairing P (CompleteElementary.h k) = 1 := by
  rw [pairing_lift hP]
  have he : pi (CompleteElementary.h k) = hPartition (rowShape k).val := by
    rw [hPartition_eq, rowShape_rows k hk]; simp [hWord]
  rw [he, pair_hPartition_p, if_pos rfl]

theorem phiP_km1 {k : ℕ} {P : A} (hP : pi P = p k) (hk : 2 ≤ k) :
    pairing P (CompleteElementary.h (k - 1) * CompleteElementary.h 1) = 0 := by
  rw [pairing_lift hP]
  have hs : List.Sorted (· ≥ ·) [k - 1, 1] := by
    refine List.sorted_cons.mpr ⟨?_, List.sorted_singleton 1⟩
    intro b hb; simp at hb; omega
  let μ := YoungDiagram.ofRowLens [k - 1, 1] hs
  have hμ : μ.rowLens = [k - 1, 1] :=
    YoungDiagram.rowLens_ofRowLens_eq_self (hw := hs) (by intro x hx; simp at hx; omega)
  have he : pi (CompleteElementary.h (k - 1) * CompleteElementary.h 1) = hPartition μ := by
    rw [hPartition_eq, hμ]; simp [hWord]
  rw [he, pair_hPartition_p, if_neg]
  intro hc
  have := (rows_iff k (by omega) μ).mpr hc
  rw [hμ] at this
  simp at this

/-- Odd `k ≥ 3`: `p k` does not commute with `h_1`. -/
theorem not_central_odd (k : ℕ) (hk3 : 3 ≤ k) (hk : Odd k) :
    p k * EKElementaryQuotient.h 1 ≠ EKElementaryQuotient.h 1 * p k := by
  intro hc
  obtain ⟨P, hP⟩ := pi_surjective (p k)
  rw [← hP] at hc
  have h2 := congrArg (fun z => quotientPairing z
    (pi (CompleteElementary.h k * CompleteElementary.h 1))) hc
  simp only [EKElementaryQuotient.h, ← map_mul, quotientPairing_pi] at h2
  rw [pairing_mul_two, pairing_mul_two] at h2
  have hL : ∑ i : Fin (k+1), ∑ j : Fin (1+1), (-1 : ℤ) ^ (j.val * (k - i.val)) *
      (pairing P (CompleteElementary.h i.val * CompleteElementary.h j.val) *
        pairing (CompleteElementary.h 1)
          (CompleteElementary.h (k - i.val) * CompleteElementary.h (1 - j.val))) = 1 := by
    rw [Fintype.sum_eq_single (Fin.last k)]
    · simp [Fin.sum_univ_two, pairing_h_two, phiP_k hP (by omega),
        phiP_mismatch hP k 1 (by omega)]
    · intro i hi
      have hik : i.val < k := by
        have := i.isLt
        have : i.val ≠ k := fun h => hi (Fin.ext (by simp [h]))
        omega
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      rw [pairing_h_two]
      rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
      · rw [if_neg (by omega)]; simp
      · by_cases h1 : i.val = k - 1
        · rw [hj, h1, phiP_km1 hP (by omega)]; simp
        · rw [if_neg (by omega)]; simp
  have hR : ∑ i : Fin (k+1), ∑ j : Fin (1+1), (-1 : ℤ) ^ (j.val * (k - i.val)) *
      (pairing (CompleteElementary.h 1) (CompleteElementary.h i.val * CompleteElementary.h j.val) *
        pairing P (CompleteElementary.h (k - i.val) * CompleteElementary.h (1 - j.val))) = -1 := by
    rw [Fintype.sum_eq_single 0]
    · simp [Fin.sum_univ_two, pairing_h_two, phiP_k hP (by omega), hk.neg_one_pow,
        phiP_mismatch hP k 1 (by omega)]
    · intro i hi
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      rw [pairing_h_two]
      rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
      · by_cases h1 : i.val = 1
        · rw [hj, h1]; simp [phiP_km1 hP (k := k) (by omega)]
        · rw [if_neg (by omega)]; simp
      · rw [if_neg (by omega)]; simp
  rw [hL, hR] at h2
  norm_num at h2

theorem rowShape_one : rowShape 1 = EKCenterPowerControls.row1 := rfl

/-- **EK Prop 3.4 (integral, q = -1).** For every `k ≥ 1`, `p_k = m_(k)` is central
in the actual quotient `Q` iff `k` is even. -/
theorem center_iff (k : ℕ) (hk : 1 ≤ k) : (∀ y : Q, p k * y = y * p k) ↔ Even k := by
  constructor
  · intro hc
    by_contra hne
    have ho : Odd k := Nat.not_even_iff_odd.mp hne
    by_cases h1 : k = 1
    · subst h1
      exact EKCenterPowerControls.control_k1 (hc (EKElementaryQuotient.h 2))
    · exact not_central_odd k (by obtain ⟨t, ht⟩ := ho; omega) ho (hc _)
  · intro he y
    exact central_of_even k (by omega) he y

end OddMath.Frontier.EKCenterPower
