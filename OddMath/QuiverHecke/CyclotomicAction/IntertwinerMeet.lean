/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerBalance

/-!
# The three-strand identity on `i, j, i`

Kang–Kashiwara–Oh, arXiv:1206.5933v2, Lemma 8.3 and the first identity of (8.13), in the case
left open by `IntertwinerBalance`: for `j ≠ i` the two sides `meetLeft`, `meetRight` of
`τ_{a+1} g_a τ_{a+1} = τ_a g_{a+1} τ_a` on the word `i, j, i` agree. KKO deduce this from
`S x_b = ± x_{s(b)} S`; here it is a direct computation. Conjugating `g` by the crossings
moves its dots to the outer strands (`conj_element`, `conj_gEven`), leaving the double crossings
(`cross_cross_ne`) and the two braid words (`braid_iji`). Their combination is a signed
geometric-sum identity in the outer dots (`odd_poly` for odd `i`, where the dots anticommute,
`even_poly` for even `i`), proved termwise from `pow_sub_mul_sub_of_anticomm`.

## Main results

* `meetLeft_eq_meetRight_iji`: the three-strand identity on `i, j, i`, `j ≠ i`.
* `meetLeft_eq_all`: the three-strand identity for all colours `i, j, c`.
* `cross_comp_moveHom_all`: the first identity of KKO (8.13) for every old crossing:
  `ψ g_n ⋯ g_1 = (-1)^{p(j)p(c)p(i)p(ν)} g_n ⋯ g_1 ψ`.
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams SignedNilHecke
open SKM (zsign)

namespace IntertwinerMeet

section Ring
variable {B : Type*} [Ring B]

/-- The alternating geometric sum `∑_{s < m} (-1)^s u^{m-1-s} w^s`. -/
def altGeom (u w : B) (m : ℕ) : B :=
  ∑ s ∈ Finset.range m, (-1 : B) ^ s * (u ^ (m - 1 - s) * w ^ s)

theorem altGeom_add_two (u w : B) (n : ℕ) :
    altGeom u w (2 * n + 2) = u ^ 2 * altGeom u w (2 * n) + (u - w) * w ^ (2 * n) := by
  unfold altGeom
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.mul_sum]
  have e : ∀ s ∈ Finset.range (2 * n), (-1 : B) ^ s * (u ^ (2 * n + 2 - 1 - s) * w ^ s) =
      u ^ 2 * ((-1 : B) ^ s * (u ^ (2 * n - 1 - s) * w ^ s)) := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [show 2 * n + 2 - 1 - s = 2 + (2 * n - 1 - s) by omega, pow_add,
      ((Commute.neg_one_left u).pow_pow s 2).symm.left_comm, mul_assoc]
  rw [Finset.sum_congr rfl e, show 2 * n + 2 - 1 - 2 * n = 1 by omega,
    show 2 * n + 1 + 1 - 1 - (2 * n + 1) = 0 by omega, pow_succ (-1 : B) (2 * n),
    pow_mul, neg_one_sq, one_pow, pow_one, pow_zero, pow_succ' w (2 * n)]
  noncomm_ring

/-- For anticommuting `u, w`:
`(w^{2n} - u^{2n})(w - u) = -(w² - u²) ∑_{s<2n} (-1)^s u^{2n-1-s} w^s`. -/
theorem pow_sub_mul_sub_of_anticomm {u w : B} (h : w * u = -(u * w)) (n : ℕ) :
    (w ^ (2 * n) - u ^ (2 * n)) * (w - u) = -((w ^ 2 - u ^ 2) * altGeom u w (2 * n)) := by
  have hwu : Commute (w ^ 2) u := by
    show w ^ 2 * u = u * w ^ 2
    rw [pow_two, mul_assoc, h, mul_neg, ← mul_assoc, h, neg_mul, neg_neg, mul_assoc]
  have huw : Commute (u ^ 2) (w ^ 2) := (hwu.pow_right 2).symm
  have hn : Commute (w ^ (2 * n)) u := by rw [pow_mul]; exact hwu.pow_left n
  induction n with
  | zero => simp [altGeom]
  | succ n ih =>
    have hn' : Commute (w ^ (2 * n)) u := by rw [pow_mul]; exact hwu.pow_left n
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, altGeom_add_two]
    have e : w ^ (2 * n + 2) - u ^ (2 * n + 2) =
        u ^ 2 * (w ^ (2 * n) - u ^ (2 * n)) + (w ^ 2 - u ^ 2) * w ^ (2 * n) := by
      rw [show 2 * n + 2 = 2 + 2 * n by ring, pow_add w, pow_add u]
      noncomm_ring
    have h3 : w ^ (2 * n) * (w - u) = (w - u) * w ^ (2 * n) := by
      rw [mul_sub, sub_mul, hn'.eq, ← pow_succ, ← pow_succ']
    have h4 : u ^ 2 * ((w ^ 2 - u ^ 2) * altGeom u w (2 * n)) =
        (w ^ 2 - u ^ 2) * (u ^ 2 * altGeom u w (2 * n)) := by
      rw [← mul_assoc, ← mul_assoc, (huw.sub_right (Commute.refl (u ^ 2))).eq]
    rw [e, add_mul, mul_assoc, ih hn', mul_assoc, h3, mul_neg, h4]
    noncomm_ring

/-- For commuting `u, w`: `w^m - u^m = (w - u) ∑_{s<m} u^{m-1-s} w^s`. -/
theorem pow_sub_of_comm {u w : B} (h : Commute u w) (m : ℕ) :
    w ^ m - u ^ m = (w - u) * ∑ s ∈ Finset.range m, u ^ (m - 1 - s) * w ^ s := by
  rw [← (h.symm).mul_geom_sum₂]
  exact congrArg _ (Finset.sum_congr rfl fun s _ => ((h.pow_pow _ _).eq).symm)

end Ring

section Conj
variable {k : Type*} [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]

theorem endSub_comp {X Y : C} (f g : End X) (h : X ⟶ Y) : (f - g) ≫ h = f ≫ h - g ≫ h :=
  Preadditive.sub_comp f g h

theorem comp_endSub {X Y : C} (h : Y ⟶ X) (f g : End X) : h ≫ (f - g) = h ≫ f - h ≫ g :=
  Preadditive.comp_sub h f g

theorem endAdd_comp {X Y : C} (f g : End X) (h : X ⟶ Y) : (f + g) ≫ h = f ≫ h + g ≫ h :=
  Preadditive.add_comp _ _ _ f g h

theorem comp_endAdd {X Y : C} (h : Y ⟶ X) (f g : End X) : h ≫ (f + g) = h ≫ f + h ≫ g :=
  Preadditive.comp_add _ _ _ h f g

/-- Conjugating the odd variant `g` by a pair of morphisms that transport the dots. -/
theorem conj_element {A Bo : C} (P : A ⟶ Bo) (P' : Bo ⟶ A) (u v T : End Bo) (x y : End A)
    (σ : k) (hσ : σ * σ = 1) (hPu : P ≫ u = σ • (x ≫ P)) (hPv : P ≫ v = σ • (y ≫ P))
    (huP : u ≫ P' = σ • (P' ≫ x)) (hvP : v ≫ P' = σ • (P' ≫ y)) :
    P ≫ (OddNilHecke.Intertwiner.element u v T : End Bo) ≫ P' =
      σ • ((y - x : End A) ≫ P ≫ P' ≫ (OddNilHecke.Intertwiner.squareDiff x y : End A)) -
        P ≫ T ≫ P' ≫ (OddNilHecke.Intertwiner.squareDiff x y ^ 2 : End A) := by
  have hS : (OddNilHecke.Intertwiner.squareDiff u v : End Bo) ≫ P' =
      P' ≫ (OddNilHecke.Intertwiner.squareDiff x y : End A) := by
    simp only [OddNilHecke.Intertwiner.squareDiff, pow_two, End.mul_def, endSub_comp,
      comp_endSub, Category.assoc, huP, hvP, Linear.comp_smul, Linear.smul_comp,
      reassoc_of% huP, reassoc_of% hvP, smul_smul, hσ, one_smul]
  have hS2 : (OddNilHecke.Intertwiner.squareDiff u v ^ 2 : End Bo) ≫ P' =
      P' ≫ (OddNilHecke.Intertwiner.squareDiff x y ^ 2 : End A) := by
    simp only [pow_two, End.mul_def, Category.assoc, hS, reassoc_of% hS]
  have hD : P ≫ (v - u : End Bo) = σ • ((y - x : End A) ≫ P) := by
    simp only [comp_endSub, endSub_comp, hPu, hPv, smul_sub]
  rw [OddNilHecke.Intertwiner.element, End.mul_def, End.mul_def, endSub_comp,
    Preadditive.comp_sub, Category.assoc, Category.assoc, hS, hS2, ← Category.assoc P (v - u), hD]
  simp only [Linear.smul_comp, Category.assoc]

/-- Conjugating the even variant `g` by a pair of morphisms that transport the dots. -/
theorem conj_gEven {A Bo : C} (P : A ⟶ Bo) (P' : Bo ⟶ A) (u v T : End Bo) (x y : End A)
    (σ : k) (hσ : σ * σ = 1) (huP : u ≫ P' = σ • (P' ≫ x)) (hvP : v ≫ P' = σ • (P' ≫ y)) :
    P ≫ (gEven u v T : End Bo) ≫ P' =
      σ • (P ≫ P' ≫ (y - x : End A)) + P ≫ T ≫ P' ≫ (y - x : End A) ≫ (y - x : End A) := by
  have hD : (v - u : End Bo) ≫ P' = σ • (P' ≫ (y - x : End A)) := by
    simp only [comp_endSub, endSub_comp, huP, hvP, smul_sub]
  have hD' : ∀ (Z : C) (r : A ⟶ Z), (v - u : End Bo) ≫ P' ≫ r = σ • (P' ≫ (y - x : End A) ≫ r) :=
    fun Z r => by rw [← Category.assoc, hD, Linear.smul_comp, Category.assoc]
  simp only [gEven, phiEven, End.mul_def, End.one_def, endAdd_comp, Preadditive.comp_add,
    Preadditive.add_comp,
    Category.assoc, Category.id_comp, hD, hD', Linear.comp_smul, smul_smul, hσ, one_smul]

end Conj

section Poly
variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B]

/-- The double crossing `Q_{ij}(u, m)` on strands of colours `i, j`. -/
def qLeft (u m : B) (d e : ℕ) (t₁ t₂ : k) (s : ℕ → ℕ → k) : B :=
  ∑ p ∈ Finset.Ioo 0 d, ∑ q ∈ Finset.Ioo 0 e, s p q • (u ^ p * m ^ q) + (t₁ • u ^ d + t₂ • m ^ e)

/-- The double crossing `Q_{ji}(m, w)` on strands of colours `j, i`, indexed as `Q_{ij}`. -/
def qRight (m w : B) (d e : ℕ) (t₁ t₂ : k) (s : ℕ → ℕ → k) : B :=
  ∑ p ∈ Finset.Ioo 0 d, ∑ q ∈ Finset.Ioo 0 e, s p q • (m ^ q * w ^ p) + (t₂ • m ^ e + t₁ • w ^ d)

/-- The correction term of the braid relation on `i, j, i`, with signs `ζ`. -/
def braidCorr (ζ : ℕ → k) (u m w : B) (d e : ℕ) (t₁ : k) (s : ℕ → ℕ → k) : B :=
  ∑ r ∈ Finset.range d, (ζ r * t₁) • (u ^ (d - 1 - r) * w ^ r) +
    ∑ p ∈ Finset.Ioo 0 d, ∑ q ∈ Finset.Ioo 0 e, ∑ r ∈ Finset.range p,
      (ζ r * s p q) • (u ^ (p - 1 - r) * m ^ q * w ^ r)

/-- Termwise vanishing of `L(Q_{ji} - Q_{ij}) + R(braid correction)`. -/
theorem assembly (L R : B →+ B) (ζ : ℕ → k) (u m w : B) (d e : ℕ) (t₁ t₂ : k)
    (s : ℕ → ℕ → k)
    (ht : L (t₁ • (w ^ d - u ^ d)) +
      R (∑ r ∈ Finset.range d, (ζ r * t₁) • (u ^ (d - 1 - r) * w ^ r)) = 0)
    (hs : ∀ p q, L (s p q • (m ^ q * w ^ p - u ^ p * m ^ q)) +
      R (∑ r ∈ Finset.range p, (ζ r * s p q) • (u ^ (p - 1 - r) * m ^ q * w ^ r)) = 0) :
    L (qRight m w d e t₁ t₂ s - qLeft u m d e t₁ t₂ s) + R (braidCorr ζ u m w d e t₁ s) = 0 := by
  have hQ : qRight m w d e t₁ t₂ s - qLeft u m d e t₁ t₂ s = t₁ • (w ^ d - u ^ d) +
      ∑ p ∈ Finset.Ioo 0 d, ∑ q ∈ Finset.Ioo 0 e, s p q • (m ^ q * w ^ p - u ^ p * m ^ q) := by
    simp only [qRight, qLeft, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [hQ, braidCorr, map_add, map_add]
  simp only [map_sum] at ht hs ⊢
  rw [add_add_add_comm, ht, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun q _ => hs p q

theorem zsign_natCast_smul (r : ℕ) (Y : B) : zsign k (r : ZMod 2) • Y = (-1 : B) ^ r * Y := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [(ZMod.natCast_eq_zero_iff_even).2 hr, hr.neg_one_pow, one_mul]
    simp [zsign]
  · rw [(ZMod.natCast_eq_one_iff_odd).2 hr, hr.neg_one_pow]
    simp [zsign]

/-- The odd term identity: `σ S (c (M w^p - u^p M))(w - u) + S² ∑ ± c u^{p-1-r} M w^r = 0`
for anticommuting `u, w`, `p` even and `M` commuting with both. -/
theorem odd_term {u w M : B} (hwu : w * u = -(u * w)) (hMu : Commute M u) (hMw : Commute M w)
    (pj : ZMod 2) (c : k) {p : ℕ} (hp : Even p) :
    zsign k pj • ((w ^ 2 - u ^ 2) * (c • (M * w ^ p - u ^ p * M)) * (w - u)) +
      (w ^ 2 - u ^ 2) ^ 2 * ∑ r ∈ Finset.range p,
        (zsign k (pj + r) * c) • (u ^ (p - 1 - r) * M * w ^ r) = 0 := by
  obtain ⟨n, rfl⟩ := hp
  have h2 : n + n = 2 * n := by ring
  have hS : Commute M (w ^ 2 - u ^ 2) := (hMw.pow_right 2).sub_right (hMu.pow_right 2)
  have e1 : M * w ^ (n + n) - u ^ (n + n) * M = M * (w ^ (2 * n) - u ^ (2 * n)) := by
    rw [h2, mul_sub, (hMu.pow_right _).eq]
  have e2 : ∑ r ∈ Finset.range (n + n), (zsign k (pj + r) * c) • (u ^ (n + n - 1 - r) * M * w ^ r) =
      (zsign k pj * c) • (M * altGeom u w (2 * n)) := by
    rw [altGeom, Finset.mul_sum, Finset.smul_sum, h2]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [zsign_add_eq, mul_right_comm, mul_smul, zsign_natCast_smul,
      ← (hMu.pow_right _).eq, mul_assoc M, ← mul_assoc, ((Commute.neg_one_left M).pow_left r).eq,
      mul_assoc]
  have key := pow_sub_mul_sub_of_anticomm hwu n
  rw [e1, e2, mul_smul_comm, smul_mul_assoc, mul_assoc, mul_assoc, key, mul_smul_comm,
    smul_smul, mul_neg, mul_neg, smul_neg, ← mul_assoc M, hS.eq, mul_assoc, ← mul_assoc,
    ← pow_two, neg_add_cancel]

/-- The even term identity: `(w - u)(c (M w^p - u^p M)) - (w - u)² ∑ c u^{p-1-r} M w^r = 0`
for commuting `u, w` and `M` commuting with both. -/
theorem even_term {u w M : B} (huw : Commute u w) (hMu : Commute M u) (hMw : Commute M w)
    (ζ : ℕ → k) (hζ : ∀ r, ζ r = 1) (c : k) (p : ℕ) :
    (w - u) * (c • (M * w ^ p - u ^ p * M)) -
      (w - u) * (w - u) * ∑ r ∈ Finset.range p, (ζ r * c) • (u ^ (p - 1 - r) * M * w ^ r) = 0 := by
  have hD : Commute M (w - u) := hMw.sub_right hMu
  have e1 : M * w ^ p - u ^ p * M =
      M * ((w - u) * ∑ r ∈ Finset.range p, u ^ (p - 1 - r) * w ^ r) := by
    rw [← pow_sub_of_comm huw, mul_sub, (hMu.pow_right _).eq]
  have e2 : ∑ r ∈ Finset.range p, (ζ r * c) • (u ^ (p - 1 - r) * M * w ^ r) =
      c • (M * ∑ r ∈ Finset.range p, u ^ (p - 1 - r) * w ^ r) := by
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hζ, one_mul, ← (hMu.pow_right _).eq, mul_assoc]
  rw [e1, e2, mul_smul_comm, mul_smul_comm, ← mul_assoc, hD.symm.eq, mul_assoc, mul_assoc,
    hD.left_comm, hD.left_comm, sub_self]

/-- The polynomial identity behind the three-strand identity on `i, j, i` for odd `i`. -/
theorem odd_poly {u m w : B} (hwu : w * u = -(u * w)) {d e : ℕ} (hd : Even d) (t₁ t₂ : k)
    (s : ℕ → ℕ → k) (hs : ∀ p q, s p q ≠ 0 → Even p ∧ Commute (m ^ q) u ∧ Commute (m ^ q) w)
    (pj : ZMod 2) (ζ : ℕ → k) (hζ : ∀ r : ℕ, ζ r = zsign k (pj + r)) :
    zsign k pj • ((w ^ 2 - u ^ 2) * (qRight m w d e t₁ t₂ s - qLeft u m d e t₁ t₂ s) * (w - u)) +
      (w ^ 2 - u ^ 2) ^ 2 * braidCorr ζ u m w d e t₁ s = 0 := by
  let L : B →+ B := AddMonoidHom.mk' (fun X => zsign k pj • ((w ^ 2 - u ^ 2) * X * (w - u)))
    (fun a b => by simp only [mul_add, add_mul, smul_add])
  have h := assembly L (AddMonoidHom.mulLeft ((w ^ 2 - u ^ 2) ^ 2)) ζ u m w d e t₁ t₂ s ?_ ?_
  · exact h
  · have := odd_term hwu (Commute.one_left u) (Commute.one_left w) pj t₁ hd
    simp only [one_mul, mul_one] at this
    simpa only [L, AddMonoidHom.mk'_apply, AddMonoidHom.coe_mulLeft, hζ] using this
  · intro p q
    by_cases h0 : s p q = 0
    · simp [L, h0]
    · obtain ⟨hp, hu, hw⟩ := hs p q h0
      simpa only [L, AddMonoidHom.mk'_apply, AddMonoidHom.coe_mulLeft, hζ] using
        odd_term hwu hu hw pj (s p q) hp

/-- The polynomial identity behind the three-strand identity on `i, j, i` for even `i`. -/
theorem even_poly {u m w : B} (huw : Commute u w) (hmu : Commute m u) (hmw : Commute m w)
    (d e : ℕ) (t₁ t₂ : k) (s : ℕ → ℕ → k) (ζ : ℕ → k) (hζ : ∀ r, ζ r = 1) :
    (w - u) * (qRight m w d e t₁ t₂ s - qLeft u m d e t₁ t₂ s) -
      (w - u) * (w - u) * braidCorr ζ u m w d e t₁ s = 0 := by
  have h := assembly (AddMonoidHom.mulLeft (w - u)) (-AddMonoidHom.mulLeft ((w - u) * (w - u)))
    ζ u m w d e t₁ t₂ s ?_ ?_
  · simpa only [AddMonoidHom.coe_mulLeft, AddMonoidHom.neg_apply, ← sub_eq_add_neg] using h
  · have := even_term huw (Commute.one_left u) (Commute.one_left w) ζ hζ t₁ d
    simp only [one_mul, mul_one] at this
    simpa only [AddMonoidHom.coe_mulLeft, AddMonoidHom.neg_apply, ← sub_eq_add_neg] using this
  · intro p q
    simpa only [AddMonoidHom.coe_mulLeft, AddMonoidHom.neg_apply, ← sub_eq_add_neg] using
      even_term huw (hmu.pow_left q) (hmw.pow_left q) ζ hζ (s p q) p

/-- `Q_{ji}` written with `j, i` indices is `Q_{ij}` read on swapped strands. -/
theorem qLeft_swap (m w : B) (d e : ℕ) (t₁ t₂ : k) (s s' : ℕ → ℕ → k)
    (hs : ∀ p q, s' p q = s q p) :
    qLeft m w e d t₂ t₁ s' = qRight m w d e t₁ t₂ s := by
  rw [qLeft, qRight, Finset.sum_comm]
  simp only [hs]

/-- A power of a signed-commuting element commutes when the total sign is even. -/
theorem commute_pow_of_zsign {m x : B} (e : ZMod 2) (h : m * x = zsign k e • (x * m)) (q : ℕ)
    (hq : (q : ZMod 2) * e = 0) : Commute (m ^ q) x := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) e with rfl | rfl
  · have hc : Commute m x := by
      show m * x = x * m
      rw [h]; simp [zsign]
    exact hc.pow_left q
  · rw [mul_one, ZMod.natCast_eq_zero_iff_even] at hq
    obtain ⟨n, rfl⟩ := hq
    have hc : Commute (m * m) x := by
      show m * m * x = x * (m * m)
      rw [mul_assoc, h, mul_smul_comm, ← mul_assoc, h, smul_mul_assoc, smul_smul,
        zsign_mul_self, one_smul, mul_assoc]
    rw [← two_mul, pow_mul, sq]
    exact hc.pow_left n

theorem fin_odd (σ : k) (S D Qr Ql T₁ T₂ : B)
    (h : σ • (S * (Qr - Ql) * D) + S ^ 2 * (T₁ - T₂) = 0) :
    σ • (S * Qr * D) - S ^ 2 * T₂ = σ • (S * Ql * D) - S ^ 2 * T₁ := by
  rw [← sub_eq_zero, ← h]
  simp only [mul_sub, sub_mul, smul_sub]
  abel

theorem fin_even (D Qr Ql T₁ T₂ : B) (h : D * (Qr - Ql) - D * D * (T₁ - T₂) = 0) :
    D * Qr + D * D * T₂ = D * Ql + D * D * T₁ := by
  rw [← sub_eq_zero, ← h]
  simp only [mul_sub]
  abel

end Poly

section Words
variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

theorem sChain_iji_left (l v : List I) (i j : I) :
    SChain (l ++ i :: j :: i :: v) (pl (l ++ i :: j :: i :: v) [.cross l.length])
      (l ++ j :: i :: i :: v) :=
  sChain_ofShape' l (i :: v) (.cross i j) (by simp [Shape.dom]) (by simp [Shape.cod]) rfl

theorem sChain_jii_left (l v : List I) (i j : I) :
    SChain (l ++ j :: i :: i :: v) (pl (l ++ j :: i :: i :: v) [.cross l.length])
      (l ++ i :: j :: i :: v) :=
  sChain_ofShape' l (i :: v) (.cross j i) (by simp [Shape.dom]) (by simp [Shape.cod]) rfl

/-- Transporting a class along equalities of its source and target words. -/
@[reassoc]
theorem eqToHom_cl_eqToHom {t t₀ t₁ t' s : List I} {gs gs' : List PG} (e₀ : t = t₀) (e₁ : t₁ = s)
    (e₂ : t' = s) (hg : gs = gs') (h : SChain t₀ (pl t₀ gs) t₁) (h' : SChain t (pl t gs') t') :
    eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e₀) ≫ cl D Sc t₀ t₁ gs h ≫
        eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e₁) =
      cl D Sc t t' gs' h' ≫ eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e₂) := by
  subst e₀ hg e₁ e₂
  simp

theorem eqToHom_cl {t t₀ t₁ t' : List I} {gs gs' : List PG} (e₀ : t = t₀) (e₂ : t' = t₁)
    (hg : gs = gs') (h : SChain t₀ (pl t₀ gs) t₁) (h' : SChain t (pl t gs') t') :
    eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e₀) ≫ cl D Sc t₀ t₁ gs h =
      cl D Sc t t' gs' h' ≫ eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e₂) := by
  subst e₀ hg e₂
  simp

theorem meetLeft_iji (l v : List I) {i j : I} (hij : i ≠ j) :
    meetLeft D Sc l v i j i =
      cl D Sc _ _ [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫
        sameIntertwiner D Sc (l ++ i :: i :: j :: v) l.length i ≫
          cl D Sc _ _ [.cross (l.length + 1)] (sChain_cross_succ l v i i j) ≫
            eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
              (show l ++ i :: j :: i :: v = (l ++ [i] ++ [j]) ++ i :: v by simp)) := by
  unfold meetLeft
  rw [intertwinerHom_self, intertwinerHom_of_ne D Sc _ _ hij,
    sameIntertwiner_congr D Sc (w := l ++ i :: i :: j :: v)
      (show l ++ i :: i :: j :: v = l ++ [i, i] ++ (j :: v) by simp) rfl]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [eqToHom_refl, Category.id_comp]
  rw [eqToHom_cl_eqToHom D Sc (t' := l ++ i :: j :: i :: v) (gs' := [.cross (l.length + 1)])
    (s := (l ++ [i] ++ [j]) ++ i :: v) ?_ ?_ ?_ ?_ _ (sChain_cross_succ l v i i j)] <;> simp

theorem meetRight_iji (l v : List I) {i j : I} (hij : i ≠ j) :
    meetRight D Sc l v i j i =
      cl D Sc _ _ [.cross l.length] (sChain_iji_left l v i j) ≫
        sameIntertwiner D Sc (l ++ j :: i :: i :: v) (l.length + 1) i ≫
          cl D Sc _ _ [.cross l.length] (sChain_jii_left l v i j) ≫
            eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
              (show l ++ i :: j :: i :: v = (l ++ [i] ++ [j]) ++ i :: v by simp)) := by
  unfold meetRight
  rw [intertwinerHom_self, intertwinerHom_of_ne D Sc _ _ hij,
    sameIntertwiner_congr D Sc (w := l ++ j :: i :: i :: v)
      (show l ++ j :: i :: i :: v = (l ++ [j]) ++ [i, i] ++ v by simp)
      (show l.length + 1 = (l ++ [j]).length by simp)]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [eqToHom_cl_eqToHom_assoc D Sc (t' := l ++ j :: i :: i :: v) (gs' := [.cross l.length])
      (by simp) (by simp) rfl rfl _ (sChain_iji_left l v i j),
    eqToHom_refl, Category.id_comp,
    eqToHom_cl D Sc (t' := l ++ i :: j :: i :: v) (gs' := [.cross l.length]) (by simp) (by simp)
      rfl _ (sChain_jii_left l v i j)]


theorem slide_right_ne_gen {t t' : List I} (l r : List I) (i j : I) (hij : i ≠ j) {p : ℕ}
    (hp : l.length = p) (ht : t = l ++ [i, j] ++ r) (ht' : t' = l ++ [j, i] ++ r)
    (h₁ : SChain t (pl t [.cross p, .dot p]) t')
    (h₂ : SChain t (pl t [.dot (p + 1), .cross p]) t') :
    cl D Sc t t' [.cross p, .dot p] h₁ =
      zsign k (D.parity i * D.parity j) • cl D Sc t t' [.dot (p + 1), .cross p] h₂ := by
  subst hp ht ht'
  exact slide_right_ne D Sc l r i j hij h₁ h₂

section Push
variable (l v : List I) {i j : I} (hij : i ≠ j)
include hij

omit hij in
/-- The first dot passes through the crossing of strands `a + 1, a + 2`. -/
theorem push_P_u :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫ dotE D Sc (l ++ i :: i :: j :: v) (l.length) =
      zsign k (D.parity i * D.parity j) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length) ≫ cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  refine eq_zsign_smul_symm ?_
  rw [show D.parity i * D.parity j = D.parity i * (D.parity j * D.parity i) by
    rw [mul_comm (D.parity j), ← mul_assoc, parity_sq]]
  exact cl_interchange_gen D Sc l [] v (.dot i) (.cross j i) (by simp [Shape.dom])
    (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom]) (by simp [Shape.dom]) _ _

theorem push_P_v :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫ dotE D Sc (l ++ i :: i :: j :: v) (l.length + 1) =
      zsign k (D.parity i * D.parity j) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) ≫ cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  rw [mul_comm]
  exact slide_right_ne_gen D Sc (l ++ [i]) v j i (Ne.symm hij) (by simp) (by simp) (by simp) _ _

omit hij in
theorem push_u_P' :
    dotE D Sc (l ++ i :: i :: j :: v) (l.length) ≫ cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) =
      zsign k (D.parity i * D.parity j) • (cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) ≫ dotE D Sc (l ++ i :: j :: i :: v) (l.length)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  rw [show D.parity i * D.parity j = D.parity i * (D.parity i * D.parity j) by
    rw [← mul_assoc, parity_sq]]
  exact cl_interchange_gen D Sc l [] v (.dot i) (.cross i j) (by simp [Shape.dom])
    (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom]) (by simp [Shape.dom]) _ _

theorem push_v_P' :
    dotE D Sc (l ++ i :: i :: j :: v) (l.length + 1) ≫ cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) =
      zsign k (D.parity i * D.parity j) • (cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) ≫ dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  exact slide_left_ne_gen D Sc (l ++ [i]) v i j hij (by simp) (by simp) (by simp) _ _

theorem push_P1_u :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j) ≫ dotE D Sc (l ++ j :: i :: i :: v) (l.length + 1) =
      zsign k (D.parity i * D.parity j) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length) ≫ cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  exact eq_zsign_smul_symm (slide_left_ne_gen D Sc l (i :: v) i j hij rfl (by simp) (by simp) _ _)

omit hij in
theorem push_P1_v :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j) ≫ dotE D Sc (l ++ j :: i :: i :: v) (l.length + 2) =
      zsign k (D.parity i * D.parity j) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) ≫ cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  rw [show D.parity i * D.parity j = D.parity i * D.parity j * D.parity i by
    rw [mul_right_comm, parity_sq]]
  exact cl_interchange_gen D Sc l [] v (.cross i j) (.dot i) (by simp [Shape.dom])
    (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom]) (by simp [Shape.dom]) _ _

theorem push_u_P1' :
    dotE D Sc (l ++ j :: i :: i :: v) (l.length + 1) ≫ cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) =
      zsign k (D.parity i * D.parity j) • (cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) ≫ dotE D Sc (l ++ i :: j :: i :: v) (l.length)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  rw [mul_comm]
  exact eq_zsign_smul_symm (slide_right_ne_gen D Sc l (i :: v) j i (Ne.symm hij) rfl (by simp)
    (by simp) _ _)

omit hij in
theorem push_v_P1' :
    dotE D Sc (l ++ j :: i :: i :: v) (l.length + 2) ≫ cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) =
      zsign k (D.parity i * D.parity j) • (cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) ≫ dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2)) := by
  rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
  rw [show D.parity i * D.parity j = D.parity j * D.parity i * D.parity i by
    rw [mul_assoc, parity_sq, mul_comm]]
  exact eq_zsign_smul_symm (cl_interchange_gen D Sc l [] v (.cross j i) (.dot i)
    (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom]) (by simp [Shape.dom])
    _ _)

end Push


theorem crossSq_gen {t : List I} (l' r : List I) {i j : I} (hij : i ≠ j) (hd : D.d i j ≠ 0)
    (ht : t = l' ++ [i, j] ++ r) {p : ℕ} (hp : l'.length = p)
    (h : SChain t (pl t [.cross p, .cross p]) t) :
    cl D Sc t t [.cross p, .cross p] h =
      qLeft (dotE D Sc t p) (dotE D Sc t (p + 1)) (D.dn i j) (D.dn j i) (Sc.t i j : k)
        (Sc.t j i : k) (Sc.s i j) := by
  subst ht hp
  exact cross_cross_ne D Sc l' r hij hd h

theorem crossSq_zero_gen {t : List I} (l' r : List I) {i j : I} (hij : i ≠ j) (hd : D.d i j = 0)
    (ht : t = l' ++ [i, j] ++ r) {p : ℕ} (hp : l'.length = p)
    (h : SChain t (pl t [.cross p, .cross p]) t) :
    cl D Sc t t [.cross p, .cross p] h = (Sc.t i j : k) • 𝟙 _ := by
  subst ht hp
  exact cross_cross_ne_zero D Sc l' r hij hd h

theorem braid_iji_gen {t : List I} (l r : List I) {i j : I} (hij : i ≠ j)
    (ht : t = l ++ [i, j, i] ++ r) {p : ℕ} (hp : l.length = p)
    (h₁ : SChain t (pl t [.cross p, .cross (p + 1), .cross p]) t)
    (h₂ : SChain t (pl t [.cross (p + 1), .cross p, .cross (p + 1)]) t) :
    cl D Sc t t [.cross p, .cross (p + 1), .cross p] h₁ -
        cl D Sc t t [.cross (p + 1), .cross p, .cross (p + 1)] h₂ =
      braidCorr (fun r : ℕ => zsign k (D.parity i * (D.parity j + r))) (dotE D Sc t p)
        (dotE D Sc t (p + 1)) (dotE D Sc t (p + 2)) (D.dn i j) (D.dn j i) (Sc.t i j : k)
        (Sc.s i j) := by
  subst ht hp
  exact braid_iji D Sc l r hij h₁ h₂

section Main
variable (l v : List I) {i j : I} (hij : i ≠ j)
include hij

theorem conj_square_right (hd : D.d i j ≠ 0) :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫ cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) =
      qRight (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1)) (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2)) (D.dn i j) (D.dn j i) (Sc.t i j : k) (Sc.t j i : k) (Sc.s i j) := by
  have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).2 h)
  rw [cl_comp]
  refine (crossSq_gen D Sc (l ++ [i]) v (Ne.symm hij) hd' (p := l.length + 1) (by simp) (by simp)
    _).trans ?_
  exact qLeft_swap (B := End ((pres D Sc).obj (ob D (l ++ i :: j :: i :: v)))) _ _ _ _ _ _ _ _
    fun p q => Sc.s_symm j i p q

theorem conj_square_left (hd : D.d i j ≠ 0) :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j) ≫ cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) =
      qLeft (dotE D Sc (l ++ i :: j :: i :: v) (l.length)) (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1)) (D.dn i j) (D.dn j i) (Sc.t i j : k) (Sc.t j i : k) (Sc.s i j) := by
  rw [cl_comp]
  exact crossSq_gen D Sc l (i :: v) hij hd (by simp) rfl _

theorem conj_square_eq (hd : D.d i j = 0) :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫ cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) = cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j) ≫ cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) := by
  have hd' : D.d j i = 0 := (D.d_eq_zero_iff i j).1 hd
  rw [cl_comp, cl_comp]
  refine (crossSq_zero_gen D Sc (l ++ [i]) v (Ne.symm hij) hd' (p := l.length + 1) (by simp)
    (by simp) _).trans ?_
  refine Eq.trans ?_ (crossSq_zero_gen D Sc l (i :: v) hij hd (p := l.length) (by simp) rfl _).symm
  rw [Sc.t_symm_of_d_eq_zero i j hd]

theorem conj_braid :
    cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j) ≫ crossE D Sc (l ++ j :: i :: i :: v) (l.length + 1) ≫ cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) -
        cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫ crossE D Sc (l ++ i :: i :: j :: v) l.length ≫ cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) =
      braidCorr (fun r : ℕ => zsign k (D.parity i * (D.parity j + r))) (dotE D Sc (l ++ i :: j :: i :: v) (l.length)) (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1)) (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2))
        (D.dn i j) (D.dn j i) (Sc.t i j : k) (Sc.s i j) := by
  rw [crossE, crossE, genE_eq D Sc (sChain_cross (l ++ [j]) v i (by simp) (by simp)),
    genE_eq D Sc (sChain_cross l (j :: v) i (by simp) rfl), cl_comp, cl_comp, cl_comp, cl_comp]
  exact braid_iji_gen D Sc l v hij (by simp) rfl _ _


/-- KKO I (8.13) on colours `(i, j, i)` with `j ≠ i`: `τ_{a+1} g_a τ_{a+1} = τ_a g_{a+1} τ_a`. -/
theorem meet_iji : meetLeft D Sc l v i j i = meetRight D Sc l v i j i := by
  rw [meetLeft_iji D Sc l v hij, meetRight_iji D Sc l v hij]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  obtain ⟨Qr, hQr⟩ : ∃ Q : End ((pres D Sc).obj (ob D (l ++ i :: j :: i :: v))), cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫ cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) = Q := ⟨_, rfl⟩
  obtain ⟨Ql, hQl⟩ : ∃ Q : End ((pres D Sc).obj (ob D (l ++ i :: j :: i :: v))), cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j) ≫ cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) = Q := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T : End ((pres D Sc).obj (ob D (l ++ i :: j :: i :: v))),
      cl D Sc (l ++ i :: j :: i :: v) (l ++ i :: i :: j :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i j i) ≫ crossE D Sc (l ++ i :: i :: j :: v) l.length ≫ cl D Sc (l ++ i :: i :: j :: v) (l ++ i :: j :: i :: v) [.cross (l.length + 1)] (sChain_cross_succ l v i i j) = T := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T : End ((pres D Sc).obj (ob D (l ++ i :: j :: i :: v))),
      cl D Sc (l ++ i :: j :: i :: v) (l ++ j :: i :: i :: v) [.cross l.length] (sChain_iji_left l v i j) ≫ crossE D Sc (l ++ j :: i :: i :: v) (l.length + 1) ≫ cl D Sc (l ++ j :: i :: i :: v) (l ++ i :: j :: i :: v) [.cross l.length] (sChain_jii_left l v i j) = T := ⟨_, rfl⟩
  have hbr := conj_braid D Sc l v hij
  rw [hT1, hT2] at hbr
  have hm : ∀ f g : End ((pres D Sc).obj (ob D (l ++ i :: j :: i :: v))), f ≫ g = g * f := fun _ _ => rfl
  have hxy : dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) * dotE D Sc (l ++ i :: j :: i :: v) (l.length) = zsign k (D.parity i * D.parity i) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2)) :=
    genE_interchange D Sc l [j] v (.dot i) (.dot i) rfl rfl (by simp [Shape.dom]) rfl
      (by simp [Shape.dom])
  have hmx : dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1) * dotE D Sc (l ++ i :: j :: i :: v) (l.length) = zsign k (D.parity i * D.parity j) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1)) :=
    genE_interchange D Sc l [] (i :: v) (.dot i) (.dot j) rfl rfl (by simp [Shape.dom]) rfl
      (by simp [Shape.dom])
  have hym : dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1) = zsign k (D.parity j * D.parity i) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2)) :=
    genE_interchange D Sc (l ++ [i]) [] v (.dot j) (.dot i) rfl rfl (by simp [Shape.dom])
      (by simp) (by simp [Shape.dom])
  have hmy : dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) = zsign k (D.parity j * D.parity i) • (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1)) := by
    rw [hym, smul_smul, zsign_mul_self, one_smul]
  have hd0 : D.d i j = 0 → Qr = Ql ∧ T1 - T2 = 0 := fun hd => by
    have hdn : D.dn i j = 0 := by simp [SKM.Datum.dn, hd]
    refine ⟨by rw [← hQr, ← hQl]; exact conj_square_eq D Sc l v hij hd, ?_⟩
    rw [hbr, braidCorr, hdn]
    simp
  unfold sameIntertwiner
  by_cases hp : D.parity i = 1
  · simp only [eq_true hp, ↓reduceIte]
    rw [
      conj_element _ _ _ _ _ _ _ _ (zsign_mul_self _) (push_P_u D Sc l v) (push_P_v D Sc l v hij)
        (push_u_P' D Sc l v) (push_v_P' D Sc l v hij),
      conj_element _ _ _ _ _ _ _ _ (zsign_mul_self _) (push_P1_u D Sc l v hij) (push_P1_v D Sc l v)
        (push_u_P1' D Sc l v hij) (push_v_P1' D Sc l v),
      reassoc_of% hQr, reassoc_of% hQl, reassoc_of% hT2, reassoc_of% hT1]
    simp only [hm, OddNilHecke.Intertwiner.squareDiff]
    have key : zsign k (D.parity i * D.parity j) • ((dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) ^ 2 - dotE D Sc (l ++ i :: j :: i :: v) (l.length) ^ 2) * (Qr - Ql) * (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) - dotE D Sc (l ++ i :: j :: i :: v) (l.length))) +
        (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) ^ 2 - dotE D Sc (l ++ i :: j :: i :: v) (l.length) ^ 2) ^ 2 * (T1 - T2) = 0 := by
      by_cases hd : D.d i j = 0
      · obtain ⟨hQ, hT⟩ := hd0 hd
        simp only [hQ, hT, sub_self, mul_zero, zero_mul, smul_zero, add_zero]
      · rw [hbr, ← hQr, ← hQl, conj_square_right D Sc l v hij hd,
          conj_square_left D Sc l v hij hd, hp, one_mul]
        refine odd_poly ?_ ?_ _ _ _ ?_ _ _ fun r => by rw [one_mul]
        · rw [hxy, hp]; simp [zsign]
        · exact (Int.even_coe_nat _).1 (by rw [D.dn_cast hij]; exact D.even_d_of_odd hp j)
        · intro p q hne
          have h01 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          have hp' : (p : ZMod 2) = 0 := by
            by_contra hc
            exact hne (Sc.s_eq_zero i j p q (by rw [hp, mul_one]; exact h01 _ hc))
          have hq' : (q : ZMod 2) * D.parity j = 0 := by
            by_contra hc
            exact hne (by rw [Sc.s_symm]; exact Sc.s_eq_zero j i q p (h01 _ hc))
          refine ⟨(ZMod.natCast_eq_zero_iff_even).1 hp', ?_, ?_⟩
          · exact commute_pow_of_zsign _ hmx q (by rw [hp, one_mul]; exact hq')
          · exact commute_pow_of_zsign _ hmy q (by rw [hp, mul_one]; exact hq')
    exact fin_odd _ _ _ _ _ _ _ key
  · have hp0 : D.parity i = 0 := parity_eq_zero_of_ne_one hp
    have hσ : zsign k (D.parity i * D.parity j) = 1 := by rw [hp0, zero_mul]; simp [zsign]
    simp only [eq_false hp, ↓reduceIte]
    rw [
      conj_gEven _ _ _ _ _ _ _ _ (zsign_mul_self _) (push_u_P' D Sc l v) (push_v_P' D Sc l v hij),
      conj_gEven _ _ _ _ _ _ _ _ (zsign_mul_self _) (push_u_P1' D Sc l v hij) (push_v_P1' D Sc l v),
      reassoc_of% hQr, reassoc_of% hQl, reassoc_of% hT2, reassoc_of% hT1, hσ, one_smul, one_smul]
    simp only [hm]
    have key : (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) - dotE D Sc (l ++ i :: j :: i :: v) (l.length)) * (Qr - Ql) - (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) - dotE D Sc (l ++ i :: j :: i :: v) (l.length)) * (dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) - dotE D Sc (l ++ i :: j :: i :: v) (l.length)) * (T1 - T2) = 0 := by
      by_cases hd : D.d i j = 0
      · obtain ⟨hQ, hT⟩ := hd0 hd
        simp only [hQ, hT, sub_self, mul_zero]
      · rw [hbr, ← hQr, ← hQl, conj_square_right D Sc l v hij hd,
          conj_square_left D Sc l v hij hd]
        refine even_poly ?_ ?_ ?_ _ _ _ _ _ _ fun r => by rw [hp0, zero_mul]; simp [zsign]
        · show dotE D Sc (l ++ i :: j :: i :: v) (l.length) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) = dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) * dotE D Sc (l ++ i :: j :: i :: v) (l.length)
          rw [hxy, hp0]; simp [zsign]
        · show dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1) * dotE D Sc (l ++ i :: j :: i :: v) (l.length) = dotE D Sc (l ++ i :: j :: i :: v) (l.length) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1)
          rw [hmx, hp0]; simp [zsign]
        · show dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) = dotE D Sc (l ++ i :: j :: i :: v) (l.length + 2) * dotE D Sc (l ++ i :: j :: i :: v) (l.length + 1)
          rw [hmy, hp0]; simp [zsign]
    exact fin_even _ _ _ _ _ key

end Main

end Words

end IntertwinerMeet

section
variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- KKO I (8.13) on `i, j, i` with `j ≠ i`: `τ_{a+1} g_a τ_{a+1} = τ_a g_{a+1} τ_a`. -/
theorem meetLeft_eq_meetRight_iji (l v : List I) {i j : I} (hij : i ≠ j) :
    meetLeft D Sc l v i j i = meetRight D Sc l v i j i :=
  IntertwinerMeet.meet_iji D Sc l v hij

/-- The three-strand identity `τ_{a+1} g_a g_{a+1} = g_a g_{a+1} τ_a` for all colours. -/
theorem meetLeft_eq_all (l v : List I) (i j c : I) :
    meetLeft D Sc l v i j c = meetRight D Sc l v i j c := by
  by_cases hb : i = c ∧ i ≠ j
  · obtain ⟨rfl, hij⟩ := hb
    exact meetLeft_eq_meetRight_iji D Sc l v hij
  · exact meetLeft_eq D Sc l v hb

/-- The first identity of KKO (8.13) for every old crossing `ψ` of `j, c` in `ν`:
`ψ g_n ⋯ g_1 = (-1)^{p(j)p(c)p(i)p(ν)} g_n ⋯ g_1 ψ`. -/
theorem cross_comp_moveHom_all (v : List I) (i j c : I) (m l : List I) :
    cl D Sc _ _ [.cross (l.length + 1 + m.length)] (sChain_mid₁ l m v i j c) ≫
        moveHom D Sc i l (m ++ c :: j :: v) =
      zsign k (D.parity j * D.parity c * (D.parity i * (wordSumParity D m + wordSumParity D v))) •
        (moveHom D Sc i l (m ++ j :: c :: v) ≫
          cl D Sc _ _ [.cross (l.length + m.length)] (sChain_mid₂ l m v i j c)) :=
  cross_comp_moveHom D Sc v i j c (fun l' => meetLeft_eq_all D Sc l' v i j c) m l

end

end OddMath.QuiverHecke
