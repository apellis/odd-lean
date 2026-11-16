import OddMath.QuiverHecke.CyclotomicAction.SignedIntertwiner
import OddMath.QuiverHecke.ShuffleBasis
import OddMath.QuiverHecke.SerreWords
import OddMath.QuiverHecke.Spanning
import StringDiagrams.Super.Parity
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import StringDiagrams.Super.Envelope

/-!
# Intertwiner chains

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
  ∑ p ∈ Finset.range d, ∑ q ∈ Finset.range e, s p q • (u ^ p * m ^ q) + (t₁ • u ^ d + t₂ • m ^ e)

/-- The double crossing `Q_{ji}(m, w)` on strands of colours `j, i`, indexed as `Q_{ij}`. -/
def qRight (m w : B) (d e : ℕ) (t₁ t₂ : k) (s : ℕ → ℕ → k) : B :=
  ∑ p ∈ Finset.range d, ∑ q ∈ Finset.range e, s p q • (m ^ q * w ^ p) + (t₂ • m ^ e + t₁ • w ^ d)

/-- The correction term of the braid relation on `i, j, i`, with signs `ζ`. -/
def braidCorr (ζ : ℕ → k) (u m w : B) (d e : ℕ) (t₁ : k) (s : ℕ → ℕ → k) : B :=
  ∑ r ∈ Finset.range d, (ζ r * t₁) • (u ^ (d - 1 - r) * w ^ r) +
    ∑ p ∈ Finset.range d, ∑ q ∈ Finset.range e, ∑ r ∈ Finset.range p,
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
      ∑ p ∈ Finset.range d, ∑ q ∈ Finset.range e, s p q • (m ^ q * w ^ p - u ^ p * m ^ q) := by
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
end

end

section

/-!
# Balance of the moving-strand map on positioned words

Kang–Kashiwara–Oh, arXiv:1206.5933v2, (8.13) and Proposition 8.4: for every positioned word
`gs` on `ν` (a diagram of `R(β)`), placing it to the right of the moving strand `i` and then
applying `g_n ⋯ g_1` equals applying `g_n ⋯ g_1` and then `gs` on the first `n` strands, up to the
sign `(-1)^{p(gs) p(i) p(ν)}`. This is the balance needed for KKO's map
`Q : a e(β, i) ⊗ b ↦ a g_n ⋯ g_1 v(i, β) ⊗ π b` to be well defined over `R(β)`: the generator
cases are `dot_mem_comp_moveHom` and `cross_comp_moveHom_all`.

## Main results

* `chainParity`: the parity of a positioned word on a word `ν`.
* `gen_comp_moveHom`: the balance for one positioned generator.
* `cl_comp_moveHom`: the balance for every positioned word fitting in `ν`.
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams
open SKM (zsign)

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The parity of the positioned word `gs` read on the word `t`. -/
def chainParity : List I → List PG → ZMod 2
  | _, [] => 0
  | t, g :: gs => g.par D t + chainParity (g.act t) gs

@[simp] theorem chainParity_nil (t : List I) : chainParity D t [] = 0 := rfl

@[simp] theorem chainParity_cons (t : List I) (g : PG) (gs : List PG) :
    chainParity D t (g :: gs) = g.par D t + chainParity D (g.act t) gs := rfl

theorem cl_congr_gs {t t' : List I} {gs gs' : List PG} (hg : gs = gs')
    (h : SChain t (pl t gs) t') (h' : SChain t (pl t gs') t') :
    cl D Sc t t' gs h = cl D Sc t t' gs' h' := by
  subst hg
  rfl

theorem sChain_shift_one (i : I) {ν ν' : List I} {gs : List PG} (h : SChain ν (pl ν gs) ν') :
    SChain (i :: ν) (pl (i :: ν) (gs.map (PG.shift 1))) (i :: ν') := by
  have := sChain_wh h [i] []
  rw [show (1 : ℕ) = [i].length from rfl, show i :: ν = [i] ++ ν from rfl, pl_shift]
  simpa using this

theorem sChain_append_one (i : I) {ν ν' : List I} {gs : List PG} (h : SChain ν (pl ν gs) ν')
    (hfit : Fits ν.length gs) : SChain (ν ++ [i]) (pl (ν ++ [i]) gs) (ν' ++ [i]) := by
  rw [pl_append_right [i] hfit]
  simpa using sChain_wh h [] [i]

/-- KKO (8.13) for one positioned generator `g` of `R(β)`, together with the invariance of the
word parity. -/
theorem gen_comp_moveHom (i : I) {ν ν' : List I} (g : PG) (h : SChain ν (pl ν [g]) ν')
    (hfit : Fits ν.length [g]) :
    cl D Sc (i :: ν) (i :: ν') ([g].map (PG.shift 1)) (sChain_shift_one i h) ≫
        moveHom D Sc i [] ν' =
      zsign k (g.par D ν * (D.parity i * wordSumParity D ν)) •
        (moveHom D Sc i [] ν ≫ cl D Sc (ν ++ [i]) (ν' ++ [i]) [g] (sChain_append_one i h hfit)) ∧
      wordSumParity D ν' = wordSumParity D ν := by
  obtain ⟨m, s, v, hν, hg, -, -⟩ := exists_split g 0 ν (Nat.zero_le _)
    (by simpa using hfit g (by simp))
  subst hg
  have ht := tgt_eq h
  cases s with
  | dot x =>
    obtain rfl : ν = m ++ x :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ x :: v := by simpa [PG.ofShape, PG.act] using ht.symm
    refine ⟨?_, rfl⟩
    have key : dotE D Sc (i :: (m ++ x :: v)) ([].length + 1 + m.length) ≫
          moveHom D Sc i [] (m ++ x :: v) =
        zsign k (D.parity x * (D.parity i * wordSumParity D (m ++ x :: v))) •
          (moveHom D Sc i [] (m ++ x :: v) ≫ dotE D Sc (m ++ x :: v ++ [i]) ([].length + m.length)) :=
      dot_mem_comp_moveHom D Sc i x v m [] (m ++ x :: v) (by simp)
    rw [cl_congr_gs D Sc (t := i :: (m ++ x :: v)) (gs' := [.dot ([].length + 1 + m.length)])
        (by simp [PG.ofShape, PG.shift]) _ (sChain_dotAny _ _), ← dotE_eq_cl,
      cl_congr_gs D Sc (t := m ++ x :: v ++ [i]) (gs' := [.dot ([].length + m.length)])
        (by simp [PG.ofShape]) _ (sChain_dotAny _ _), ← dotE_eq_cl]
    have hp : PG.par D (m ++ x :: v) (PG.ofShape (Shape.dot x) (0 + m.length)) = D.parity x := by
      simp [PG.par, PG.ofShape]
    rw [hp]
    exact key
  | cross j c =>
    obtain rfl : ν = m ++ j :: c :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ c :: j :: v := by
      simpa [PG.ofShape, PG.act, List.take_append, List.drop_append] using ht.symm
    refine ⟨?_, ?_⟩
    · have key : cl D Sc (i :: (m ++ j :: c :: v)) (i :: (m ++ c :: j :: v))
            [.cross ([].length + 1 + m.length)] (sChain_mid₁ [] m v i j c) ≫
            moveHom D Sc i [] (m ++ c :: j :: v) =
          zsign k (D.parity j * D.parity c *
              (D.parity i * (wordSumParity D m + wordSumParity D v))) •
            (moveHom D Sc i [] (m ++ j :: c :: v) ≫
              cl D Sc (m ++ j :: c :: v ++ [i]) (m ++ c :: j :: v ++ [i])
                [.cross ([].length + m.length)] (sChain_mid₂ [] m v i j c)) :=
        cross_comp_moveHom_all D Sc v i j c m []
      rw [cl_congr_gs D Sc (t := i :: (m ++ j :: c :: v)) (t' := i :: (m ++ c :: j :: v))
          (gs' := [.cross ([].length + 1 + m.length)])
          (by simp [PG.ofShape, PG.shift, Nat.add_comm]) _ (sChain_mid₁ [] m v i j c),
        cl_congr_gs D Sc (t := m ++ j :: c :: v ++ [i]) (t' := m ++ c :: j :: v ++ [i])
          (gs' := [.cross ([].length + m.length)]) (by simp [PG.ofShape]) _
          (sChain_mid₂ [] m v i j c)]
      rw [key]
      congr 1
      have hp : PG.par D (m ++ j :: c :: v) (PG.ofShape (Shape.cross j c) (0 + m.length)) =
          D.parity j * D.parity c := by simp [PG.par, PG.ofShape]
      rw [hp]
      simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      generalize D.parity i = a
      generalize D.parity j = b
      generalize D.parity c = d
      generalize (List.map D.parity m).sum = e
      generalize (List.map D.parity v).sum = f
      congr 1
      revert a b d e f
      decide
    · simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      abel

/-- KKO (8.13) for every positioned word `gs` on `ν`: placed to the right of the moving strand,
it passes through `g_n ⋯ g_1` with the sign `(-1)^{p(gs) p(i) p(ν)}`. -/
theorem cl_comp_moveHom (i : I) : ∀ {ν ν' : List I} (gs : List PG) (h : SChain ν (pl ν gs) ν')
    (hfit : Fits ν.length gs),
    cl D Sc (i :: ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h) ≫
        moveHom D Sc i [] ν' =
      zsign k (chainParity D ν gs * (D.parity i * wordSumParity D ν)) •
        (moveHom D Sc i [] ν ≫ cl D Sc (ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h hfit)) ∧
      wordSumParity D ν' = wordSumParity D ν
  | ν, ν', [], h, _ => by
    obtain rfl : ν = ν' := h
    refine ⟨?_, rfl⟩
    simp [cl_nil, zsign]
  | ν, ν', g :: gs, h, hfit => by
    have h₁ : SChain ν (pl ν [g]) (g.act ν) := sChain_pl ν [g]
    have h₂ : SChain (g.act ν) (pl (g.act ν) gs) ν' := by
      have := tgt_eq h
      simpa [← this] using sChain_pl (g.act ν) gs
    have hfit₁ : Fits ν.length [g] := fun g' hg' => hfit g' (by simp_all)
    have hfit₂ : Fits (g.act ν).length gs := by
      rw [length_act]; exact fun g' hg' => hfit g' (by simp [hg'])
    obtain ⟨e₁, p₁⟩ := gen_comp_moveHom D Sc i g h₁ hfit₁
    obtain ⟨e₂, p₂⟩ := cl_comp_moveHom i gs h₂ hfit₂
    refine ⟨?_, p₂.trans p₁⟩
    have s₁ : cl D Sc (i :: ν) (i :: ν') ((g :: gs).map (PG.shift 1)) (sChain_shift_one i h) =
        cl D Sc (i :: ν) (i :: g.act ν) ([g].map (PG.shift 1)) (sChain_shift_one i h₁) ≫
          cl D Sc (i :: g.act ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h₂) := by
      rw [cl_comp]; rfl
    have s₂ : cl D Sc (ν ++ [i]) (ν' ++ [i]) (g :: gs) (sChain_append_one i h hfit) =
        cl D Sc (ν ++ [i]) (g.act ν ++ [i]) [g] (sChain_append_one i h₁ hfit₁) ≫
          cl D Sc (g.act ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h₂ hfit₂) := by
      rw [cl_comp]; rfl
    rw [s₁, s₂, Category.assoc, e₂, Linear.comp_smul, ← Category.assoc, e₁, Linear.smul_comp,
      smul_smul, Category.assoc, p₁, chainParity_cons, ← zsign_add_eq]
    congr 2
    ring
end OddMath.QuiverHecke
end

end

section

/-!
# Moving-strand balance on arbitrary morphisms

Kang–Kashiwara–Oh, arXiv:1206.5933v2, (8.13), the balance input to
Proposition 8.4. `hom_comp_moveHom` extends the positioned-word identity to
all morphisms of the presented quiver Hecke supercategory. The parity
involution is applied to the entire morphism, so no homogeneity hypothesis
is imposed. This is an input to the balanced map Q and subsequently the
QP identity of Theorem 8.5, not a construction of Q itself.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open Categorification.TypeA
open SKM (zsign)

variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- The parity of the layers of a fitting positioned generator. -/
theorem parity_ld_of_fits (t : List I) (g : PG) (hg : g.pos + g.width ≤ t.length) :
    ((g.ld t).map fun x => x.2.1.parity D).sum = g.par D t := by
  obtain ⟨l, s, r, rfl, hgs, -, -⟩ := exists_split g 0 t (Nat.zero_le _) (by simpa using hg)
  simp only [zero_add] at hgs
  subst hgs
  rw [par_ofShape]
  cases s <;> simp [PG.ld, PG.ofShape, Shape.dom, Shape.parity]

/-- The recursive word parity agrees with the diagram's parity. -/
theorem parity_pl_of_fits (t : List I) (gs : List PG) (hf : Fits t.length gs) :
    ((pl t gs).map fun x => x.2.1.parity D).sum = chainParity D t gs := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    rw [pl_cons, List.map_append, List.sum_append, parity_ld_of_fits D t g (hf g (by simp)),
      chainParity_cons, ih]
    intro g' hg'
    simpa using hf g' (by simp [hg'])

/-- Positioned words are homogeneous for their recursive parity. -/
theorem cl_mem_chainParity {t t' : List I} (gs : List PG)
    (h : SChain t (pl t gs) t') (hf : Fits t.length gs) :
    cl D Sc t t' gs h ∈ Supercategory.parity (R := k) _ _ (chainParity D t gs) := by
  have hd := (pres D Sc).diag_isHomogeneous (isParityHomogeneous D Sc) (mkD D (pl t gs) h)
  have he : Diagram.degree (Presentation.parityDeg (sig D)) (mkD D (pl t gs) h) =
      chainParity D t gs := by
    rw [Diagram.degree, layers_mkD]
    have hp : ∀ g : Shape I, Presentation.parityDeg (sig D) g = g.parity D := by
      intro g
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (g.parity D) with h | h <;>
        simp [Presentation.parityDeg, sig, h]
    simpa only [layList, List.map_map, Function.comp_def, lay, hp] using
      parity_pl_of_fits D t gs hf
  rw [he] at hd
  exact hd

/-- KKO (8.13) on arbitrary, possibly inhomogeneous, Hom entries. The twist
is `f₀ + (-1)^(p(i)p(t)) f₁`. -/
theorem hom_comp_moveHom (i : I) {t t' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    ((pres D Sc).obj (ob D [i]) ◁ f) ≫ moveHom D Sc i [] t' =
      moveHom D Sc i [] t ≫
        (Supercategory.twist k (D.parity i * wordSumParity D t) f ▷
          (pres D Sc).obj (ob D [i])) := by
  have hf : f ∈ Submodule.span k {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') |
      ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
        ∃ w : Equiv.Perm (Fin t.length),
          ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (canWord t.length w)) h = f} := by
    rw [span_normalForms]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, -, hl, w, h, rfl⟩ := hf
    have hfit := fits_append (fits_dots hl) (fits_cw (validWord_canWord t.length w))
    rw [Supercategory.twist_of_mem _ (cl_mem_chainParity D Sc _ h hfit),
      (MonoidalSupercategory.smul_whiskerRight (R := k)), Linear.comp_smul,
      cl_whiskerLeft, cl_whiskerRight D Sc _ h [i] hfit]
    have hs : ∀ p : ZMod 2, Supercategory.sign k p = zsign k p := by
      intro p
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) p with rfl | rfl <;>
        simp [Supercategory.sign, zsign]
    simpa only [List.singleton_append, List.length_singleton, hs, mul_comm] using
      (cl_comp_moveHom D Sc i _ h hfit).1
  | zero => simp [MonoidalSupercategory.whiskerLeft_zero (R := k),
      MonoidalSupercategory.zero_whiskerRight (R := k)]
  | add f g _ _ hf hg =>
    simp only [map_add, (MonoidalSupercategory.whiskerLeft_add (R := k)),
      (MonoidalSupercategory.add_whiskerRight (R := k)), Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | smul r f _ hf =>
    simp only [map_smul, (MonoidalSupercategory.whiskerLeft_smul (R := k)),
      (MonoidalSupercategory.smul_whiskerRight (R := k)), Linear.smul_comp,
      Linear.comp_smul, hf]

end OddMath.QuiverHecke
end

end

section

/-!
# Moving-strand elements in the finite-support Hom algebra

The colour-corner assembly of KKO I, arXiv:1206.5933v2, (8.13).
`contentMove_balance` is the algebra balance used to descend the map Q of
Proposition 8.4. Rows are targets, so multiplication reverses diagrammatic
composition. This module does not assert the tensor descent or the QP formula.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical

variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- Insertion of the distinguished strand on the left. -/
def prependWord (i : I) {n : ℕ} (w : Word I n) : Word I (n + 1) :=
  ⟨i :: w.1, by simp [w.2]⟩

theorem prependWord_injective (i : I) (n : ℕ) :
    Function.Injective (prependWord i (n := n)) := by
  intro a b h
  apply Subtype.ext
  exact List.cons.inj (congrArg Subtype.val h) |>.2

/-- Left insertion on each entry of the existing Hom algebra. -/
def prependHom (i : I) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k]
      (wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) where
  toFun f := (pres D Sc).obj (ob D [i]) ◁ f
  map_add' f g := MonoidalSupercategory.whiskerLeft_add (R := k) _ f g
  map_smul' c f := MonoidalSupercategory.whiskerLeft_smul (R := k) _ c f

/-- A single left-inserted entry, with its dependent Hom fibre explicit. -/
def prependEntry (i : I) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc (n + 1) where
  toFun f := FiniteHomMatrix.single (prependWord i t) (prependWord i s)
    (prependHom D Sc i s t f)
  map_add' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_add]
  map_smul' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_smul]

/-- The affine left insertion, extended by the matrix coordinate sum. -/
def prependLinear (i : I) (n : ℕ) : Hn D Sc n →ₗ[k] Hn D Sc (n + 1) :=
  DFinsupp.lsum k fun p => prependEntry D Sc i p.2 p.1

@[simp] theorem prependLinear_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    prependLinear D Sc i n (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single (prependWord i t) (prependWord i s)
        (prependHom D Sc i s t f) := by
  let : DecidableEq (Word I n) := Classical.decEq _
  let : DecidableEq (Word I (n + 1)) := Classical.decEq _
  exact DFinsupp.lsum_single (S := k)
    (fun p : Word I n × Word I n => prependEntry D Sc i p.2 p.1) (t, s) f

/-- Insert a parity-twisted Hom entry. -/
def homTwistEntry (p : ZMod 2) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc n where
  toFun f := FiniteHomMatrix.single t s (Supercategory.twist k p f)
  map_add' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_add]
  map_smul' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_smul]

/-- Parity involution on matrix entries; the exponent is uniform on a content block. -/
def homMatrixTwist (n : ℕ) (p : ZMod 2) : Hn D Sc n →ₗ[k] Hn D Sc n :=
  DFinsupp.lsum k fun q => homTwistEntry D Sc p q.2 q.1

@[simp] theorem homMatrixTwist_single (p : ZMod 2) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    homMatrixTwist D Sc n p (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single t s (Supercategory.twist k p f) := by
  let : DecidableEq (Word I n) := Classical.decEq _
  exact DFinsupp.lsum_single (S := k)
    (fun q : Word I n × Word I n => homTwistEntry D Sc p q.2 q.1) (t, s) f

theorem homMatrixTwist_twice (n : ℕ) (p : ZMod 2) (z : Hn D Sc n) :
    homMatrixTwist D Sc n p (homMatrixTwist D Sc n p z) = z := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs s t f => simp [Supercategory.twist_twist]

/-- Left insertion respects multiplication, including off-diagonal zero products. -/
def prependAlgebra (i : I) (n : ℕ) : Hn D Sc n →ₙₐ[k] Hn D Sc (n + 1) where
  toFun := prependLinear D Sc i n
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' a b := by
    induction a using FiniteHomMatrix.induction with
    | hz => simp
    | ha a b ha hb => simp [add_mul, ha, hb]
    | hs s t f =>
      induction b using FiniteHomMatrix.induction with
      | hz => simp
      | ha a b ha hb => simp [mul_add, ha, hb]
      | hs r q g =>
        by_cases h : t = r
        · subst r
          simp only [FiniteHomMatrix.single_mul_single, prependLinear_single]
          congr 1
          exact MonoidalSupercategory.whiskerLeft_comp (R := k) _ g f
        · have h' : prependWord i t ≠ prependWord i r := fun e => h (prependWord_injective i n e)
          simp [FiniteHomMatrix.single_mul_single_of_ne, h, h']

/-- Entrywise parity twisting is an algebra map. -/
def homMatrixTwistAlgebra (n : ℕ) (p : ZMod 2) : Hn D Sc n →ₙₐ[k] Hn D Sc n where
  toFun := homMatrixTwist D Sc n p
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' a b := by
    induction a using FiniteHomMatrix.induction with
    | hz => simp
    | ha a b ha hb => simp [add_mul, ha, hb]
    | hs s t f =>
      induction b using FiniteHomMatrix.induction with
      | hz => simp
      | ha a b ha hb => simp [mul_add, ha, hb]
      | hs r q g =>
        by_cases h : t = r
        · subst r
          simp [Supercategory.twist_comp]
        · simp [FiniteHomMatrix.single_mul_single_of_ne, h]

/-- The parity of an unordered colour content. -/
def contentSumParity (β : Multiset I) : ZMod 2 := (β.map D.parity).sum

theorem wordSumParity_eq_content {n : ℕ} (s : Word I n) :
    wordSumParity D s.1 = contentSumParity D (wordContent s) := rfl

variable [Fintype I]

/-- The sum of `g_n ⋯ g_1 e(i,ν)` over the words of content `β`. -/
def contentMove (i : I) (n : ℕ) (β : Multiset I) : Hn D Sc (n + 1) :=
  ∑ w ∈ Finset.univ.filter (fun w : Word I n => wordContent w = β),
    FiniteHomMatrix.single (appendWord i w) (prependWord i w) (moveHom D Sc i [] w.1)

private theorem contentMove_mul_entry (i : I) {n : ℕ} (β : Multiset I) (s t : Word I n)
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) :
    contentMove D Sc i n β * FiniteHomMatrix.single (prependWord i t) (prependWord i s) f =
      if wordContent t = β then
        FiniteHomMatrix.single (appendWord i t) (prependWord i s) (f ≫ moveHom D Sc i [] t.1)
      else 0 := by
  rw [contentMove, Finset.sum_mul]
  by_cases ht : wordContent t = β
  · rw [ite_eq_left ht, Finset.sum_eq_single t]
    · simp
    · intro b _ hb
      exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
        (fun h => hb (prependWord_injective i n h)) _ _
    · simp [ht]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro b hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    have he := prependWord_injective i n h
    subst b
    exact ht (Finset.mem_filter.mp hb).2

private theorem entry_mul_contentMove (i : I) {n : ℕ} (β : Multiset I) (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    FiniteHomMatrix.single (appendWord i t) (appendWord i s) f * contentMove D Sc i n β =
      if wordContent s = β then
        FiniteHomMatrix.single (appendWord i t) (prependWord i s) (moveHom D Sc i [] s.1 ≫ f)
      else 0 := by
  rw [contentMove, Finset.mul_sum]
  by_cases hs : wordContent s = β
  · rw [ite_eq_left hs, Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
        (fun h => hb (appendWord_injective i n h.symm)) _ _
    · simp [hs]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro b hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    have he := appendWord_injective i n h.symm
    subst b
    exact hs (Finset.mem_filter.mp hb).2

/-- KKO (8.13) as an equality in `Hn`, for arbitrary inhomogeneous algebra elements.
The exponent `p(i)p(β)` is the twist required by the shifted coefficient factor in Q. -/
theorem contentMove_balance (i : I) (n : ℕ) (β : Multiset I) (z : Hn D Sc n) :
    appendLinear D Sc i n (homMatrixTwist D Sc n (D.parity i * contentSumParity D β) z) *
        contentMove D Sc i n β =
      contentMove D Sc i n β * prependLinear D Sc i n z := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp only [map_add, add_mul, mul_add, ha, hb]
  | hs t s f =>
    rw [homMatrixTwist_single, appendLinear_single, prependLinear_single,
      entry_mul_contentMove, contentMove_mul_entry]
    by_cases h : wordContent s = wordContent t
    · rw [h]
      split_ifs with ht
      · congr 1
        have hp : wordSumParity D s.1 = contentSumParity D β := by
          rw [wordSumParity_eq_content, h, ht]
        simpa only [hp, appendHom, prependHom, LinearMap.coe_mk, AddHom.coe_mk,
          wordObj, prependWord, appendWord, List.nil_append, List.singleton_append] using
          (hom_comp_moveHom D Sc i f).symm
      · rfl
    · have hf := hom_eq_zero_of_content_ne D Sc h f
      subst f
      simp [appendHom, prependHom, MonoidalSupercategory.whiskerLeft_zero (R := k),
        MonoidalSupercategory.zero_whiskerRight (R := k)]

end OddMath.QuiverHecke
end

end

section

/-!
# Balanced tensor descent of the moving-strand element

The underlying left-module map of KKO I, arXiv:1206.5933v2, Proposition 8.4.
We use the existing `InductionAlong.Ind` balanced tensor, not a free tensor.
The parity involution is placed on the right action of the first factor:
`a ⋅ r = a ξ(φ_i^{p(β)}(r))`. Moving this involution to the coefficient
factor gives the action underlying `Π_i^{p(β)} R^Λ(β)`.

`contentQ` descends for every coefficient module, hence also for the
cyclotomic quotient. It is the content-β component in the height algebra;
the other content blocks map to zero. No projectivity or flatness is used.
This module does not supply the parity grading or the signed right `t_i`
action, and therefore does not assert the full superbimodule proposition.
-/

noncomputable section
namespace OddMath.QuiverHecke
open Categorification

variable {I k X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Left insertion with the coefficient parity twist moved to the right action. -/
def twistedPrepend (i : I) (n : ℕ) (β : Multiset I) : Hn D Sc n →ₙ+* Hn D Sc (n + 1) :=
  (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)).comp
    (homMatrixTwistAlgebra D Sc n (D.parity i * contentSumParity D β) :
      Hn D Sc n →ₙ+* Hn D Sc n)

/-- The proved corner balance, with the involution on the target right action. -/
theorem contentMove_intertwines (i : I) (n : ℕ) (β : Multiset I) :
    InductionAlong.Intertwines (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))
      (twistedPrepend D Sc i n β) (contentMove D Sc i n β) := by
  intro z
  have h := contentMove_balance D Sc i n β
    (homMatrixTwist D Sc n (D.parity i * contentSumParity D β) z)
  rw [homMatrixTwist_twice] at h
  exact h

/-- The moving-strand map on the balanced tensor quotient, not just its free generators. -/
def contentQ (i : I) (n : ℕ) (β : Multiset I)
    (N : Type*) [AddCommGroup N] [Module (Hn D Sc n) N] :
    InductionAlong.Ind N (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) →ₗ[Hn D Sc (n + 1)]
      InductionAlong.Ind N (twistedPrepend D Sc i n β) :=
  InductionAlong.natMap (contentMove_intertwines D Sc i n β)

/-- On a pure balanced tensor the map is `a ⊗ b ↦ a G_β ⊗ b`. -/
@[simp] theorem contentQ_tmul (i : I) (n : ℕ) (β : Multiset I)
    (N : Type*) [AddCommGroup N] [Module (Hn D Sc n) N]
    (a : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) (b : N) :
    contentQ D Sc i n β N (InductionAlong.Ind.tmul a b) =
      InductionAlong.Ind.tmul
        (InductionAlong.cornerMul (contentMove_intertwines D Sc i n β) a) b := rfl

/-- Specialization to the actual cyclotomic quotient coefficient module. -/
def cyclotomicContentQ (i : I) (n : ℕ) (β : Multiset I)
    (a : I → _root_.Polynomial k) :=
  contentQ D Sc i (n + 1) β (CyclotomicAlgebra D Sc a n)

end OddMath.QuiverHecke
end

end

section

/-!
# The parity-shifted coefficient target of the moving-strand map

The coefficient target of KKO I, arXiv:1206.5933v2, Proposition 8.4 is
`Π_i^{p(β)} R^Λ(β)`. We use the existing superbimodule parity shift and its
canonical homogeneous isomorphism. `qCoefficientInsert_smul` proves the
semilinear identity needed to move the involution from the corner action
to that coefficient action. `parityCyclotomicContentQ` is the composition
of this transfer with the already constructed balanced map `contentQ`.

The coefficient parity is proved by `qCoefficientInsert_mem`. This file
does not yet equip the induced tensor carrier with its super grading or
construct the signed right `t_i` actions. In particular it does not assert
full Proposition 8.4, a superbimodule map, or any QP formula. The content
projection, finite-colour hypothesis and positive-height quotient indexing
are unchanged. Polynomial parity is used only for the coefficient grading.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The coefficient superbimodule in KKO I, Proposition 8.4. -/
def qCoefficient (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :=
  Envelope.piPow k (D.parity i * contentSumParity D β)
    (SuperBimodule.regular (cyclotomicParity D Sc a ha n))

instance qCoefficientModule (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    Module (Hn D Sc (n + 1)) (qCoefficient D Sc i β a ha n).toSVec where
  smul r b := (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n r) b
  one_smul b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n 1) b = b
    rw [map_one, SuperBimodule.lact_one]
    rfl
  mul_smul r s b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n (r * s)) b = _
    rw [map_mul, SuperBimodule.lact_mul]
    rfl
  smul_zero r := SVec.hom_map_zero _
  smul_add r b c := SVec.hom_map_add _ b c
  zero_smul b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n 0) b = 0
    rw [map_zero, map_zero]
    rfl
  add_smul r s b := by
    change (qCoefficient D Sc i β a ha n).lact (cyclotomicMk D Sc a n (r + s)) b = _
    rw [map_add, map_add]
    rfl

/-- The canonical coefficient insertion, with parity `p(i)p(β)`. -/
def qCoefficientInsert (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    CyclotomicAlgebra D Sc a n →ₗ[k] (qCoefficient D Sc i β a ha n).toSVec :=
  SVec.toLinearMap (Envelope.ζPow k (D.parity i * contentSumParity D β)
    (SuperBimodule.regular (cyclotomicParity D Sc a ha n))).inv.1

/-- The canonical insertion uses the existing parity-shift isomorphism. -/
@[simp] theorem qCoefficientInsert_apply (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (b : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n b =
      (Envelope.ζPow k (D.parity i * contentSumParity D β)
        (SuperBimodule.regular (cyclotomicParity D Sc a ha n))).inv.1 b := rfl

/-- The entrywise involution is the scalar sign on a homogeneous element. -/
theorem homMatrixTwist_of_affineParity (n : ℕ) (p q : ZMod 2) (r : Hn D Sc n)
    (hr : r ∈ affineParity D Sc n q) :
    homMatrixTwist D Sc n p r = Supercategory.sign k (p * q) • r := by
  classical
  rw [FiniteHomMatrix.eq_sum_single r, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [homMatrixTwist_single, Supercategory.twist_of_mem p (hr t)]
  exact FiniteHomMatrix.single_smul _ _ _ _

/-- Moving the involution from the corner action to the shifted coefficient. -/
theorem qCoefficientInsert_smul (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (r : Hn D Sc (n + 1))
    (b : CyclotomicAlgebra D Sc a n) :
    qCoefficientInsert D Sc i β a ha n (r • b) =
      homMatrixTwist D Sc (n + 1) (D.parity i * contentSumParity D β) r •
        qCoefficientInsert D Sc i β a ha n b := by
  induction r using SuperBimodule.alg_induction_on (affineParity D Sc (n + 1)) with
  | zero => simp
  | add r s hr hs => simp only [add_smul, map_add, hr, hs]
  | hom p r hr =>
    let V := SuperBimodule.regular (cyclotomicParity D Sc a ha n)
    let e := Envelope.ζPow k (D.parity i * contentSumParity D β) V
    have he : e.inv.1 ∈ Supercategory.parity (R := k) V.toSVec
        (qCoefficient D Sc i β a ha n).toSVec (D.parity i * contentSumParity D β) :=
      SuperBimodule.mem_parity_iff.mp (Envelope.ζPow_inv_mem (R := k)
        (D.parity i * contentSumParity D β) V)
    have hf := (SuperBimodule.isHom_iff_of_mem he).mp e.inv.2
    have h := congrArg (fun f => f b)
      (hf.1 p (cyclotomicMk D Sc a n r) (cyclotomicMk_parity D Sc a ha n hr))
    rw [homMatrixTwist_of_affineParity D Sc _ _ _ _ hr]
    change _ = (qCoefficient D Sc i β a ha n).lact
      (cyclotomicMk D Sc a n (Supercategory.sign k
        ((D.parity i * contentSumParity D β) * p) • r))
      (qCoefficientInsert D Sc i β a ha n b)
    rw [map_smul (cyclotomicMk D Sc a n),
      map_smul (qCoefficient D Sc i β a ha n).lact]
    have hrb : V.lact (cyclotomicMk D Sc a n r) b = r • b := by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
      rfl
    simp only [mul_comm p, SVec.comp_apply, SVec.smul_apply,
      hrb, qCoefficientInsert_apply, V, e] at h ⊢
    convert h using 1

open Categorification MulOpposite

@[simp] theorem homMatrixTwist_one (n : ℕ) (p : ZMod 2) :
    homMatrixTwist D Sc n p 1 = 1 := by
  have h := (homMatrixTwistAlgebra D Sc n p).map_mul 1 (homMatrixTwist D Sc n p 1)
  change homMatrixTwist D Sc n p (1 * homMatrixTwist D Sc n p 1) =
    homMatrixTwist D Sc n p 1 * homMatrixTwist D Sc n p (homMatrixTwist D Sc n p 1) at h
  simpa only [one_mul, homMatrixTwist_twice, mul_one] using h.symm

/-- The parity twist fixes the corner idempotent. -/
def qPrependCorner (i : I) (n : ℕ) (β : Multiset I) :
    InductionAlong.Corner (twistedPrepend D Sc i n β) →ₗ[Hn D Sc (n + 1)]
      InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun x := ⟨x.1, by
    change x.1 * prependAlgebra D Sc i n 1 = x.1
    have h := x.2
    change x.1 * prependAlgebra D Sc i n (homMatrixTwist D Sc n
      (D.parity i * contentSumParity D β) 1) = x.1 at h
    simpa only [homMatrixTwist_one] using h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical transfer to the actual parity-shifted coefficient carrier. -/
def qCoefficientTransfer (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    InductionAlong.Ind (CyclotomicAlgebra D Sc a n) (twistedPrepend D Sc i (n + 1) β)
      →ₗ[Hn D Sc (n + 1 + 1)]
    InductionAlong.Ind (qCoefficient D Sc i β a ha n).toSVec
      (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)) :=
  InductionAlong.Ind.lift
    (fun x b => InductionAlong.Ind.tmul (qPrependCorner D Sc i (n + 1) β x)
      (qCoefficientInsert D Sc i β a ha n b))
    (by intros; rw [map_add, InductionAlong.Ind.add_tmul])
    (by intros; rw [map_add, InductionAlong.Ind.tmul_add])
    (by
      intro x r b
      have h : qPrependCorner D Sc i (n + 1) β (op r • x) =
          op (homMatrixTwist D Sc (n + 1) (D.parity i * contentSumParity D β) r) •
            qPrependCorner D Sc i (n + 1) β x := rfl
      rw [h, InductionAlong.Ind.op_smul_tmul, qCoefficientInsert_smul])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

/-- The existing quotient-descended map, now with the coefficient shift in its target. -/
def parityCyclotomicContentQ (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :=
  (qCoefficientTransfer D Sc i β a ha n).comp (cyclotomicContentQ D Sc i n β a)

/-- The refined map retains the actual moving-strand representative. -/
@[simp] theorem parityCyclotomicContentQ_tmul (i : I) (β : Multiset I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (x : InductionAlong.Corner
      (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1)))
    (b : CyclotomicAlgebra D Sc a n) :
    parityCyclotomicContentQ D Sc i β a ha n (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul
        (qPrependCorner D Sc i (n + 1) β
          (InductionAlong.cornerMul (contentMove_intertwines D Sc i (n + 1) β) x))
        (qCoefficientInsert D Sc i β a ha n b) := rfl

end OddMath.QuiverHecke
end

end

section

/-!
# Total parity on the induced tensors of the moving-strand map

The source and target of KKO I, arXiv:1206.5933v2, Proposition 8.4 use
`InductionAlong.Ind`, whose underlying tensor is over the integers. We put the
sum parity on that integral tensor and prove the existing balancing submodule
is homogeneous. Restricting its scalars to `k` does not change the quotient
carrier. In particular no comparison equivalence or replacement tensor is assumed.

`qSourceSpace` and `qTargetSpace` equip the existing induced modules with their
parity grading; the latter uses the already constructed `Envelope.piPow`
coefficient. The component degrees and homogeneous left action are proved.
The grading hypotheses for the concrete modules follow from affine inclusion
parity and the actual coefficient actions. The finite-colour, positive-height,
and `CyclotomicPolynomialParity` restrictions are unchanged. These ordinary
polynomial coefficients do not cover arbitrary odd-coefficient deformations.

`contentMove_parity` derives the moving-strand degree from the local generators.
`parityCyclotomicContentQ_even` proves that Q preserves these gradings: the
corner degree and coefficient shift cancel. This does not establish full
Proposition 8.4, the full right-superalgebra action, or a QP formula.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.InducedParity
universe u
variable {k : Type u} [CommRing k] (V W : SVec k)

/-- The integral tensor map, linear for the scalar action on its first factor. -/
def tensorMap (f : V →ₗ[k] V) (g : W →ₗ[k] W) :
    (V ⊗[ℤ] W) →ₗ[k] (V ⊗[ℤ] W) where
  toFun := TensorProduct.map (InductionAlong.intLinear f.toAddMonoidHom)
    (InductionAlong.intLinear g.toAddMonoidHom)
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [TensorProduct.smul_tmul', InductionAlong.intLinear]
    | add s t hs ht => simp only [smul_add, map_add, hs, ht]

@[simp] theorem tensorMap_tmul (f : V →ₗ[k] V) (g : W →ₗ[k] W) (x : V) (y : W) :
    tensorMap V W f g (x ⊗ₜ[ℤ] y) = f x ⊗ₜ[ℤ] g y := rfl

/-- Total parity on the integral tensor used by `InductionAlong.Ind`. -/
def tensorSpace : SVec k where
  carrier := V ⊗[ℤ] W
  odd := tensorMap V W (V.proj 0) (W.proj 1) + tensorMap V W (V.proj 1) (W.proj 0)
  odd_comp_odd := by
    ext x y
    simp [tensorMap_tmul, SVec.proj_proj_apply, SVec.proj_zero_proj_one,
      SVec.proj_one_proj_zero]

@[simp] theorem tensorSpace_odd_tmul (x : V) (y : W) :
    (tensorSpace V W).odd (x ⊗ₜ[ℤ] y) =
      V.proj 0 x ⊗ₜ[ℤ] W.proj 1 y + V.proj 1 x ⊗ₜ[ℤ] W.proj 0 y := rfl

theorem tensorSpace_tmul_mem {p q : ZMod 2} {x : V} {y : W}
    (hx : x ∈ V.part p) (hy : y ∈ W.part q) :
    x ⊗ₜ[ℤ] y ∈ (tensorSpace V W).part (p + q) := by
  have hx' := SVec.proj_apply_of_mem_part (p := 1) V hx
  have hy' := SVec.proj_apply_of_mem_part (p := 1) W hy
  rw [SVec.proj_one] at hx' hy'
  rw [SVec.mem_part_iff (tensorSpace V W)]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp_all [SVec.proj, tensorSpace_odd_tmul]

theorem induction_on {P : V → Prop} (x : V)
    (hom : ∀ p x, x ∈ V.part p → P x)
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  rw [← V.proj_apply_add x]
  exact add _ _ (hom _ _ (V.proj_mem_part 0 x)) (hom _ _ (V.proj_mem_part 1 x))

section Balance
variable {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]
  [Module B V] [IsScalarTower k B V] [Module Aᵐᵒᵖ V] [Module A W]
  [SMulCommClass B Aᵐᵒᵖ V]
  (hR : ∀ (p q : ZMod 2) (a : A) (x : V), a ∈ 𝒜 p → x ∈ V.part q →
    MulOpposite.op a • x ∈ V.part (q + p))
  (hL : ∀ (p q : ZMod 2) (a : A) (y : W), a ∈ 𝒜 p → y ∈ W.part q →
    a • y ∈ W.part (p + q))

include hR hL in
omit [GradedAlgebra 𝒜] in
/-- Homogeneous balancing generators have the same total parity on both sides. -/
theorem relation_mem {p q r : ZMod 2} {a : A} {x : V} {y : W}
    (ha : a ∈ 𝒜 p) (hx : x ∈ V.part q) (hy : y ∈ W.part r) :
    (MulOpposite.op a • x) ⊗ₜ[ℤ] y - x ⊗ₜ[ℤ] (a • y) ∈
      (tensorSpace V W).part (q + p + r) := by
  apply Submodule.sub_mem
  · exact tensorSpace_tmul_mem V W (hR p q a x ha hx) hy
  · simpa only [add_assoc] using tensorSpace_tmul_mem V W hx (hL p r a y ha hy)

include hR hL in
omit [Algebra k B] [IsScalarTower k B V] in
/-- Stability of the original integral balancing submodule under total parity. -/
theorem relation_odd_mem (t : V ⊗[ℤ] W)
    (ht : t ∈ BalancedTensor.rel ℤ B A V W) :
    (tensorSpace V W).odd t ∈ BalancedTensor.rel ℤ B A V W := by
  have hs : ∀ x : V, ∀ a : A, ∀ y : W,
      (tensorSpace V W).odd ((MulOpposite.op a • x) ⊗ₜ[ℤ] y - x ⊗ₜ[ℤ] (a • y)) ∈
        BalancedTensor.rel ℤ B A V W := by
    intro x a y
    induction x using induction_on V with
    | add x x' hx hx' =>
      simpa only [smul_add, TensorProduct.add_tmul, add_sub_add_comm, map_add] using
        (BalancedTensor.rel ℤ B A V W).add_mem hx hx'
    | hom q x hx =>
      induction a using SuperBimodule.alg_induction_on 𝒜 with
      | zero => simp
      | add a a' ha ha' =>
        simpa only [MulOpposite.op_add, map_add, add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add,
          add_sub_add_comm] using (BalancedTensor.rel ℤ B A V W).add_mem ha ha'
      | hom p a ha =>
        induction y using induction_on W with
        | add y y' hy hy' =>
          simpa only [smul_add, TensorProduct.tmul_add, add_sub_add_comm, map_add] using
            (BalancedTensor.rel ℤ B A V W).add_mem hy hy'
        | hom r y hy =>
          have hd := relation_mem V W 𝒜 hR hL ha hx hy
          have he := SVec.proj_apply_of_mem_part (p := 1) _ hd
          rw [SVec.proj_one] at he
          rw [he]
          split_ifs
          · exact Submodule.subset_span ⟨x, a, y, rfl⟩
          · exact Submodule.zero_mem _
  have ht' : t ∈ Submodule.span ℤ (BalancedTensor.relSet ℤ A V W) := by
    rw [← BalancedTensor.rel_restrictScalars ℤ B A V W]
    exact ht
  clear ht
  induction ht' using Submodule.span_induction with
  | mem t ht => obtain ⟨x, a, y, rfl⟩ := ht; exact hs x a y
  | zero => simp
  | add s t _ _ hs ht => simpa only [map_add] using (BalancedTensor.rel ℤ B A V W).add_mem hs ht
  | smul c t _ ht =>
    rw [map_zsmul]
    exact Submodule.smul_of_tower_mem _ c ht

/-- The same balancing relation, with its proved parity stability. -/
def balanceGraded : SVec.GradedSubmodule (tensorSpace V W) where
  toSubmodule := (BalancedTensor.rel ℤ B A V W).restrictScalars k
  odd_mem := relation_odd_mem V W 𝒜 hR hL

/-- Total parity descended to the existing balanced tensor carrier. -/
def balancedSpace : SVec k := SVec.quot (tensorSpace V W) (balanceGraded (B := B) V W 𝒜 hR hL)

end Balance
section Corner
variable {A B : Type u} [Ring A] [Ring B] [Algebra k B]
  (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ]
  (φ : A →ₙ+* B) (he : φ 1 ∈ ℬ 0)

include he in
/-- The corner is stable under every parity projection since its idempotent is even. -/
theorem corner_proj_mem (p : ZMod 2) (x : InductionAlong.Corner φ) :
    SuperBimodule.algProj ℬ p x.val ∈ Categorification.lIdeal (φ 1) := by
  have h := SVec.apply_proj_of_mem ((SuperBimodule.regular ℬ).ract_mem 0 (φ 1) he) p x.val
  change (SuperBimodule.regularSVec ℬ).proj p x.val * φ 1 =
    (SuperBimodule.regularSVec ℬ).proj (p + 0) (x.val * φ 1) at h
  rw [add_zero, SuperBimodule.regularSVec_proj] at h
  change SuperBimodule.algProj ℬ p x.val * φ 1 = SuperBimodule.algProj ℬ p x.val
  rw [h, x.property]

/-- Parity on the original left-ideal subtype, without changing the corner carrier. -/
abbrev cornerSpace : SVec k where
  carrier := InductionAlong.Corner φ
  odd :=
    { toFun x := ⟨SuperBimodule.algProj ℬ 1 x.val, corner_proj_mem ℬ φ he 1 x⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' c x := Subtype.ext (map_smul _ _ _) }
  odd_comp_odd := by
    ext x
    exact SuperBimodule.algProj_of_mem ℬ (SuperBimodule.algProj_mem ℬ 1 x.val)

theorem cornerSpace_proj (p : ZMod 2) (x : InductionAlong.Corner φ) :
    ((cornerSpace ℬ φ he).proj p x).val = SuperBimodule.algProj ℬ p x.val := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change x.val - SuperBimodule.algProj ℬ 1 x.val = SuperBimodule.algProj ℬ 0 x.val
    exact sub_eq_iff_eq_add.mpr (SuperBimodule.algProj_add_algProj ℬ x.val).symm
  · rfl

theorem cornerSpace_mem {p : ZMod 2} {x : InductionAlong.Corner φ} :
    x ∈ (cornerSpace ℬ φ he).part p ↔ x.val ∈ ℬ p := by
  rw [SVec.mem_part_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [cornerSpace_proj] at h'
    rw [← h']
    exact SuperBimodule.algProj_mem ℬ p x.val
  · intro h
    apply Subtype.ext
    rw [cornerSpace_proj, SuperBimodule.algProj_of_mem ℬ h]
end Corner
section Ind
variable {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (𝒜 : ZMod 2 → Submodule k A) [GradedAlgebra 𝒜]
  (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ]
  (φ : A →ₙ+* B) (hφ : ∀ p a, a ∈ 𝒜 p → φ a ∈ ℬ p)
  [Module A W]
  (hW : ∀ (p q : ZMod 2) (a : A) (y : W), a ∈ 𝒜 p → y ∈ W.part q →
    a • y ∈ W.part (p + q))

abbrev indSpace : SVec k :=
  balancedSpace (B := B)
    (cornerSpace ℬ φ (hφ 0 1 (SetLike.one_mem_graded 𝒜))) W 𝒜
    (fun p _q a _x ha hx => (cornerSpace_mem ℬ φ _).mpr
      (SetLike.GradedMul.mul_mem ((cornerSpace_mem ℬ φ _).mp hx) (hφ p a ha))) hW

end Ind
end OddMath.QuiverHecke.InducedParity
namespace OddMath.QuiverHecke
universe v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

omit [Fintype I] in
/-- The prepend algebra map preserves affine parity. -/
theorem prependAlgebra_parity (i : I) (n : ℕ) {p : ZMod 2} {x : Hn D Sc n}
    (hx : x ∈ affineParity D Sc n p) :
    prependAlgebra D Sc i n x ∈ affineParity D Sc (n + 1) p := by
  classical
  change prependLinear D Sc i n x ∈ _
  rw [FiniteHomMatrix.eq_sum_single x, map_sum]
  apply Submodule.sum_mem
  intro q _
  rw [prependLinear_single]
  apply FiniteHomMatrix.single_mem_component
  exact MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [i])) (hx q)

/-- The coefficient action used by source induction respects quotient parity. -/
theorem cyclotomicCoefficient_smul_mem (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p q : ZMod 2)
    (r : Hn D Sc (n + 1)) (b : CyclotomicAlgebra D Sc a n)
    (hr : r ∈ affineParity D Sc (n + 1) p) (hb : b ∈ cyclotomicParity D Sc a ha n q) :
    r • b ∈ cyclotomicParity D Sc a ha n (p + q) := by
  have h : r • b = cyclotomicMk D Sc a n r * b := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    rfl
  rw [h]
  exact SetLike.GradedMul.mul_mem (cyclotomicMk_parity D Sc a ha n hr) hb

/-- The shifted coefficient action respects its shifted grading. -/
theorem qCoefficient_smul_mem (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (p q : ZMod 2)
    (r : Hn D Sc (n + 1)) (b : (qCoefficient D Sc i β a ha n).toSVec)
    (hr : r ∈ affineParity D Sc (n + 1) p)
    (hb : b ∈ (qCoefficient D Sc i β a ha n).toSVec.part q) :
    r • b ∈ (qCoefficient D Sc i β a ha n).toSVec.part (p + q) := by
  have h := SVec.apply_mem_part ((qCoefficient D Sc i β a ha n).lact_mem p
    (cyclotomicMk D Sc a n r) (cyclotomicMk_parity D Sc a ha n hr)) hb
  rw [add_comm q p] at h
  convert h using 1

/-- Total parity on the source induced tensor of Q, on its existing carrier. -/
def qSourceSpace (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) : SVec k :=
  let : Module (Hn D Sc (n + 1)) (cyclotomicSuperspace D Sc a ha n) :=
    inferInstanceAs (Module (Hn D Sc (n + 1)) (CyclotomicAlgebra D Sc a n))
  InducedParity.indSpace (cyclotomicSuperspace D Sc a ha n)
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (appendAlgebra D Sc i (n + 1)) (fun _ _ h => appendAlgebra_parity D Sc i (n + 1) h)
    (cyclotomicCoefficient_smul_mem D Sc a ha n)

/-- Total parity on the target with the canonical coefficient shift of Q. -/
def qTargetSpace (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) : SVec k :=
  InducedParity.indSpace (qCoefficient D Sc i β a ha n).toSVec
    (affineParity D Sc (n + 1)) (affineParity D Sc (n + 1 + 1))
    (prependAlgebra D Sc i (n + 1)) (fun _ _ h => prependAlgebra_parity D Sc i (n + 1) h)
    (qCoefficient_smul_mem D Sc i β a ha n)

omit [Fintype I] in
theorem positionedDot_parity (l r : List I) (i : I) :
    dotE D Sc (l ++ i :: r) l.length ∈ parity (R := k) _ _ (D.parity i) := by
  rw [dotE_eq]
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, pl, PG.ld, Shape.parity]

omit [Fintype I] in
theorem positionedCross_parity (l r : List I) (i j : I) :
    cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j) ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  apply Presentation.diag_mem_homDeg'
  simp [degree_parity_mkD, pl, PG.ld, Shape.parity]

private theorem end_mul_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A : C} {p q : ZMod 2} {x y : End A}
    (hx : x ∈ parity (R := k) A A p) (hy : y ∈ parity (R := k) A A q) :
    x * y ∈ parity (R := k) A A (p + q) := by
  simpa only [End.mul_def, add_comm] using Supercategory.comp_mem hy hx

private theorem gEven_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A : C} {x y t : End A}
    (hx : x ∈ parity (R := k) A A 0) (hy : y ∈ parity (R := k) A A 0)
    (ht : t ∈ parity (R := k) A A 0) :
    SignedNilHecke.gEven x y t ∈ parity (R := k) A A 0 := by
  have hd := Submodule.sub_mem _ hy hx
  have hp : (y - x) * t ∈ parity (R := k) A A 0 := end_mul_parity hd ht
  exact end_mul_parity hd (Submodule.add_mem _ (Supercategory.id_mem A) hp)

private theorem gOdd_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {A : C} {x y t : End A}
    (hx : x ∈ parity (R := k) A A 1) (hy : y ∈ parity (R := k) A A 1)
    (ht : t ∈ parity (R := k) A A 1) :
    OddNilHecke.Intertwiner.element x y t ∈ parity (R := k) A A 1 := by
  have hs : OddNilHecke.Intertwiner.squareDiff x y ∈ parity (R := k) A A 0 := by
    simpa only [OddNilHecke.Intertwiner.squareDiff, pow_two,
      show (1 : ZMod 2) + 1 = 0 by decide] using
      Submodule.sub_mem _ (end_mul_parity hy hy) (end_mul_parity hx hx)
  exact Submodule.sub_mem _ (end_mul_parity hs (Submodule.sub_mem _ hy hx))
    (end_mul_parity (show OddNilHecke.Intertwiner.squareDiff x y ^ 2 ∈ parity (R := k) A A 0 by
      simpa only [pow_two, zero_add] using end_mul_parity hs hs) ht)

omit [Fintype I] in
theorem intertwinerHom_parity (l r : List I) (i j : I) :
    intertwinerHom D Sc l r i j ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [intertwinerHom_self]
    have hx := positionedDot_parity D Sc l (i :: r) i
    have hy : dotE D Sc (l ++ i :: i :: r) (l.length + 1) ∈
        parity (R := k) _ _ (D.parity i) := by
      have e : (l ++ [i]) ++ i :: r = l ++ i :: i :: r := by simp
      have h := positionedDot_parity D Sc (l ++ [i]) r i
      rw [e] at h
      simpa only [List.length_append, List.length_singleton] using h
    have ht := positionedCross_parity D Sc l r i i
    rw [← crossE_eq_cl] at ht
    have e : l ++ [i,i] ++ r = l ++ i :: i :: r := by simp
    rw [e] at ht ⊢
    rcases parity_eq_zero_or_one (D.parity i) with hp | hp
    · simp only [hp, mul_zero] at hx hy ht ⊢
      rw [sameIntertwiner, ite_eq_right (by simpa only [hp] using (zero_ne_one : (0 : ZMod 2) ≠ 1))]
      exact gEven_parity hx hy ht
    · simp only [hp, mul_one] at hx hy ht ⊢
      rw [sameIntertwiner, ite_eq_left hp]
      exact gOdd_parity hx hy ht
  · rw [intertwinerHom_of_ne D Sc l r hij]
    exact positionedCross_parity D Sc l r i j

omit [Fintype I] in
theorem moveHom_parity (i : I) (l ν : List I) :
    moveHom D Sc i l ν ∈ parity (R := k) _ _ (D.parity i * wordSumParity D ν) := by
  have he {A B : (pres D Sc).Presented} (h : A = B) :
      eqToHom h ∈ parity (R := k) A B 0 := by
    subst h
    exact Supercategory.id_mem _
  induction ν generalizing l with
  | nil => simpa only [moveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero] using he _
  | cons j ν ih =>
    simpa only [moveHom, wordSumParity, List.map_cons, List.sum_cons, mul_add,
      zero_add, add_zero] using Supercategory.comp_mem (he _)
        (Supercategory.comp_mem (intertwinerHom_parity D Sc l ν i j)
          (Supercategory.comp_mem (he _) (Supercategory.comp_mem (ih (l ++ [j])) (he _))))

end OddMath.QuiverHecke
end

end

section

/-!
# Moving-strand annihilation of old cyclotomic relations

`append_relation_move_tmul_zero` is the relation-killing input to the
repeated-colour QP induction. It allows arbitrary old factors on both
sides of the first-position relation, and arbitrary ambient left factors.
Naturality transports the entire old expression, including its parity
involution, before the old relation is killed in the prescribed balanced
coefficient target. No polynomial is commuted through bare crossings.

The coefficients here are ordinary polynomials over the even ground ring.
This does not assert the coefficient-superalgebra extension or the QP formula.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The bare crossing prefix taking the last strand to the first position.
Its execution order is rightmost crossing first, so algebraically it is
`τ₁ ⋯ τₙ` on a word of length `n + 1`. -/
def lastToFirstHom (i : I) : (ν : List I) →
    (pres D Sc).obj (ob D (ν ++ [i])) ⟶ (pres D Sc).obj (ob D (i :: ν))
  | [] => 𝟙 _
  | j :: ν =>
      ((pres D Sc).obj (ob D [j]) ◁ lastToFirstHom i ν) ≫
        cl D Sc (j :: i :: ν) (i :: j :: ν) [.cross 0]
          (by simpa using sChain_crossAt [] ν j i)

end OddMath.QuiverHecke
end

end
