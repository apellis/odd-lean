import OddMath.Frontier.EKFinalPrinted
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# EK §5.2: irreducibility of the printed minimal polynomials, and roots of unity

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, pp. 39–40.

* The eleven printed factors marked "(m-th root of unity)" are the cyclotomic polynomials
  `Φ_m` for `m = 3, 6, 5, 4, 22, 7, 8, 10, 12, 17, 28` (`cyclo_*`).  Hence each is irreducible
  over `ℚ` and its complex roots are exactly the primitive `m`-th roots of unity
  (`cyclotomic_facts`).
* `q`, `q - 1`, `q + 1` are irreducible.
* `f6 = q⁶ + 2q⁴ - q³ + 2q² + 1` and the printed degree-18 polynomial `f18` are irreducible
  over `ℚ` (`f6_irreducible`, `f18_irreducible`), certified by irreducibility modulo `2` and
  modulo `5` respectively (`irreducible_of_frob`: a monic polynomial of degree `n` over `𝔽_p`
  is irreducible if `X^{p^d} - X` is a unit modulo it for `1 ≤ d ≤ n/2`).
* The printed polynomials of degrees 50 and 102 are treated in `EKFinalIrred50` and
  `EKFinalIrred102` (irreducible modulo `269` and `89`).
* No complex root of `f6` or of `f18` is a root of unity (`f6_no_root_of_unity`,
  `f18_no_root_of_unity`): an irreducible factor with a root of unity as a root is a
  cyclotomic polynomial `Φ_m`, whose value at `1` is `0`, `1`, or a prime `ℓ` (when `m` is a
  power of `ℓ`); here the values at `1` are `5` and `112`, and `deg Φ_{5^k} = 4·5^{k-1} ≠ 6`.
-/

noncomputable section
open Polynomial

namespace OddMath.Frontier.EKFinal

/-! ## The cyclotomic factors -/

section Cyclotomic

theorem cyclo_prime (p : ℕ) [Fact p.Prime] :
    cyclotomic p ℤ = ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i := cyclotomic_prime ℤ p

theorem cyclo_3 : cyclotomic 3 ℤ = X ^ 2 + X + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [cyclo_prime]; simp [Finset.sum_range_succ]; ring

theorem cyclo_5 : cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [cyclo_prime]; simp [Finset.sum_range_succ]; ring

theorem cyclo_7 : cyclotomic 7 ℤ = X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [cyclo_prime]; simp [Finset.sum_range_succ]; ring

theorem cyclo_11 : cyclotomic 11 ℤ = ∑ i ∈ Finset.range 11, (X : ℤ[X]) ^ i := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact cyclo_prime 11

theorem cyclo_17 : cyclotomic 17 ℤ = phi17 := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  rw [cyclo_prime, phi17_eq]

theorem cyclo_4 : cyclotomic 4 ℤ = X ^ 2 + 1 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 1) Nat.prime_two
  norm_num at h
  rw [h]

theorem cyclo_8 : cyclotomic 8 ℤ = X ^ 4 + 1 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (n := 2) Nat.prime_two
  norm_num at h
  rw [h]

/-- `Φ_{2m}` from `Φ_m`, `m` odd: `Φ_m(X²) = Φ_{2m}(X) Φ_m(X)`. -/
theorem cyclo_double_odd {m : ℕ} (hm : ¬ 2 ∣ m) (P : ℤ[X])
    (h : expand ℤ 2 (cyclotomic m ℤ) = P * cyclotomic m ℤ) : cyclotomic (m * 2) ℤ = P := by
  have h2 := cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two hm ℤ
  rw [h2] at h
  exact mul_right_cancel₀ (cyclotomic_ne_zero m ℤ) h

theorem cyclo_6 : cyclotomic 6 ℤ = X ^ 2 - X + 1 := by
  apply cyclo_double_odd (m := 3) (by norm_num)
  rw [cyclo_3]; simp [expand_X]; ring

theorem cyclo_10 : cyclotomic 10 ℤ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  apply cyclo_double_odd (m := 5) (by norm_num)
  rw [cyclo_5]; simp [expand_X]; ring

theorem cyclo_14 : cyclotomic 14 ℤ = X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  apply cyclo_double_odd (m := 7) (by norm_num)
  rw [cyclo_7]; simp [expand_X]; ring

theorem cyclo_22 : cyclotomic 22 ℤ = phi22 := by
  apply cyclo_double_odd (m := 11) (by norm_num)
  rw [cyclo_11, phi22_eq]; simp [expand_X, Finset.sum_range_succ]; ring

theorem cyclo_12 : cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 := by
  have h := cyclotomic_expand_eq_cyclotomic (R := ℤ) Nat.prime_two (by norm_num : 2 ∣ 6)
  rw [cyclo_6] at h
  rw [show (12 : ℕ) = 6 * 2 from rfl, ← h]; simp [expand_X]; ring

theorem cyclo_28 : cyclotomic 28 ℤ = phi28 := by
  have h := cyclotomic_expand_eq_cyclotomic (R := ℤ) Nat.prime_two (by norm_num : 2 ∣ 14)
  rw [cyclo_14] at h
  rw [show (28 : ℕ) = 14 * 2 from rfl, ← h, phi28_eq]; simp [expand_X]; ring

/-- A cyclotomic factor is irreducible over `ℚ`, and its complex roots are exactly the
primitive `m`-th roots of unity. -/
theorem cyclotomic_facts {m : ℕ} (hm : 0 < m) {P : ℤ[X]} (h : cyclotomic m ℤ = P) :
    Irreducible (P.map (Int.castRingHom ℚ)) ∧
      ∀ z : ℂ, (P.map (Int.castRingHom ℂ)).IsRoot z ↔ IsPrimitiveRoot z m := by
  subst h
  refine ⟨?_, fun z => ?_⟩
  · rw [map_cyclotomic]; exact cyclotomic.irreducible_rat hm
  · rw [map_cyclotomic]; exact isRoot_cyclotomic_iff_charZero hm

end Cyclotomic

/-! ## An irreducibility criterion over `𝔽_p` -/

section Criterion

variable {p : ℕ} [hp : Fact p.Prime]

/-- A monic `f` of degree `n ≥ 1` over `𝔽_p` is irreducible as soon as `α^{p^d} - α` is a unit
in `𝔽_p[X]/(f)` for every `1 ≤ d ≤ n/2` (`α` the class of `X`): an irreducible factor `g` of
degree `d` would give a field `𝔽_p[X]/(g)` with `p^d` elements, in which `α^{p^d} = α`. -/
theorem irreducible_of_frob (f : (ZMod p)[X]) (hm : f.Monic) (hd : 0 < f.natDegree)
    (h : ∀ d, 0 < d → 2 * d ≤ f.natDegree →
      IsUnit ((AdjoinRoot.root f) ^ (p ^ d) - AdjoinRoot.root f)) : Irreducible f := by
  refine ⟨Polynomial.not_isUnit_of_natDegree_pos f hd, fun a b hab => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨hna, hnb⟩ := hne
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hab; exact hm.ne_zero hab
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hm.ne_zero hab
  have hdeg : f.natDegree = a.natDegree + b.natDegree := by rw [hab, natDegree_mul ha0 hb0]
  -- the smaller factor
  obtain ⟨c, hcf, hcu, hc0, hcd⟩ : ∃ c : (ZMod p)[X], c ∣ f ∧ ¬ IsUnit c ∧ c ≠ 0 ∧
      2 * c.natDegree ≤ f.natDegree := by
    by_cases hle : a.natDegree ≤ b.natDegree
    · exact ⟨a, ⟨b, hab⟩, hna, ha0, by omega⟩
    · exact ⟨b, ⟨a, by rw [hab, mul_comm]⟩, hnb, hb0, by omega⟩
  obtain ⟨g, hg, hgc⟩ := WfDvdMonoid.exists_irreducible_factor hcu hc0
  have hgf : g ∣ f := dvd_trans hgc hcf
  have hg0 : g ≠ 0 := hg.ne_zero
  have hgd : 0 < g.natDegree := hg.natDegree_pos
  have hgle : g.natDegree ≤ c.natDegree := natDegree_le_of_dvd hgc hc0
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hroot : aeval (AdjoinRoot.root g) f = 0 := by
    obtain ⟨t, ht⟩ := hgf
    rw [ht, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  let φ := AdjoinRoot.liftHom f (AdjoinRoot.root g) hroot
  have hu := (h g.natDegree hgd (by omega)).map φ
  rw [map_sub, map_pow, AdjoinRoot.liftHom_root] at hu
  let pb := AdjoinRoot.powerBasis hg0
  haveI : Module.Finite (ZMod p) (AdjoinRoot g) := pb.finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod p)
  letI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot g) = p ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, pb.finrank]
    rfl
  have hfix : (AdjoinRoot.root g) ^ (p ^ g.natDegree) = AdjoinRoot.root g := by
    rw [← hcard]; exact FiniteField.pow_card _
  rw [hfix, sub_self] at hu
  exact not_isUnit_zero hu

end Criterion

/-! ## Arithmetic modulo `p` and a monic polynomial, on coefficient lists -/

section ListPoly

variable {R : Type*} [CommRing R]

/-- `Σ cᵢ αⁱ` for a list of natural coefficients. -/
def evN (α : R) : List ℕ → R
  | [] => 0
  | c :: l => (c : R) + α * evN α l

/-- `Σ cᵢ αⁱ` for a list of integer coefficients. -/
def evZ (α : R) : List ℤ → R
  | [] => 0
  | c :: l => (c : R) + α * evZ α l

def addP (p : ℕ) : List ℕ → List ℕ → List ℕ
  | [], b => b
  | a :: l, [] => a :: l
  | x :: a, y :: b => ((x + y) % p) :: addP p a b

def scaleP (p c : ℕ) (a : List ℕ) : List ℕ := a.map fun x => (c * x) % p

/-- Multiplication by `α`, reducing `αⁿ` to `r` (`a` of length `n`). -/
def mulX (p : ℕ) (r : List ℕ) (a : List ℕ) : List ℕ :=
  addP p (0 :: a.dropLast) (scaleP p (a.getLastD 0) r)

/-- Product modulo the monic polynomial with `αⁿ = r`. -/
def mulmodP (p : ℕ) (r : List ℕ) (a b : List ℕ) : List ℕ :=
  a.foldr (fun c acc => addP p (scaleP p c b) (mulX p r acc)) (List.replicate r.length 0)

def powP (p : ℕ) (r : List ℕ) (a : List ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate (r.length - 1) 0
  | e + 1 => mulmodP p r a (powP p r a e)

/-- `s - α`. -/
def subXP (p n : ℕ) (s : List ℕ) : List ℕ := addP p s (0 :: (p - 1) :: List.replicate (n - 2) 0)

def oneP (n : ℕ) : List ℕ := 1 :: List.replicate (n - 1) 0

variable {p : ℕ}

theorem cast_mod_eq (hp : (p : R) = 0) (x : ℕ) : ((x % p : ℕ) : R) = x := by
  conv_rhs => rw [← Nat.mod_add_div x p]
  push_cast
  rw [hp, zero_mul, add_zero]

theorem evN_addP (α : R) (hp : (p : R) = 0) (a b : List ℕ) :
    evN α (addP p a b) = evN α a + evN α b := by
  induction a generalizing b with
  | nil => simp [addP, evN]
  | cons x a ih =>
    cases b with
    | nil => simp [addP, evN]
    | cons y b =>
      simp only [addP, evN, cast_mod_eq hp, ih]
      push_cast
      ring

theorem length_addP (a b : List ℕ) : (addP p a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [addP]
  | cons x a ih =>
    cases b with
    | nil => simp [addP]
    | cons y b => simp [addP, ih, Nat.succ_max_succ]

theorem evN_scaleP (α : R) (hp : (p : R) = 0) (c : ℕ) (a : List ℕ) :
    evN α (scaleP p c a) = c * evN α a := by
  induction a with
  | nil => simp [scaleP, evN]
  | cons x a ih =>
    simp only [scaleP, List.map_cons, evN] at ih ⊢
    rw [cast_mod_eq hp, ih]
    push_cast
    ring

theorem length_scaleP (c : ℕ) (a : List ℕ) : (scaleP p c a).length = a.length := by
  simp [scaleP]

theorem evN_append (α : R) (l : List ℕ) (c : ℕ) :
    evN α (l ++ [c]) = evN α l + c * α ^ l.length := by
  induction l with
  | nil => simp [evN]
  | cons x l ih => simp only [List.cons_append, evN, ih, List.length_cons, pow_succ]; ring

theorem evN_replicate_zero (α : R) (m : ℕ) : evN α (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, evN, ih]

theorem evN_mulX (α : R) (hp : (p : R) = 0) {n : ℕ} (r : List ℕ) (hr : evN α r = α ^ n)
    (a : List ℕ) (ha : a.length = n) (hn : 0 < n) : evN α (mulX p r a) = α * evN α a := by
  have hne : a ≠ [] := by rintro rfl; simp at ha; omega
  have hsplit := List.dropLast_append_getLast hne
  have hlast : a.getLastD 0 = a.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne]; rfl
  rw [mulX, evN_addP α hp, evN_scaleP α hp, hr, hlast]
  conv_rhs => rw [← hsplit, evN_append]
  have hl : a.dropLast.length = n - 1 := by rw [List.length_dropLast, ha]
  rw [hl]
  simp only [evN, Nat.cast_zero, zero_add]
  have : α * α ^ (n - 1) = α ^ n := by rw [← pow_succ']; congr 1; omega
  rw [mul_add, ← mul_assoc, mul_comm α (↑(a.getLast hne) : R), mul_assoc, this]

theorem length_mulX {n : ℕ} (r : List ℕ) (hr : r.length = n) (a : List ℕ) (ha : a.length = n)
    (hn : 0 < n) : (mulX p r a).length = n := by
  rw [mulX, length_addP, length_scaleP, hr]
  simp [ha]
  omega

theorem mulmodP_spec (α : R) (hp : (p : R) = 0) {n : ℕ} (r : List ℕ) (hr : evN α r = α ^ n)
    (hrl : r.length = n) (hn : 0 < n) (b : List ℕ) (hb : b.length = n) (a : List ℕ) :
    evN α (mulmodP p r a b) = evN α a * evN α b ∧ (mulmodP p r a b).length = n := by
  induction a with
  | nil => simp [mulmodP, evN_replicate_zero, evN, hrl]
  | cons c a ih =>
    have e : mulmodP p r (c :: a) b =
        addP p (scaleP p c b) (mulX p r (mulmodP p r a b)) := rfl
    rw [e, evN_addP α hp, evN_scaleP α hp, evN_mulX α hp r hr _ ih.2 hn, ih.1, length_addP,
      length_scaleP, length_mulX r hrl _ ih.2 hn, hb]
    simp only [evN, max_self, and_true]
    ring

theorem powP_spec (α : R) (hp : (p : R) = 0) {n : ℕ} (r : List ℕ) (hr : evN α r = α ^ n)
    (hrl : r.length = n) (hn : 0 < n) (a : List ℕ) (e : ℕ) :
    evN α (powP p r a e) = evN α a ^ e ∧ (powP p r a e).length = n := by
  induction e with
  | zero => simp [powP, evN, evN_replicate_zero, hrl]; omega
  | succ e ih =>
    obtain ⟨h1, h2⟩ := mulmodP_spec α hp r hr hrl hn _ ih.2 a
    refine ⟨?_, h2⟩
    rw [powP, h1, ih.1, pow_succ']

theorem evN_subXP (α : R) (hp : (p : R) = 0) (hp1 : 1 ≤ p) (n : ℕ) (s : List ℕ) :
    evN α (subXP p n s) = evN α s - α := by
  rw [subXP, evN_addP α hp]
  simp only [evN, evN_replicate_zero, Nat.cast_zero, zero_add, mul_zero, add_zero]
  rw [Nat.cast_sub hp1, hp]
  ring

theorem evN_oneP (α : R) (n : ℕ) : evN α (oneP n) = 1 := by
  simp [oneP, evN, evN_replicate_zero]

/-- The certificate check: for each `w` in turn, `s ← s^p` and `(s - α) w = 1`. -/
def chkP (p : ℕ) (r : List ℕ) (n : ℕ) : List (List ℕ) → List ℕ → Bool
  | [], _ => true
  | w :: ws, s =>
    (w.length == n && mulmodP p r (subXP p n (powP p r s p)) w == oneP n) &&
      chkP p r n ws (powP p r s p)

theorem chkP_spec (α : R) (hp : (p : R) = 0) (hp1 : 1 ≤ p) {n : ℕ} (r : List ℕ)
    (hr : evN α r = α ^ n) (hrl : r.length = n) (hn : 0 < n) (ws : List (List ℕ)) :
    ∀ (s : List ℕ) (j : ℕ), evN α s = α ^ (p ^ j) → s.length = n → chkP p r n ws s = true →
      ∀ i < ws.length, IsUnit (α ^ (p ^ (j + i + 1)) - α) := by
  induction ws with
  | nil => intro s j _ _ _ i hi; simp at hi
  | cons w ws ih =>
    intro s j hs hsl h i hi
    simp only [chkP, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hwl, hw⟩, hrest⟩ := h
    obtain ⟨hps, hpl⟩ := powP_spec α hp r hr hrl hn s p
    have hs' : evN α (powP p r s p) = α ^ (p ^ (j + 1)) := by
      rw [hps, hs, ← pow_mul, pow_succ]
    cases i with
    | zero =>
      have := (mulmodP_spec α hp r hr hrl hn w hwl (subXP p n (powP p r s p))).1
      rw [hw, evN_oneP, evN_subXP α hp hp1, hs'] at this
      exact isUnit_of_mul_eq_one _ _ this.symm
    | succ i =>
      have := ih (powP p r s p) (j + 1) hs' hpl hrest i (by simpa using hi)
      rwa [show j + 1 + i + 1 = j + (i + 1) + 1 by ring] at this

theorem evZ_eq_aeval {S : Type*} [CommRing S] [Algebra S R] (α : R) (l : List ℤ) :
    aeval α ((ofList l).map (Int.castRingHom S)) = evZ α l := by
  induction l with
  | nil => simp [ofList, evZ]
  | cons c l ih =>
    simp only [ofList, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      map_add, map_mul, aeval_C, aeval_X, ih, evZ]
    simp

theorem evZ_append (α : R) (l : List ℤ) (c : ℤ) :
    evZ α (l ++ [c]) = evZ α l + c * α ^ l.length := by
  induction l with
  | nil => simp [evZ]
  | cons x l ih => simp only [List.cons_append, evZ, ih, List.length_cons, pow_succ]; ring

/-- `-c mod p` as a natural number. -/
def negMod (p : ℕ) (c : ℤ) : ℕ := (p - (c % p).toNat) % p

theorem cast_negMod (hp : (p : R) = 0) (hp0 : 0 < p) (c : ℤ) : ((negMod p c : ℕ) : R) = -(c : R) := by
  rw [negMod, cast_mod_eq hp]
  have h0 : 0 ≤ c % p := Int.emod_nonneg _ (by exact_mod_cast hp0.ne')
  have h1 : c % p < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp0)
  have hle : (c % p).toNat ≤ p := by omega
  rw [Nat.cast_sub hle, hp, zero_sub]
  congr 1
  have : (((c % p).toNat : ℕ) : ℤ) = c % p := Int.toNat_of_nonneg h0
  have e : ((c % p : ℤ) : R) = (c : R) := by
    rw [Int.emod_def]; push_cast
    rw [hp, zero_mul, sub_zero]
  rw [← e, ← this]
  push_cast
  rfl

theorem evN_negMod (α : R) (hp : (p : R) = 0) (hp0 : 0 < p) (l : List ℤ) :
    evN α (l.map (negMod p)) = -evZ α l := by
  induction l with
  | nil => simp [evN, evZ]
  | cons c l ih => simp only [List.map_cons, evN, evZ, ih, cast_negMod hp hp0]; ring

end ListPoly

/-! ## Irreducibility of integer polynomials via a prime -/

section IrrMod

theorem natDegree_ofList_one (lower : List ℤ) : (ofList (lower ++ [1])).natDegree = lower.length := by
  have hcoeff : ∀ e, (ofList (lower ++ [1])).coeff e = (lower ++ [1]).getD e 0 := coeff_ofList _
  have hget : (lower ++ [1]).getD lower.length 0 = 1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro e he
    rw [hcoeff, List.getD_eq_default]
    simp; exact_mod_cast he
  · rw [hcoeff, hget]; exact one_ne_zero

theorem monic_ofList_one (lower : List ℤ) : (ofList (lower ++ [1])).Monic := by
  rw [Monic, leadingCoeff, natDegree_ofList_one, coeff_ofList, List.getD_eq_getElem?_getD,
    List.getElem?_append_right le_rfl]
  simp

/-- A monic integer polynomial `lower ++ [1]` is irreducible over `ℚ` if the certificate
check `chkP` succeeds modulo a prime `p`. -/
theorem irreducible_of_chk (p : ℕ) [Fact p.Prime] (lower : List ℤ)
    (ws : List (List ℕ)) (hws : lower.length ≤ 2 * ws.length)
    (h : chkP p (lower.map (negMod p)) lower.length ws
      (0 :: 1 :: List.replicate (lower.length - 2) 0) = true)
    (hn2 : 2 ≤ lower.length) :
    Irreducible ((ofList (lower ++ [1])).map (Int.castRingHom ℚ)) := by
  set n := lower.length with hndef
  set f := ofList (lower ++ [1]) with hfdef
  have hdeg : f.natDegree = n := natDegree_ofList_one lower
  have hmonic : f.Monic := monic_ofList_one lower
  have hZ : Irreducible f := by
    apply hmonic.irreducible_of_irreducible_map (Int.castRingHom (ZMod p))
    set fb := f.map (Int.castRingHom (ZMod p))
    have hmb : fb.Monic := hmonic.map _
    have hdb : fb.natDegree = n := by rw [hmonic.natDegree_map, hdeg]
    apply irreducible_of_frob fb hmb (by omega)
    intro d hd0 hd
    set α := AdjoinRoot.root fb
    have hp : ((p : ℕ) : AdjoinRoot fb) = 0 := by
      rw [← map_natCast (algebraMap (ZMod p) (AdjoinRoot fb)), ZMod.natCast_self, map_zero]
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hroot : evZ α (lower ++ [1]) = 0 := by
      rw [← evZ_eq_aeval (S := ZMod p), AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hr : evN α (lower.map (negMod p)) = α ^ n := by
      rw [evN_negMod α hp hp0, hndef]
      rw [evZ_append] at hroot
      simp only [Int.cast_one, one_mul] at hroot
      linear_combination -hroot
    have hs0 : evN α (0 :: 1 :: List.replicate (n - 2) 0) = α ^ (p ^ 0) := by
      simp [evN, evN_replicate_zero]
    have := chkP_spec α hp hp0 (lower.map (negMod p)) hr (by simp [hndef]) (by omega) ws _ 0 hs0
      (by simp only [List.length_cons, List.length_replicate]; omega) h (d - 1) (by omega)
    rwa [show 0 + (d - 1) + 1 = d by omega] at this
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp hZ

end IrrMod

/-! ## `f6` and `f18` -/

/-- Inverses of `X^{2^d} - X` modulo `f6` over `𝔽₂`, `d = 1, 2, 3`. -/
def cert6 : List (List ℕ) := [[0, 0, 1, 1, 1, 0], [0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 1, 0]]

/-- Inverses of `X^{5^d} - X` modulo `f18` over `𝔽₅`, `d = 1, …, 9`. -/
def cert18 : List (List ℕ) :=
  [[1, 1, 4, 4, 3, 1, 0, 0, 3, 1, 2, 3, 2, 3, 3, 4, 1, 3],
   [1, 0, 0, 3, 4, 1, 3, 0, 3, 3, 4, 0, 2, 2, 2, 0, 4, 2],
   [0, 3, 1, 3, 3, 1, 0, 4, 4, 0, 2, 2, 1, 1, 4, 0, 0, 0],
   [0, 3, 0, 1, 0, 1, 1, 0, 3, 2, 1, 4, 2, 2, 2, 2, 0, 0],
   [1, 1, 1, 0, 2, 3, 4, 3, 2, 2, 3, 2, 4, 1, 2, 0, 0, 3],
   [4, 3, 4, 0, 0, 2, 3, 0, 2, 3, 0, 1, 4, 0, 3, 1, 0, 1],
   [3, 3, 3, 0, 2, 4, 1, 3, 3, 0, 1, 2, 1, 2, 2, 4, 1, 4],
   [0, 3, 3, 3, 1, 3, 3, 0, 2, 3, 3, 1, 0, 1, 1, 2, 2, 1],
   [3, 3, 1, 2, 0, 2, 2, 4, 0, 3, 3, 2, 2, 0, 3, 1, 3, 1]]

def f6Lower : List ℤ := [1, 0, 2, -1, 2, 0]
def f18Lower : List ℤ := [1, 1, 3, 4, 6, 7, 8, 10, 11, 10, 11, 10, 8, 7, 6, 4, 3, 1]

theorem f6_split : f6 = ofList (f6Lower ++ [1]) := rfl
theorem f18_split : f18 = ofList (f18Lower ++ [1]) := by
  rw [f18, f18L]; rfl

/-- **`f6 = q⁶ + 2q⁴ - q³ + 2q² + 1` is irreducible over `ℚ`** (it is irreducible mod `2`). -/
theorem f6_irreducible : Irreducible (f6.map (Int.castRingHom ℚ)) := by
  rw [f6_split]
  exact irreducible_of_chk 2 f6Lower cert6 (by decide) (by decide +kernel) (by decide)

/-- **The printed degree-18 polynomial is irreducible over `ℚ`** (it is irreducible mod `5`). -/
theorem f18_irreducible : Irreducible (f18.map (Int.castRingHom ℚ)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [f18_split]
  exact irreducible_of_chk 5 f18Lower cert18 (by decide) (by decide +kernel) (by decide)

/-! ## Roots of unity -/

/-- The value at `1` of a cyclotomic polynomial over `ℚ`: `0` for `Φ₁`, a prime `ℓ` for
`Φ_{ℓ^{k+1}}`, and `1` otherwise. -/
theorem cyclotomic_eval_one_cases (N : ℕ) (hN : 0 < N) :
    (N = 1 ∧ eval 1 (cyclotomic N ℚ) = 0) ∨
    (∃ ℓ k : ℕ, ℓ.Prime ∧ N = ℓ ^ (k + 1) ∧ eval 1 (cyclotomic N ℚ) = ℓ) ∨
    eval 1 (cyclotomic N ℚ) = 1 := by
  by_cases hpp : ∃ ℓ k : ℕ, ℓ.Prime ∧ ℓ ^ k = N
  · obtain ⟨ℓ, k, hℓ, hk⟩ := hpp
    cases k with
    | zero =>
      left
      simp at hk
      subst hk
      simp [cyclotomic_one]
    | succ k =>
      right; left
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      refine ⟨ℓ, k, hℓ, hk.symm, ?_⟩
      rw [← hk, eval_one_cyclotomic_prime_pow]
  · right; right
    apply eval_one_cyclotomic_not_prime_pow
    intro ℓ hℓ k hk
    exact hpp ⟨ℓ, k, hℓ, hk⟩

/-- If an irreducible monic integer polynomial has a root of unity as a complex root, it is a
cyclotomic polynomial over `ℚ`. -/
theorem eq_cyclotomic_of_root_of_unity (P : ℤ[X]) (hm : P.Monic)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ))) (z : ℂ)
    (hz : (P.map (Int.castRingHom ℂ)).IsRoot z) (m : ℕ) (hm0 : 0 < m) (hzm : z ^ m = 1) :
    ∃ N, 0 < N ∧ P.map (Int.castRingHom ℚ) = cyclotomic N ℚ := by
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm0, hzm⟩
  refine ⟨orderOf z, hfin.orderOf_pos, ?_⟩
  rw [cyclotomic_eq_minpoly_rat (IsPrimitiveRoot.orderOf z) hfin.orderOf_pos]
  apply minpoly.eq_of_irreducible_of_monic hirr _ (hm.map _)
  rw [aeval_def, eval₂_map]
  have : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [this, ← eval_map]
  exact hz

theorem eval_one_map_ofList (L : List ℤ) :
    eval 1 ((ofList L).map (Int.castRingHom ℚ)) = (hornerL 1 L : ℚ) := by
  rw [eval_one_map, eval_ofList]
  rfl

/-- **No complex root of `f6` is a root of unity** (EK p. 39: "not a root of unity"). -/
theorem f6_no_root_of_unity (z : ℂ) (hz : (f6.map (Int.castRingHom ℂ)).IsRoot z) :
    ¬ ∃ m, 0 < m ∧ z ^ m = 1 := by
  rintro ⟨m, hm0, hzm⟩
  obtain ⟨N, hN, hE⟩ := eq_cyclotomic_of_root_of_unity f6 (by rw [f6_split]; exact monic_ofList_one _)
    f6_irreducible z hz m hm0 hzm
  have hv : eval 1 (f6.map (Int.castRingHom ℚ)) = 5 := by
    rw [f6, eval_one_map_ofList]; norm_num [hornerL, f6L]
  have hdeg : (f6.map (Int.castRingHom ℚ)).natDegree = 6 := by
    rw [(show f6.Monic by rw [f6_split]; exact monic_ofList_one _).natDegree_map, f6_split,
      natDegree_ofList_one]; rfl
  rw [hE] at hv hdeg
  rcases cyclotomic_eval_one_cases N hN with ⟨-, h⟩ | ⟨ℓ, k, hℓ, rfl, h⟩ | h
  · rw [h] at hv; norm_num at hv
  · rw [h] at hv
    have hℓ5 : ℓ = 5 := by exact_mod_cast hv
    subst hℓ5
    rw [natDegree_cyclotomic, Nat.totient_prime_pow_succ hℓ] at hdeg
    omega
  · rw [h] at hv; norm_num at hv

/-- **No complex root of `f18` is a root of unity** (EK p. 40: "not a root of unity"). -/
theorem f18_no_root_of_unity (z : ℂ) (hz : (f18.map (Int.castRingHom ℂ)).IsRoot z) :
    ¬ ∃ m, 0 < m ∧ z ^ m = 1 := by
  rintro ⟨m, hm0, hzm⟩
  obtain ⟨N, hN, hE⟩ := eq_cyclotomic_of_root_of_unity f18
    (by rw [f18_split]; exact monic_ofList_one _) f18_irreducible z hz m hm0 hzm
  have hv : eval 1 (f18.map (Int.castRingHom ℚ)) = 112 := by
    rw [f18, eval_one_map_ofList]; norm_num [hornerL, f18L, palin]
  rw [hE] at hv
  rcases cyclotomic_eval_one_cases N hN with ⟨-, h⟩ | ⟨ℓ, k, hℓ, rfl, h⟩ | h
  · rw [h] at hv; norm_num at hv
  · rw [h] at hv
    have hℓ112 : ℓ = 112 := by exact_mod_cast hv
    subst hℓ112
    norm_num at hℓ
  · rw [h] at hv; norm_num at hv

/-! ## Summary of the printed list -/

/-- **EK §5.2, pp. 39–40: the printed minimal polynomials.**
The factors marked "(m-th root of unity)" are the cyclotomic polynomials `Φ_m`; each is
irreducible over `ℚ` with roots exactly the primitive `m`-th roots of unity. -/
theorem printed_cyclotomic :
    cyclotomic 3 ℤ = X ^ 2 + X + 1 ∧ cyclotomic 6 ℤ = X ^ 2 - X + 1 ∧
    cyclotomic 4 ℤ = X ^ 2 + 1 ∧ cyclotomic 22 ℤ = phi22 ∧
    cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 ∧
    cyclotomic 7 ℤ = X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 ∧
    cyclotomic 8 ℤ = X ^ 4 + 1 ∧ cyclotomic 10 ℤ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 ∧
    cyclotomic 12 ℤ = X ^ 4 - X ^ 2 + 1 ∧ cyclotomic 17 ℤ = phi17 ∧ cyclotomic 28 ℤ = phi28 :=
  ⟨cyclo_3, cyclo_6, cyclo_4, cyclo_22, cyclo_5, cyclo_7, cyclo_8, cyclo_10, cyclo_12, cyclo_17,
    cyclo_28⟩

/-- The linear printed factors are irreducible over `ℚ`. -/
theorem linear_irreducible :
    Irreducible ((X : ℤ[X]).map (Int.castRingHom ℚ)) ∧
    Irreducible ((X - 1 : ℤ[X]).map (Int.castRingHom ℚ)) ∧
    Irreducible ((X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.map_X]; exact irreducible_X
  · rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, ← C_1]
    exact irreducible_X_sub_C 1
  · rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
      show (X + 1 : ℚ[X]) = X - C (-1) by simp]
    exact irreducible_X_sub_C (-1)

end OddMath.Frontier.EKFinal
