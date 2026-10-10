/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Bubbles
import OddMath.SKM.Lemma31Rot

/-!
# Infinite Grassmannian relations, part 1 (Brundan–Ellis, Proposition 5.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 5.1
(TeX label `IG`): (5.3)–(5.4) and the identities (5.8) from its proof, hence (5.5) for even `i`.

* `closedPar μ p`: the span of the closed normal-form diagrams on `1_μ` of parity `p`; two such
  2-morphisms supercommute (`comm_of_mem`; the super interchange law (1.3) for endomorphisms of
  `1_λ`). All dotted bubbles are homogeneous (`bubL_mem`, `bubR_mem`).
* (5.3): `bubLs_neg`, `bubLs_zero`; (5.4): `bubRs_neg`, `bubRs_zero`.
* (5.8), first identity (`⟨hᵢ, λ⟩ ≥ 0`): `ig_hpos`; second identity (`⟨hᵢ, λ⟩ ≤ 0`): `ig_hneg`.
  The paper deduces the second from the first by the Chevalley involution (Proposition 3.5); here
  it is proved by the mirrored computation (using (2.12), (2.14) and (3.3)). Both are stated with
  the bubble on the left composed first; the paper's second identity has the opposite vertical
  order, which differs by the super interchange law (`ig_hneg'`).
* (5.5) (`i` even): `eq_5_5`.

Sums over `r + s = t - 2` with `r, s ∈ ℤ` are finite: the terms outside the ranges used vanish by
(5.3)–(5.4) (`bubL_eq_zero_of_lt`, `bubR_eq_zero_of_lt`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## Integer-indexed sums -/

theorem sum_Icc_split {M : Type*} [AddCommMonoid M] (f : ℤ → M) (N T : ℕ) :
    ∑ s ∈ Icc (-(N:ℤ)-1) T, f s =
      ∑ n ∈ range (N+1), f (-(n:ℤ)-1) + ∑ m ∈ range (T+1), f m := by
  have h1 : Icc (-(N:ℤ)-1) T = (range (N+1)).image (fun n : ℕ => -(n:ℤ)-1) ∪
      (range (T+1)).image (fun n : ℕ => (n:ℤ)) := by
    ext s; simp only [mem_Icc, mem_union, mem_image, mem_range]
    constructor
    · intro ⟨h1, h2⟩
      rcases lt_or_ge s 0 with h | h
      · left; exact ⟨(-s-1).toNat, by omega, by omega⟩
      · right; exact ⟨s.toNat, by omega, by omega⟩
    · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) <;> omega
  rw [h1, sum_union, sum_image, sum_image]
  · intro a _ b _ h; simpa using h
  · intro a _ b _ h; simpa using h
  · rw [disjoint_left]; simp only [mem_image, mem_range]
    rintro _ ⟨a, _, rfl⟩ ⟨b, _, hb⟩; omega

theorem natCast_toNat_zmod (z : ℤ) (hz : 0 ≤ z) : ((z.toNat : ℕ) : ZMod 2) = (z : ZMod 2) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]

/-! ## Supercommutation of closed diagrams -/

variable (D Sc) in
/-- The span of the closed normal-form diagrams on `1_μ` whose generators have parities summing
to `p`. -/
def closedPar (μ : X) (p : ZMod 2) :
    Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])) :=
  Submodule.span k {f | ∃ L, SChain [] L [] ∧ parsum D L = p ∧ f = cl D Sc μ [] [] L}

theorem cl_mem_closedPar {μ : X} {L : List (LayerData I)} (hL : SChain [] L []) {p : ZMod 2}
    (hp : parsum D L = p) : cl D Sc μ [] [] L ∈ closedPar D Sc μ p :=
  Submodule.subset_span ⟨L, hL, hp, rfl⟩

theorem cl_comm_closed {μ : X} {L M : List (LayerData I)} (hL : SChain [] L [])
    (hM : SChain [] M []) :
    cl D Sc μ [] [] L ≫ cl D Sc μ [] [] M =
      zsign k (parsum D L * parsum D M) • (cl D Sc μ [] [] M ≫ cl D Sc μ [] [] L) := by
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := []) (T := []) [] [] hL hM
  have hw : ∀ L : List (LayerData I), L.map (whL [] []) = L := fun L => by
    induction L with
    | nil => rfl
    | cons x L ih => rw [List.map_cons, ih, whL_nil_nil]
  simp only [List.nil_append, List.append_nil, hw] at E
  rw [cl_comp hL hM, cl_comp hM hL, E]

/-- **Super interchange for endomorphisms of `1_λ`**: homogeneous closed 2-morphisms
supercommute. -/
theorem comm_of_mem {μ : X} {p q : ZMod 2} {f g : (pres D Sc).obj (ob D μ []) ⟶
    (pres D Sc).obj (ob D μ [])} (hf : f ∈ closedPar D Sc μ p) (hg : g ∈ closedPar D Sc μ q) :
    f ≫ g = zsign k (p * q) • (g ≫ f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨M, hM, rfl, rfl⟩ := hg
      exact cl_comm_closed hL hM
    | zero => simp
    | add x y _ _ hx hy => rw [Preadditive.comp_add, Preadditive.add_comp, hx, hy, smul_add]
    | smul a x _ hx => rw [Linear.comp_smul, Linear.smul_comp, hx, smul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [Preadditive.comp_add, Preadditive.add_comp, hx, hy, smul_add]
  | smul a x _ hx => rw [Linear.comp_smul, Linear.smul_comp, hx, smul_comm]

/-! ## Normal forms of the leftward cup and cap and of the bubbles -/

variable (cs : CScalars Sc)

theorem etaP_eq_of_nonpos {i : I} {μ : X} (hh : D.h i μ ≤ 0) :
    etaP cs i μ = (zsign k (ipar D i μ) * (cs.c μ i : k)) •
      cl D Sc μ [] [up i, dn i] (etaL i (-D.h i μ).toNat ++ lcrossL i i) :=
  ite_eq_right (show ¬ 0 < D.h i μ by omega)

theorem epsP_eq_of_nonneg {i : I} {μ : X} (hh : 0 ≤ D.h i μ) :
    epsP cs i μ = (-(zsign k (D.parity i * (D.h i μ : ZMod 2))) * (↑(cs.c μ i)⁻¹ : k)) •
      cl D Sc μ [dn i, up i] [] (lcrossL i i ++ epsL i (D.h i μ).toNat) :=
  by rw [epsP, ite_eq_right (show ¬ D.h i μ < 0 by omega), neg_mul]

theorem bubL_nat (i : I) (μ : X) (n : ℕ) :
    bubL cs i μ n = etaP cs i μ ≫ cl D Sc μ [up i, dn i] [] (epsL i n) := by
  rw [bubL, ite_eq_left (show (0:ℤ) ≤ (n:ℤ) by omega), Int.toNat_natCast]

theorem bubR_nat (i : I) (μ : X) (n : ℕ) :
    bubR cs i μ n = cl D Sc μ [] [dn i, up i] (etaL i n) ≫ epsP cs i μ := by
  rw [bubR, ite_eq_left (show (0:ℤ) ≤ (n:ℤ) by omega), Int.toNat_natCast]

theorem bubL_eq_zero_of_lt (i : I) (μ : X) {n : ℤ} (hn : n < D.h i μ - 1) :
    bubL cs i μ n = 0 := by
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [bubL_nat, eq_2_13_c cs i μ m (by omega), ite_eq_right (by omega)]
  · rw [bubL]; split_ifs <;> first | rfl | omega

theorem bubR_eq_zero_of_lt (i : I) (μ : X) {n : ℤ} (hn : n < -D.h i μ - 1) :
    bubR cs i μ n = 0 := by
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [bubR_nat, eq_2_14_c cs i μ m (by omega), ite_eq_right (by omega)]
  · rw [bubR]; split_ifs <;> first | rfl | omega

theorem bubL_eq_c (i : I) (μ : X) : bubL cs i μ (D.h i μ - 1) = (cs.c μ i : k) • 𝟙 _ := by
  rcases le_or_gt 0 (D.h i μ - 1) with h0 | h0
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hm, bubL_nat, eq_2_13_c cs i μ m (by omega), ite_eq_left (by omega)]
  · rw [bubL]; split_ifs <;> first | rfl | omega

theorem bubR_eq_c (i : I) (μ : X) : bubR cs i μ (-D.h i μ - 1) = (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
  rcases le_or_gt 0 (-D.h i μ - 1) with h0 | h0
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hm, bubR_nat, eq_2_14_c cs i μ m (by omega), ite_eq_left (by omega)]
  · rw [bubR]; split_ifs <;> first | rfl | omega

/-- **Brundan–Ellis, (5.3)**, first relation: `n + *` dots on the counterclockwise bubble give
`0` for `n < 0`. -/
theorem bubLs_neg (i : I) (μ : X) {n : ℤ} (hn : n < 0) : bubLs cs i μ n = 0 :=
  bubL_eq_zero_of_lt cs i μ (by omega)

/-- **Brundan–Ellis, (5.3)**, second relation: `0 + *` dots give `c_{λ;i} 1_{1_λ}`. -/
theorem bubLs_zero (i : I) (μ : X) : bubLs cs i μ 0 = (cs.c μ i : k) • 𝟙 _ := by
  rw [bubLs, zero_add, bubL_eq_c]

/-- **Brundan–Ellis, (5.4)**, first relation. -/
theorem bubRs_neg (i : I) (μ : X) {n : ℤ} (hn : n < 0) : bubRs cs i μ n = 0 :=
  bubR_eq_zero_of_lt cs i μ (by omega)

/-- **Brundan–Ellis, (5.4)**, second relation: `0 + *` dots give `c_{λ;i}⁻¹ 1_{1_λ}`. -/
theorem bubRs_zero (i : I) (μ : X) : bubRs cs i μ 0 = (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
  rw [bubRs, zero_sub, bubR_eq_c]


/-! ## Signs `(-1)^{a n}` for integers `n` -/

variable (k) in
/-- `(-1)^{a n}` for `a ∈ ℤ/2` and `n ∈ ℤ`. -/
def isg (a : ZMod 2) (n : ℤ) : k := zsign k (a * (n : ZMod 2))

theorem isg_add (a : ZMod 2) (m n : ℤ) : isg k a (m + n) = isg k a m * isg k a n := by
  simp only [isg, Int.cast_add, mul_add, zsign_add]

theorem isg_congr (a : ZMod 2) {m n : ℤ} (h : (2 : ℤ) ∣ m - n) : isg k a m = isg k a n := by
  have : ((m : ℤ) : ZMod 2) = (n : ZMod 2) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub m n 2).mpr (by rw [← dvd_neg, neg_sub] at h; simpa using h)
  simp only [isg, this]

theorem isg_mul_self (a : ZMod 2) (n : ℤ) : isg k a n * isg k a n = 1 := by
  rw [← isg_add, isg_congr a (n := 0) ⟨n, by ring⟩]
  simp [isg, zsign_zero]

theorem isg_zero (a : ZMod 2) : isg k a 0 = 1 := by simp [isg, zsign_zero]

theorem isg_one (a : ZMod 2) : isg k a 1 = zsign k a := by simp [isg]

theorem isg_natCast (a : ZMod 2) (n : ℕ) : zsign k (a * (n : ZMod 2)) = isg k a n := by
  simp [isg]

/-! ## (5.8) for `⟨hᵢ, λ⟩ ≥ 0` -/

theorem bubR_neg_of_lt (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    bubR cs i μ (-(n : ℤ) - 1) = (-(isg k (D.parity i) (D.h i μ - n)) * (↑(cs.c μ i)⁻¹ : k)) •
      cl D Sc μ [] [] (dcupL i n ++ epsL i (D.h i μ).toNat) := by
  rw [bubR, ite_eq_right (show ¬ (0 : ℤ) ≤ -(n : ℤ) - 1 by omega),
    ite_eq_left (show -D.h i μ - 1 < -(n : ℤ) - 1 by omega),
    show (-(-(n : ℤ) - 1) - 1).toNat = n by omega, isg]
  congr 4
  push_cast; ring

theorem epsL_add (i : I) (m n : ℕ) : epsL i (m + n) = dotsL [] i [dn i] m ++ epsL i n := by
  simp only [epsL, dotsL, List.replicate_add, List.append_assoc]

theorem etaL_add (i : I) (m n : ℕ) : etaL i (m + n) = etaL i m ++ dotsL [dn i] i [] n := by
  simp only [etaL, dotsL, List.replicate_add, List.append_assoc]

/-- The first sum in the proof of (5.8) (`⟨hᵢ, λ⟩ ≥ 0`), the terms with `s < 0`. -/
theorem ig_hpos_neg (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (T : ℕ) :
    ∑ n ∈ range ((D.h i μ).toNat + 1), isg k (D.parity i) (-(n:ℤ) - 1) •
        (bubL cs i μ ((T:ℤ) + n) ≫ bubR cs i μ (-(n:ℤ) - 1)) =
      zsign k (D.parity i) • (etaP cs i μ ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (dotsL [] i [dn i] T ++ sigmaL i i) ≫ epsP cs i μ) := by
  set N := (D.h i μ).toNat with hN
  have hNh : (N : ℤ) = D.h i μ := Int.toNat_of_nonneg hh
  have hdT : SChain [up i, dn i] (dotsL [] i [dn i] T) [up i, dn i] := sChain_dotsL [] i [dn i] T
  -- the terms `n < N`
  have hterm : ∀ n ∈ range N, isg k (D.parity i) (-(n:ℤ) - 1) •
      (bubL cs i μ ((T:ℤ) + n) ≫ bubR cs i μ (-(n:ℤ) - 1)) =
      (-(isg k (D.parity i) (N + 1)) * (↑(cs.c μ i)⁻¹ : k)) •
        (etaP cs i μ ≫ cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] T) ≫
          cl D Sc μ [up i, dn i] [up i, dn i] (epsL i n ++ dcupL i n) ≫
            cl D Sc μ [up i, dn i] [] (epsL i N)) := by
    intro n hn
    rw [mem_range] at hn
    rw [show ((T:ℤ) + n) = ((T + n : ℕ) : ℤ) by push_cast; ring, bubL_nat,
      bubR_neg_of_lt cs i μ n (by omega), Linear.comp_smul, smul_smul, epsL_add,
      ← cl_comp hdT (sChain_epsL i n), ← cl_comp (sChain_dcupL i n) (sChain_epsL i _),
      ← cl_comp (sChain_epsL i n) (sChain_dcupL i n)]
    simp only [Category.assoc, ← hN]
    congr 1
    rw [← hNh]
    rw [show isg k (D.parity i) (-(n:ℤ) - 1) * (-isg k (D.parity i) ((N:ℤ) - n) * (↑(cs.c μ i)⁻¹ : k))
        = -(isg k (D.parity i) (-(n:ℤ) - 1) * isg k (D.parity i) ((N:ℤ) - n)) * (↑(cs.c μ i)⁻¹ : k)
        by ring, ← isg_add, isg_congr _ (n := (N:ℤ) + 1) ⟨-n - 1, by ring⟩]
  rw [sum_range_succ, sum_congr rfl hterm, ← smul_sum]
  simp only [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  have h12 : ∑ n ∈ range N, cl D Sc μ [up i, dn i] [up i, dn i] (epsL i n ++ dcupL i n) =
      cl D Sc μ [up i, dn i] [up i, dn i] (sigmaL i i ++ lcrossL i i) +
        cl D Sc μ [up i, dn i] [up i, dn i] [] := by
    rw [eq_2_12_a Sc i μ]; abel
  rw [h12, Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add, cl_nil,
    Category.id_comp, show (-(N : ℤ) - 1) = -D.h i μ - 1 by omega, bubR_eq_c,
    show ((T:ℤ) + N) = ((T + N : ℕ) : ℤ) by push_cast; ring, bubL_nat, epsL_add,
    ← cl_comp hdT (sChain_epsL i N), epsP_eq_of_nonneg cs hh, ← hN,
    ← cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i),
    ← cl_comp (sChain_lcrossL i i) (sChain_epsL i N),
    ← cl_comp hdT (sChain_sigmaL i i)]
  simp only [Category.assoc, Linear.comp_smul, Category.comp_id, smul_add, smul_smul]
  rw [← hNh]
  have e1 : isg k (D.parity i) (-(N:ℤ) - 1) = isg k (D.parity i) (N + 1) :=
    isg_congr _ ⟨-N - 1, by ring⟩
  have e2 : zsign k (D.parity i * ((N : ℤ) : ZMod 2)) = isg k (D.parity i) N := rfl
  rw [e1, e2]
  have e3 : zsign k (D.parity i) * (-isg k (D.parity i) N * (↑(cs.c μ i)⁻¹ : k)) =
      -(isg k (D.parity i) (N + 1)) * (↑(cs.c μ i)⁻¹ : k) := by
    rw [← isg_one, isg_add (m := N)]; ring
  rw [e3, add_assoc, ← add_smul, show -(isg k (D.parity i) (N + 1)) * (↑(cs.c μ i)⁻¹ : k) +
    isg k (D.parity i) (N + 1) * (↑(cs.c μ i)⁻¹ : k) = 0 by ring, zero_smul, add_zero]


theorem zmod2_mul_self' (a : ZMod 2) : a * a = a := by revert a; decide

theorem zsign_mul_self' (p : ZMod 2) : zsign k p * zsign k p = 1 := by
  rw [← zsign_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, zsign_zero]

/-- The second sum in the proof of (5.8) (`⟨hᵢ, λ⟩` arbitrary), the terms with `s ≥ 0`, after
the dot slide (3.3). -/
theorem ig_pos (i : I) (μ : X) (T : ℕ) :
    ∑ m ∈ range (T + 1), isg k (D.parity i) m •
        (bubL cs i μ ((T:ℤ) - 1 - m) ≫ bubR cs i μ m) =
      isg k (D.parity i) (T + 1) • (etaP cs i μ ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] T) ≫ epsP cs i μ) -
      zsign k (D.parity i) • (etaP cs i μ ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (dotsL [] i [dn i] T ++ sigmaL i i) ≫ epsP cs i μ) +
      isg k (D.parity i) T • (bubL cs i μ (-1) ≫ bubR cs i μ T) := by
  rw [sum_range_succ, show (T:ℤ) - 1 - T = -1 by ring]
  congr 1
  have hterm : ∀ r ∈ range T, isg k (D.parity i) ((T - 1 - r : ℕ) : ℤ) •
      (bubL cs i μ ((T:ℤ) - 1 - ((T - 1 - r : ℕ) : ℤ)) ≫ bubR cs i μ ((T - 1 - r : ℕ) : ℤ)) =
      isg k (D.parity i) (T + 1) • (etaP cs i μ ≫ (zsign k (D.parity i * r) •
        cl D Sc μ [up i, dn i] [dn i, up i]
          (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            dotsL [dn i] i [] (T - 1 - r))) ≫ epsP cs i μ) := by
    intro r hr
    rw [mem_range] at hr
    rw [show (T:ℤ) - 1 - ((T - 1 - r : ℕ) : ℤ) = (r : ℤ) by omega, bubL_nat, bubR_nat,
      Category.assoc, ← Category.assoc (cl D Sc μ [up i, dn i] [] (epsL i r)),
      cl_comp (sChain_epsL i r) (sChain_etaL i _), Linear.smul_comp, Linear.comp_smul, smul_smul,
      isg_natCast]
    congr 1
    · have h3 : ((T - 1 - r : ℕ) : ℤ) = T - 1 - r := by omega
      rw [← isg_add, h3]; exact isg_congr _ ⟨-1 - r, by ring⟩
    · simp only [epsL, etaL, List.append_assoc, List.cons_append, List.nil_append]
  rw [← sum_range_reflect, sum_congr rfl hterm, ← smul_sum]
  simp only [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  rw [← lemma31_eq3_eq Sc i μ T]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul,
    smul_sub, smul_smul]
  congr 2
  rw [zmod2_mul_self', isg_natCast, ← isg_add, ← isg_one]
  exact isg_congr _ ⟨T, by ring⟩

/-- **(5.8), first identity** (Brundan–Ellis, proof of Proposition 5.1), in the form with the
two ranges of `s` separated: for `⟨hᵢ, λ⟩ ≥ 0` and `t = T + 1 > 0`,
`∑_{r+s=t-2} (-1)^{|i|s} (bubble with r dots on the left) ≫ (bubble with s dots on the right) = 0`
(the left bubble below). -/
theorem ig_hpos_split (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (T : ℕ) :
    ∑ n ∈ range ((D.h i μ).toNat + 1), isg k (D.parity i) (-(n:ℤ) - 1) •
        (bubL cs i μ ((T:ℤ) + n) ≫ bubR cs i μ (-(n:ℤ) - 1)) +
      ∑ m ∈ range (T + 1), isg k (D.parity i) m •
        (bubL cs i μ ((T:ℤ) - 1 - m) ≫ bubR cs i μ m) = 0 := by
  rw [ig_hpos_neg cs i μ hh, ig_pos]
  rw [show ∀ x y w : ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])),
    x + (y - x + w) = y + w from fun x y w => by abel]
  have hdR : SChain [dn i, up i] (dotsL [dn i] i [] T) [dn i, up i] := sChain_dotsL [dn i] i [] T
  rcases hh.lt_or_eq with hp | h0
  · rw [← cl_comp (sChain_sigmaL i i) hdR, ← Category.assoc (etaP cs i μ),
      ← Category.assoc (etaP cs i μ), eq_2_13_a cs i μ hp, bubL_eq_zero_of_lt cs i μ (by omega)]
    simp
  · have hlσ := (sChain_lcrossL i i).append (sChain_sigmaL i i)
    have hW : etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] T) =
        -((zsign k (ipar D i μ) * (cs.c μ i : k)) • cl D Sc μ [] [dn i, up i] (etaL i T)) := by
      have e : cl D Sc μ [] [dn i, up i] (etaL i 0) ≫
          cl D Sc μ [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) ≫
            cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] T) =
          cl D Sc μ [] [up i, dn i] (etaL i 0 ++ lcrossL i i) ≫
            cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] T) := by
        rw [cl_comp hlσ hdR, cl_comp (sChain_etaL i 0) (hlσ.append hdR),
          cl_comp ((sChain_etaL i 0).append (sChain_lcrossL i i)) ((sChain_sigmaL i i).append hdR)]
        simp only [List.append_assoc]
      rw [etaP_eq_of_nonpos cs (by omega), show (-D.h i μ).toNat = 0 by omega, Linear.smul_comp, ← e,
        cl_invP₂ Sc i μ hh, Preadditive.neg_comp, Preadditive.comp_neg, cl_nil, Category.id_comp,
        cl_comp (sChain_etaL i 0) hdR, ← etaL_add, zero_add, smul_neg]
    rw [show (-1 : ℤ) = D.h i μ - 1 by omega, bubL_eq_c, ← Category.assoc, hW, Preadditive.neg_comp,
      Linear.smul_comp, ← bubR_nat, Linear.smul_comp, Category.id_comp, smul_neg, smul_smul,
      smul_smul, ← neg_smul, ← add_smul]
    convert zero_smul k _
    simp only [ipar, ← h0, Int.cast_zero, zero_add, mul_one]
    rw [isg_add, isg_one]
    linear_combination (-(isg k (D.parity i) T * (cs.c μ i : k))) * zsign_mul_self' (k := k) (D.parity i)


/-! ## (5.8) for `⟨hᵢ, λ⟩ ≤ 0` -/

theorem bubL_neg_of_lt (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    bubL cs i μ (-(n : ℤ) - 1) = (-(isg k (D.parity i) (D.h i μ - n)) * (cs.c μ i : k)) •
      cl D Sc μ [] [] (etaL i (-D.h i μ).toNat ++ dcapL i n) := by
  rw [bubL, ite_eq_right (show ¬ (0 : ℤ) ≤ -(n : ℤ) - 1 by omega),
    ite_eq_left (show D.h i μ - 1 < -(n : ℤ) - 1 by omega),
    show (-(-(n : ℤ) - 1) - 1).toNat = n by omega, isg]
  congr 4
  push_cast; ring

/-- The first sum in the mirrored computation of (5.8) (`⟨hᵢ, λ⟩ ≤ 0`), the terms with `r < 0`. -/
theorem ig_hneg_neg (i : I) (μ : X) (hh : D.h i μ ≤ 0) (T : ℕ) :
    ∑ n ∈ range ((-D.h i μ).toNat + 1), isg k (D.parity i) (-(n:ℤ) - 1) •
        (bubL cs i μ (-(n:ℤ) - 1) ≫ bubR cs i μ ((T:ℤ) + n)) =
      -(etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] T) ≫
        epsP cs i μ) := by
  set M := (-D.h i μ).toNat with hM
  have hMh : (M : ℤ) = -D.h i μ := Int.toNat_of_nonneg (by omega)
  have hdR : SChain [dn i, up i] (dotsL [dn i] i [] T) [dn i, up i] := sChain_dotsL [dn i] i [] T
  have hterm : ∀ n ∈ range M, isg k (D.parity i) (-(n:ℤ) - 1) •
      (bubL cs i μ (-(n:ℤ) - 1) ≫ bubR cs i μ ((T:ℤ) + n)) =
      (-(isg k (D.parity i) (D.h i μ + 1)) * (cs.c μ i : k)) •
        (cl D Sc μ [] [dn i, up i] (etaL i M) ≫
          cl D Sc μ [dn i, up i] [dn i, up i] (dcapL i n ++ etaL i n) ≫
            cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] T) ≫ epsP cs i μ) := by
    intro n hn
    rw [mem_range] at hn
    rw [show ((T:ℤ) + n) = ((n + T : ℕ) : ℤ) by push_cast; ring, bubR_nat,
      bubL_neg_of_lt cs i μ n (by omega), Linear.smul_comp, smul_smul, etaL_add,
      ← cl_comp (sChain_etaL i n) hdR, ← cl_comp (sChain_etaL i _) (sChain_dcapL i n),
      ← cl_comp (sChain_dcapL i n) (sChain_etaL i n)]
    simp only [Category.assoc, ← hM]
    congr 1
    rw [show isg k (D.parity i) (-(n:ℤ) - 1) * (-isg k (D.parity i) (D.h i μ - n) * (cs.c μ i : k))
        = -(isg k (D.parity i) (-(n:ℤ) - 1) * isg k (D.parity i) (D.h i μ - n)) * (cs.c μ i : k)
        by ring, ← isg_add, isg_congr _ (n := D.h i μ + 1) ⟨-n - 1, by ring⟩]
  rw [sum_range_succ, sum_congr rfl hterm, ← smul_sum]
  simp only [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  have h12 : ∑ n ∈ range M, cl D Sc μ [dn i, up i] [dn i, up i] (dcapL i n ++ etaL i n) =
      cl D Sc μ [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) +
        cl D Sc μ [dn i, up i] [dn i, up i] [] := by
    rw [eq_2_12_b Sc i μ]; abel
  have hlσ := (sChain_lcrossL i i).append (sChain_sigmaL i i)
  have e : cl D Sc μ [] [dn i, up i] (etaL i M) ≫
      cl D Sc μ [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) ≫
        cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] T) =
      cl D Sc μ [] [up i, dn i] (etaL i M ++ lcrossL i i) ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] T) := by
    rw [cl_comp hlσ hdR, cl_comp (sChain_etaL i M) (hlσ.append hdR),
      cl_comp ((sChain_etaL i M).append (sChain_lcrossL i i)) ((sChain_sigmaL i i).append hdR)]
    simp only [List.append_assoc]
  rw [h12, Preadditive.add_comp, Preadditive.comp_add, cl_nil, Category.id_comp,
    show (-(M : ℤ) - 1) = D.h i μ - 1 by omega, bubL_eq_c,
    show ((T:ℤ) + M) = ((M + T : ℕ) : ℤ) by push_cast; ring, bubR_nat, etaL_add,
    ← cl_comp (sChain_etaL i M) hdR, etaP_eq_of_nonpos cs hh, ← hM,
    Linear.smul_comp (f := cl D Sc μ [] [up i, dn i] (etaL i M ++ lcrossL i i)),
    ← Category.assoc (cl D Sc μ [] [up i, dn i] (etaL i M ++ lcrossL i i)), ← e]
  simp only [Category.assoc, Linear.smul_comp, Category.id_comp, smul_add, smul_smul]
  have e1 : isg k (D.parity i) (D.h i μ - 1) = isg k (D.parity i) (D.h i μ + 1) :=
    isg_congr _ ⟨-1, by ring⟩
  have e2 : zsign k (ipar D i μ) = isg k (D.parity i) (D.h i μ + 1) := by
    simp [ipar, isg]
  rw [e1, e2]
  module

/-- The second sum in the mirrored computation of (5.8): the terms with `r ≥ 0`. -/
theorem ig_pos' (i : I) (μ : X) (T : ℕ) :
    ∑ m ∈ range (T + 1), isg k (D.parity i) m •
        (bubL cs i μ m ≫ bubR cs i μ ((T:ℤ) - 1 - m)) =
      etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] T) ≫
        epsP cs i μ -
      isg k (D.parity i) T • (etaP cs i μ ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (dotsL [] i [dn i] T ++ sigmaL i i) ≫ epsP cs i μ) +
      isg k (D.parity i) T • (bubL cs i μ T ≫ bubR cs i μ (-1)) := by
  rw [sum_range_succ, show (T:ℤ) - 1 - T = -1 by ring]
  congr 1
  have hterm : ∀ r ∈ range T, isg k (D.parity i) (r : ℤ) •
      (bubL cs i μ (r : ℤ) ≫ bubR cs i μ ((T:ℤ) - 1 - r)) =
      etaP cs i μ ≫ (zsign k (D.parity i * r) •
        cl D Sc μ [up i, dn i] [dn i, up i]
          (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            dotsL [dn i] i [] (T - 1 - r))) ≫ epsP cs i μ := by
    intro r hr
    rw [mem_range] at hr
    rw [show (T:ℤ) - 1 - r = ((T - 1 - r : ℕ) : ℤ) by omega, bubL_nat, bubR_nat,
      Category.assoc, ← Category.assoc (cl D Sc μ [up i, dn i] [] (epsL i r)),
      cl_comp (sChain_epsL i r) (sChain_etaL i _), Linear.smul_comp, Linear.comp_smul,
      isg_natCast]
    congr 3
    simp only [epsL, etaL, List.append_assoc, List.cons_append, List.nil_append]
  rw [sum_congr rfl hterm]
  simp only [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  rw [← lemma31_eq3_eq Sc i μ T]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul]
  rw [zmod2_mul_self', isg_natCast]

/-- **(5.8), second identity, mirrored** (`⟨hᵢ, λ⟩ ≤ 0`, `t = T + 1 > 0`):
`∑_{r+s=t-2} (-1)^{|i|r} (bubble with r dots on the left) ≫ (bubble with s dots on the right) = 0`
(the left bubble below). The paper's second identity in (5.8) has the opposite vertical order; it is
obtained from this one by the Chevalley involution and supercommuting the bubbles. -/
theorem ig_hneg_split (i : I) (μ : X) (hh : D.h i μ ≤ 0) (T : ℕ) :
    ∑ n ∈ range ((-D.h i μ).toNat + 1), isg k (D.parity i) (-(n:ℤ) - 1) •
        (bubL cs i μ (-(n:ℤ) - 1) ≫ bubR cs i μ ((T:ℤ) + n)) +
      ∑ m ∈ range (T + 1), isg k (D.parity i) m •
        (bubL cs i μ m ≫ bubR cs i μ ((T:ℤ) - 1 - m)) = 0 := by
  rw [ig_hneg_neg cs i μ hh, ig_pos']
  rw [show ∀ x y w : ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])),
    -x + (x - y + w) = w - y from fun x y w => by abel]
  have hdL : SChain [up i, dn i] (dotsL [] i [dn i] T) [up i, dn i] := sChain_dotsL [] i [dn i] T
  rw [← smul_sub, ← cl_comp hdL (sChain_sigmaL i i), Category.assoc]
  rcases hh.lt_or_eq with hp | h0
  · rw [eq_2_14_a cs i μ hp, bubR_eq_zero_of_lt cs i μ (by omega)]
    simp
  · have hY : cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ epsP cs i μ =
        (↑(cs.c μ i)⁻¹ : k) • cl D Sc μ [up i, dn i] [] (epsL i 0) := by
      rw [epsP_eq_of_nonneg cs (by omega), show (D.h i μ).toNat = 0 by omega, Linear.comp_smul,
        cl_comp (sChain_sigmaL i i) ((sChain_lcrossL i i).append (sChain_epsL i 0)),
        ← List.append_assoc,
        ← cl_comp ((sChain_sigmaL i i).append (sChain_lcrossL i i)) (sChain_epsL i 0),
        cl_invM₂ Sc i μ hh,
        Preadditive.neg_comp, cl_nil, Category.id_comp, h0]
      simp [zsign_zero]
    rw [hY, show (-1 : ℤ) = -D.h i μ - 1 by omega, bubR_eq_c, Linear.comp_smul, Linear.comp_smul,
      Category.comp_id, cl_comp hdL (sChain_epsL i 0), ← epsL_add, add_zero, Linear.comp_smul,
      ← bubL_nat, sub_self, smul_zero]


/-! ## Parities of the bubbles -/

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- The dotted bubble `bubL i μ n` has parity `|i|(n + ⟨hᵢ, λ⟩ + 1)`. -/
theorem bubL_mem (i : I) (μ : X) (n : ℤ) :
    bubL cs i μ n ∈ closedPar D Sc μ (D.parity i * ((n + D.h i μ + 1 : ℤ) : ZMod 2)) := by
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [bubL_nat]
    rcases lt_or_ge 0 (D.h i μ) with hp | hp
    · rw [etaP_of_pos cs hp, Linear.smul_comp, cl_comp (sChain_dcupL i _) (sChain_epsL i m)]
      refine Submodule.smul_mem _ _ (cl_mem_closedPar ((sChain_dcupL i _).append
        (sChain_epsL i m)) ?_)
      simp only [parsum, parity_sum_append, parity_dcupL, parity_epsL,
        natCast_toNat_zmod _ (show 0 ≤ D.h i μ - 1 by omega)]
      push_cast
      generalize D.parity i = a; generalize (m : ZMod 2) = x; generalize (D.h i μ : ZMod 2) = y
      revert a x y; decide
    · rw [etaP_eq_of_nonpos cs hp, Linear.smul_comp,
        cl_comp ((sChain_etaL i _).append (sChain_lcrossL i i)) (sChain_epsL i m)]
      refine Submodule.smul_mem _ _ (cl_mem_closedPar (((sChain_etaL i _).append
        (sChain_lcrossL i i)).append (sChain_epsL i m)) ?_)
      simp only [parsum, parity_sum_append, parity_etaL, parity_lcrossL, parity_epsL,
        natCast_toNat_zmod _ (show 0 ≤ -D.h i μ by omega)]
      push_cast
      generalize D.parity i = a; generalize (m : ZMod 2) = x; generalize (D.h i μ : ZMod 2) = y
      revert a x y; decide
  · rw [bubL]
    split_ifs with h1 h2 h3
    · omega
    · refine Submodule.smul_mem _ _ (cl_mem_closedPar ((sChain_etaL i _).append
        (sChain_dcapL i _)) ?_)
      simp only [parsum, parity_sum_append, parity_etaL, parity_dcapL,
        natCast_toNat_zmod _ (show 0 ≤ -D.h i μ by omega),
        natCast_toNat_zmod _ (show 0 ≤ -n - 1 by omega)]
      push_cast
      generalize D.parity i = a; generalize (n : ZMod 2) = x; generalize (D.h i μ : ZMod 2) = y
      revert a x y; decide
    · refine Submodule.smul_mem _ _ ?_
      rw [← cl_nil μ []]
      refine cl_mem_closedPar (L := []) (SChain.nil' []) ?_
      rw [h3, show D.h i μ - 1 + D.h i μ + 1 = 2 * D.h i μ by ring]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl]; simp
    · exact Submodule.zero_mem _

/-- The dotted bubble `bubR i μ n` has parity `|i|(n + ⟨hᵢ, λ⟩ + 1)`. -/
theorem bubR_mem (i : I) (μ : X) (n : ℤ) :
    bubR cs i μ n ∈ closedPar D Sc μ (D.parity i * ((n + D.h i μ + 1 : ℤ) : ZMod 2)) := by
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [bubR_nat]
    rcases lt_or_ge (D.h i μ) 0 with hp | hp
    · rw [epsP_of_neg cs hp, Linear.comp_smul, cl_comp (sChain_etaL i m) (sChain_dcapL i _)]
      refine Submodule.smul_mem _ _ (cl_mem_closedPar ((sChain_etaL i m).append
        (sChain_dcapL i _)) ?_)
      simp only [parsum, parity_sum_append, parity_dcapL, parity_etaL,
        natCast_toNat_zmod _ (show 0 ≤ -D.h i μ - 1 by omega)]
      push_cast
      generalize D.parity i = a; generalize (m : ZMod 2) = x; generalize (D.h i μ : ZMod 2) = y
      revert a x y; decide
    · rw [epsP_eq_of_nonneg cs hp, Linear.comp_smul,
        cl_comp (sChain_etaL i m) ((sChain_lcrossL i i).append (sChain_epsL i _))]
      refine Submodule.smul_mem _ _ (cl_mem_closedPar ((sChain_etaL i m).append
        ((sChain_lcrossL i i).append (sChain_epsL i _))) ?_)
      simp only [parsum, parity_sum_append, parity_etaL, parity_lcrossL, parity_epsL,
        natCast_toNat_zmod _ hp]
      push_cast
      generalize D.parity i = a; generalize (m : ZMod 2) = x; generalize (D.h i μ : ZMod 2) = y
      revert a x y; decide
  · rw [bubR]
    split_ifs with h1 h2 h3
    · omega
    · refine Submodule.smul_mem _ _ (cl_mem_closedPar ((sChain_dcupL i _).append
        (sChain_epsL i _)) ?_)
      simp only [parsum, parity_sum_append, parity_dcupL, parity_epsL,
        natCast_toNat_zmod _ (show 0 ≤ D.h i μ by omega),
        natCast_toNat_zmod _ (show 0 ≤ -n - 1 by omega)]
      push_cast
      generalize D.parity i = a; generalize (n : ZMod 2) = x; generalize (D.h i μ : ZMod 2) = y
      revert a x y; decide
    · refine Submodule.smul_mem _ _ ?_
      rw [← cl_nil μ []]
      refine cl_mem_closedPar (L := []) (SChain.nil' []) ?_
      rw [h3, show -D.h i μ - 1 + D.h i μ + 1 = 0 by ring]
      simp
    · exact Submodule.zero_mem _

/-- Even bubbles commute with all bubbles; in general bubbles supercommute. -/
theorem bubL_bubR_comm (i : I) (μ : X) (r s : ℤ) :
    bubL cs i μ r ≫ bubR cs i μ s =
      zsign k (D.parity i * ((r + D.h i μ + 1 : ℤ) : ZMod 2) *
        (D.parity i * ((s + D.h i μ + 1 : ℤ) : ZMod 2))) • (bubR cs i μ s ≫ bubL cs i μ r) :=
  comm_of_mem (bubL_mem cs i μ r) (bubR_mem cs i μ s)


/-! ## (5.8) as sums over `r + s = t - 2` -/

/-- **Brundan–Ellis, (5.8), first identity**: for `⟨hᵢ, λ⟩ ≥ 0` and `t = T + 1 > 0`,
`∑_{r+s=t-2} (-1)^{|i|s} bubL(r) ≫ bubR(s) = 0` (sum over the `s` for which the term can be
nonzero; all other terms vanish by (5.3)–(5.4)). -/
theorem ig_hpos (i : I) (μ : X) (hh : 0 ≤ D.h i μ) (T : ℕ) :
    ∑ s ∈ Icc (-((D.h i μ).toNat : ℤ) - 1) T, isg k (D.parity i) s •
      (bubL cs i μ ((T:ℤ) - 1 - s) ≫ bubR cs i μ s) = 0 := by
  rw [sum_Icc_split (fun s => isg k (D.parity i) s • (bubL cs i μ ((T:ℤ) - 1 - s) ≫ bubR cs i μ s))]
  simp only [show ∀ n : ℕ, (T:ℤ) - 1 - (-(n:ℤ) - 1) = T + n from fun n => by ring]
  exact ig_hpos_split cs i μ hh T

/-- **Brundan–Ellis, (5.8), second identity (mirrored order)**: for `⟨hᵢ, λ⟩ ≤ 0` and
`t = T + 1 > 0`, `∑_{r+s=t-2} (-1)^{|i|r} bubL(r) ≫ bubR(s) = 0`. -/
theorem ig_hneg (i : I) (μ : X) (hh : D.h i μ ≤ 0) (T : ℕ) :
    ∑ r ∈ Icc (-((-D.h i μ).toNat : ℤ) - 1) T, isg k (D.parity i) r •
      (bubL cs i μ r ≫ bubR cs i μ ((T:ℤ) - 1 - r)) = 0 := by
  rw [sum_Icc_split (fun r => isg k (D.parity i) r • (bubL cs i μ r ≫ bubR cs i μ ((T:ℤ) - 1 - r)))]
  simp only [show ∀ n : ℕ, (T:ℤ) - 1 - (-(n:ℤ) - 1) = T + n from fun n => by ring]
  exact ig_hneg_split cs i μ hh T

/-- **Brundan–Ellis, Proposition 5.1, (5.5)**: for even `i` and `t > 0`,
`∑_{r+s=t, r,s ≥ 0}` (the clockwise bubble with `s + *` dots, below) `≫` (the counterclockwise
bubble with `r + *` dots, above) `= 0`. -/
theorem eq_5_5 (i : I) (μ : X) (hi : D.parity i = 0) (t : ℕ) (ht : 0 < t) :
    ∑ r ∈ range (t + 1), bubRs cs i μ ((t : ℤ) - r) ≫ bubLs cs i μ r = 0 := by
  obtain ⟨T, rfl⟩ : ∃ T, t = T + 1 := ⟨t - 1, by omega⟩
  have hisg : ∀ x : ℤ, isg k (D.parity i) x = 1 := fun x => by simp [isg, hi, zsign_zero]
  have hcomm : ∀ r : ℕ, bubRs cs i μ (((T + 1 : ℕ) : ℤ) - r) ≫ bubLs cs i μ r =
      bubL cs i μ ((r : ℤ) + D.h i μ - 1) ≫ bubR cs i μ ((T : ℤ) - 1 - ((r : ℤ) + D.h i μ - 1)) := by
    intro r
    rw [bubL_bubR_comm, hi, zero_mul, zero_mul, zsign_zero, one_smul, bubRs, bubLs]
    congr 2; push_cast; ring
  simp only [hcomm]
  rcases le_total 0 (D.h i μ) with hh | hh
  · -- reindex by `s = T - 1 - (r + h - 1)`
    have := ig_hpos cs i μ hh T
    simp only [hisg, one_smul] at this
    have e : ∀ r ∈ range (T + 1 + 1), bubL cs i μ ((r : ℤ) + D.h i μ - 1) ≫
        bubR cs i μ ((T : ℤ) - 1 - ((r : ℤ) + D.h i μ - 1)) =
        (fun s => bubL cs i μ ((T:ℤ) - 1 - s) ≫ bubR cs i μ s)
          ((fun r : ℕ => (T : ℤ) - 1 - ((r : ℤ) + D.h i μ - 1)) r) := by
      intro r _
      simp only [show (T : ℤ) - 1 - ((T : ℤ) - 1 - ((r : ℤ) + D.h i μ - 1)) =
        (r : ℤ) + D.h i μ - 1 by ring]
    rw [sum_congr rfl e, ← sum_image (f := fun s => bubL cs i μ ((T:ℤ) - 1 - s) ≫ bubR cs i μ s)
      (g := fun r : ℕ => (T : ℤ) - 1 - ((r : ℤ) + D.h i μ - 1))
      (fun a _ b _ h => by beta_reduce at h; omega), ← this]
    · apply sum_subset
      · intro s hs
        simp only [mem_image, mem_range] at hs
        obtain ⟨r, hr, rfl⟩ := hs
        rw [mem_Icc]; constructor <;> omega
      · intro s hs hns
        rw [mem_Icc] at hs
        simp only [mem_image, mem_range, not_exists, not_and] at hns
        rcases lt_or_ge s (-D.h i μ - 1) with h1 | h1
        · rw [bubR_eq_zero_of_lt cs i μ h1, Limits.comp_zero]
        · have : (T : ℤ) - 1 - s < D.h i μ - 1 := by
            by_contra hc
            exact hns ((T : ℤ) - 1 - s - D.h i μ + 1).toNat (by omega) (by omega)
          rw [bubL_eq_zero_of_lt cs i μ this, Limits.zero_comp]
  · have := ig_hneg cs i μ hh T
    simp only [hisg, one_smul] at this
    rw [← this, ← sum_image (g := fun r : ℕ => (r : ℤ) + D.h i μ - 1)
      (f := fun x => bubL cs i μ x ≫ bubR cs i μ ((T:ℤ) - 1 - x)) (fun a _ b _ h => by
        beta_reduce at h; omega)]
    apply sum_subset
    · intro s hs
      simp only [mem_image, mem_range] at hs
      obtain ⟨r, hr, rfl⟩ := hs
      rw [mem_Icc]; constructor <;> omega
    · intro x hx hnx
      rw [mem_Icc] at hx
      simp only [mem_image, mem_range, not_exists, not_and] at hnx
      rcases lt_or_ge x (D.h i μ - 1) with h1 | h1
      · rw [bubL_eq_zero_of_lt cs i μ h1, Limits.zero_comp]
      · have : (T : ℤ) - 1 - x < -D.h i μ - 1 := by
          by_contra hc
          exact hnx (x - D.h i μ + 1).toNat (by omega) (by omega)
        rw [bubR_eq_zero_of_lt cs i μ this, Limits.comp_zero]

end OddMath.SKM
