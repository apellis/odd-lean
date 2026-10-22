/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ShuffleBasis
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.Centre

/-!
# Maps between words with a common tail `i^e`

Input to the surjectivity half of Brundan–Ellis, arXiv:1701.04133v2, **Theorem 11.3**, along the
route of Khovanov–Lauda, arXiv:0803.4121v2, §3.2 (the operators `e_i` and the largest power of
`i` at the end of a word), here for the projectives of the quiver Hecke superalgebras.

For words `s`, `s'` of the same length and `r = i^e`, every map `s r → s' r` of `H` is a sum of
* maps `a ⊗ c = (1_s ⊗ c)(a ⊗ 1_r)` with `a : s → s'` and `c ∈ End(i^e)`, and
* maps through words ending in `i^{e+1}`,

with all factors homogeneous and their degrees and parities adding up
(`homPiece_le_span_tail`). This is read off the shuffle basis (Hill–Wang, arXiv:1202.2769v2,
Proposition 6.4, `shuffleBasis`) of `Hom(s r, s' r)` for the split `s' | r` of the target: the
trivial shuffle gives the elements `a ⊗ c`, and for any other shuffle `d` the last letter of the
first block of the top word of `ψ_d` comes from `r`, so the top word ends in `i^{e+1}`
(`isShuffle_eq_one`).

## Main results

* `isShuffle_eq_one`: a shuffle that keeps the first block in place is the identity.
* `homPiece_le_span_tail`: the decomposition above.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA MonoidalCategory
namespace OddMath.QuiverHecke

universe u v w
variable {I : Type u}

/-! ## Shuffles -/

section Shuffle

open Equiv

/-- A shuffle `d` for blocks of sizes `m` and `n` with `d⁻¹(m - 1) < m` (that is, the first
block is not moved past any letter of the second) is the identity. -/
theorem isShuffle_eq_one {m n N : ℕ} {h : m + n = N} {d : Perm (Fin N)} (hd : IsShuffle h d)
    (hlast : ∀ hm : 0 < m, (d⁻¹ ⟨m - 1, by omega⟩ : ℕ) < m) : d = 1 := by
  -- the first block is fixed
  have h₁ : ∀ x : Fin N, (x : ℕ) < m → d⁻¹ x = x := by
    have hlt : ∀ x : Fin m, (d⁻¹ (blockEquiv h (Sum.inl x)) : ℕ) < m := fun x => by
      have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) x.2
      refine lt_of_le_of_lt ?_ (hlast hm)
      have hle := hd.1.monotone (show x ≤ ⟨m - 1, by omega⟩ from Fin.le_def.2 (by simp; omega))
      exact Fin.le_def.1 hle
    let f : Fin m → Fin m := fun x => ⟨d⁻¹ (blockEquiv h (Sum.inl x)), hlt x⟩
    have hf : StrictMono f := fun x y hxy => Fin.lt_def.2 (Fin.lt_def.1 (hd.1 hxy))
    intro x hx
    have e := congrArg Fin.val (congrFun hf.eq_id ⟨x, hx⟩)
    exact Fin.ext (by simpa [f, blockEquiv, finSumFinEquiv] using e)
  -- the second block is sent to itself
  have h₂ : ∀ x : Fin N, m ≤ (x : ℕ) → m ≤ (d⁻¹ x : ℕ) := by
    intro x hx
    by_contra hc
    have e := h₁ (d⁻¹ x) (by omega)
    have := d⁻¹.injective e
    rw [this] at hc
    omega
  have h₃ : ∀ x : Fin N, m ≤ (x : ℕ) → d⁻¹ x = x := by
    let g : Fin n → Fin n := fun y => ⟨(d⁻¹ (blockEquiv h (Sum.inr y)) : ℕ) - m, by
      have := (d⁻¹ (blockEquiv h (Sum.inr y))).2; have := y.2; omega⟩
    have hg : StrictMono g := fun y y' hyy' => by
      have a := Fin.lt_def.1 (hd.2 hyy')
      simp only at a
      have b := h₂ (blockEquiv h (Sum.inr y)) (by simp)
      exact Fin.lt_def.2 (by simp only [g]; omega)
    intro x hx
    have e := congrArg Fin.val (congrFun hg.eq_id ⟨x - m, by omega⟩)
    have hb : blockEquiv h (Sum.inr ⟨x - m, by omega⟩) = x := Fin.ext (by simp; omega)
    simp only [g, hb, id] at e
    have := h₂ x hx
    exact Fin.ext (by omega)
  have hinv : d⁻¹ = 1 := Perm.ext fun x => by
    by_cases hx : (x : ℕ) < m
    · exact h₁ x hx
    · exact h₃ x (by omega)
  exact inv_eq_one.mp hinv

end Shuffle

/-! ## Homogeneity -/

variable {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

theorem cl_mem_homPiece {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    (cl D Sc t t' gs h : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t') ∈
      homPiece D Sc sy hc t t' (gsum D sy (pl t gs))
        ((pl t gs).map fun x => x.2.1.parity D).sum :=
  ⟨Presentation.diag_mem_homDeg' (degree_gdeg_mkD D sy _ _),
    Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)⟩

theorem NFIdx.nf_mem_homPiece {t t' : List I} (i : NFIdx t t') :
    (i.nf (D := D) (Sc := Sc) : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t') ∈
      homPiece D Sc sy hc t t' (i.deg D sy) (i.par D) :=
  cl_mem_homPiece D Sc sy hc _ _

variable {D Sc sy hc}

theorem comp_mem_homPiece {t₁ t₂ t₃ : List I} {n₁ n₂ : ℤ} {p₁ p₂ : ZMod 2}
    {f : hObj D Sc sy hc t₁ ⟶ hObj D Sc sy hc t₂} {g : hObj D Sc sy hc t₂ ⟶ hObj D Sc sy hc t₃}
    (hf : f ∈ homPiece D Sc sy hc t₁ t₂ n₁ p₁) (hg : g ∈ homPiece D Sc sy hc t₂ t₃ n₂ p₂) :
    f ≫ g ∈ homPiece D Sc sy hc t₁ t₃ (n₁ + n₂) (p₁ + p₂) :=
  ⟨GradedSupercategory.comp_mem_degree hf.1 hg.1, Supercategory.comp_mem hf.2 hg.2⟩

theorem whiskerLeft_mem_homPiece (l : List I) {t t' : List I} {n : ℤ} {p : ZMod 2}
    {f : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'} (hf : f ∈ homPiece D Sc sy hc t t' n p) :
    (hObj D Sc sy hc l ◁ f : hObj D Sc sy hc (l ++ t) ⟶ hObj D Sc sy hc (l ++ t')) ∈
      homPiece D Sc sy hc (l ++ t) (l ++ t') n p :=
  ⟨GradedMonoidalSupercategory.whiskerLeft_mem_degree (R := k) (hObj D Sc sy hc l) hf.1,
    MonoidalSupercategory.whiskerLeft_mem (R := k) (hObj D Sc sy hc l) hf.2⟩

theorem whiskerRight_mem_homPiece (r : List I) {t t' : List I} {n : ℤ} {p : ZMod 2}
    {f : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'} (hf : f ∈ homPiece D Sc sy hc t t' n p) :
    (f ▷ hObj D Sc sy hc r : hObj D Sc sy hc (t ++ r) ⟶ hObj D Sc sy hc (t' ++ r)) ∈
      homPiece D Sc sy hc (t ++ r) (t' ++ r) n p :=
  ⟨GradedMonoidalSupercategory.whiskerRight_mem_degree (R := k) (hObj D Sc sy hc r) hf.1,
    MonoidalSupercategory.whiskerRight_mem (R := k) (hObj D Sc sy hc r) hf.2⟩

/-! ## The two kinds of maps -/

variable (D Sc sy hc)

/-- The maps `(1_s ⊗ c)(a ⊗ 1_r) : s r → s' r` of degree `n` and parity `p`, for homogeneous
`a : s → s'` and `c ∈ End(r)` whose degrees and parities add up to `n` and `p`. -/
def tailParabolic (s s' r : List I) (n : ℤ) (p : ZMod 2) :
    Set (hObj D Sc sy hc (s ++ r) ⟶ hObj D Sc sy hc (s' ++ r)) :=
  {f | ∃ (n₁ n₂ : ℤ) (p₁ p₂ : ZMod 2) (a : hObj D Sc sy hc s ⟶ hObj D Sc sy hc s')
    (c : hObj D Sc sy hc r ⟶ hObj D Sc sy hc r), a ∈ homPiece D Sc sy hc s s' n₁ p₁ ∧
    c ∈ homPiece D Sc sy hc r r n₂ p₂ ∧ n₁ + n₂ = n ∧ p₁ + p₂ = p ∧
    f = (hObj D Sc sy hc s ◁ c) ≫ (a ▷ hObj D Sc sy hc r)}

/-- The maps `s i^e → s' i^e` of degree `n` and parity `p` which are composites `g₂ g₁` of
homogeneous maps through a word ending in `i^{e+1}`, with degrees and parities adding up. -/
def tailThrough (s s' : List I) (i : I) (e : ℕ) (n : ℤ) (p : ZMod 2) :
    Set (hObj D Sc sy hc (s ++ List.replicate e i) ⟶ hObj D Sc sy hc (s' ++ List.replicate e i)) :=
  {f | ∃ (w : List I) (_ : List.replicate (e + 1) i <:+ w) (n₁ n₂ : ℤ) (p₁ p₂ : ZMod 2)
    (g₁ : hObj D Sc sy hc (s ++ List.replicate e i) ⟶ hObj D Sc sy hc w)
    (g₂ : hObj D Sc sy hc w ⟶ hObj D Sc sy hc (s' ++ List.replicate e i)),
    g₁ ∈ homPiece D Sc sy hc _ _ n₁ p₁ ∧ g₂ ∈ homPiece D Sc sy hc _ _ n₂ p₂ ∧ n₁ + n₂ = n ∧
    p₁ + p₂ = p ∧ f = g₁ ≫ g₂}

variable {D Sc sy hc}

/-- The shuffle basis element of the trivial shuffle is of the form `a ⊗ c`. -/
theorem cl_comp_mem_tailParabolic {s s' r L R : List I} (hL : L = s) (hR : R = r)
    (gs : List PG) (hgs : gs = []) (h : SChain (s ++ r) (pl (s ++ r) gs) (L ++ R))
    (a : NFIdx L s') (c : NFIdx R r) :
    ∃ n p, (cl D Sc (s ++ r) (L ++ R) gs h ≫ ((pres D Sc).obj (ob D L) ◁ c.nf) ≫
        (a.nf ▷ (pres D Sc).obj (ob D r)) : hObj D Sc sy hc (s ++ r) ⟶ hObj D Sc sy hc (s' ++ r)) ∈
      homPiece D Sc sy hc (s ++ r) (s' ++ r) n p ∧
      (cl D Sc (s ++ r) (L ++ R) gs h ≫ ((pres D Sc).obj (ob D L) ◁ c.nf) ≫
        (a.nf ▷ (pres D Sc).obj (ob D r)) : hObj D Sc sy hc (s ++ r) ⟶ hObj D Sc sy hc (s' ++ r)) ∈
      tailParabolic D Sc sy hc s s' r n p := by
  subst hL hR hgs
  rw [cl_nil, Category.id_comp]
  refine ⟨c.deg D sy + a.deg D sy, c.par D + a.par D, comp_mem_homPiece
    (whiskerLeft_mem_homPiece _ (c.nf_mem_homPiece D Sc sy hc))
    (whiskerRight_mem_homPiece _ (a.nf_mem_homPiece D Sc sy hc)), ?_⟩
  exact ⟨a.deg D sy, c.deg D sy, a.par D, c.par D, a.nf, c.nf, a.nf_mem_homPiece D Sc sy hc,
    c.nf_mem_homPiece D Sc sy hc, add_comm _ _, add_comm _ _, rfl⟩

/-- A word reached from `i^e` by crossings is `i^e`. -/
theorem eq_replicate_of_nfIdx {R : List I} {i : I} {e : ℕ} (c : NFIdx R (List.replicate e i)) :
    R = List.replicate e i := by
  have ht := NFIdx.tgt_cw c
  have hlen : R.length = e := by simpa using congrArg List.length ht
  refine List.eq_replicate_iff.2 ⟨hlen, fun b hb => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have hq := tgt_cw_getElem (validWord_canWord R.length c.1.2) (t := R) rfl
    (wordProd R.length (canWord R.length c.1.2) ⟨j, hj⟩)
  have hinv : (wordProd R.length (canWord R.length c.1.2))⁻¹
      (wordProd R.length (canWord R.length c.1.2) ⟨j, hj⟩) = ⟨j, hj⟩ :=
    Equiv.symm_apply_apply _ _
  simp only [hinv] at hq
  rw [← hq, List.getElem_of_eq ht]
  simp

/-- For a shuffle `d ≠ 1` of the split `s' | i^e` of `s i^e`, the top word of `ψ_d` ends in
`i^{e+1}`. -/
theorem replicate_suffix_shTop {s s' : List I} {i : I} {e : ℕ}
    (hN : s'.length + (List.replicate e i).length = (s ++ List.replicate e i).length)
    {d : Equiv.Perm (Fin (s ++ List.replicate e i).length)} (hd : IsShuffle hN d) (hd1 : d ≠ 1)
    (hR : shR (s ++ List.replicate e i) s'.length d = List.replicate e i) :
    List.replicate (e + 1) i <:+ shTop (s ++ List.replicate e i) d := by
  have hs : s.length = s'.length := by simp at hN; omega
  obtain ⟨hm, hge⟩ : ∃ hm : 0 < s'.length,
      s'.length ≤ (d⁻¹ ⟨s'.length - 1, by simp; omega⟩ : ℕ) := by
    by_contra hcon
    exact hd1 (isShuffle_eq_one hd fun hm => Nat.lt_of_not_le fun hle => hcon ⟨hm, hle⟩)
  have hlen : (shTop (s ++ List.replicate e i) d).length = s'.length + e := by
    simp [shTop, hs]
  have hall : ∀ j (hj : j < (shTop (s ++ List.replicate e i) d).length), s'.length - 1 ≤ j →
      (shTop (s ++ List.replicate e i) d)[j] = i := by
    intro j hj hj'
    rcases Nat.lt_or_ge j s'.length with hjm | hjm
    · obtain rfl : j = s'.length - 1 := by omega
      have hq := tgt_cw_getElem (validWord_canWord _ d) (t := s ++ List.replicate e i) rfl
        ⟨s'.length - 1, by simp; omega⟩
      rw [wordProd_canWord] at hq
      simp only [shTop]
      rw [hq, List.getElem_append_right (by omega)]
      simp
    · have e₁ : (shTop (s ++ List.replicate e i) d)[j] =
          (shR (s ++ List.replicate e i) s'.length d)[j - s'.length]'(by
            rw [length_shR]; rw [hlen] at hj; simp; omega) := by
        simp only [shR, List.getElem_drop]
        congr 1
        omega
      rw [e₁, List.getElem_of_eq hR]
      simp
  have hdrop : (shTop (s ++ List.replicate e i) d).drop (s'.length - 1) =
      List.replicate (e + 1) i := by
    refine List.eq_replicate_iff.2 ⟨by simp [hlen]; omega, fun b hb => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    rw [List.getElem_drop]
    exact hall _ _ (by omega)
  exact hdrop ▸ List.drop_suffix (s'.length - 1) _

/-! ## The decomposition -/

/-- **Maps between words with a common tail `i^e`.** For words `s`, `s'` of the same length,
every map `s i^e → s' i^e` of degree `n` and parity `p` is a sum of maps `(1_s ⊗ c)(a ⊗ 1)`
with `a : s → s'` and `c ∈ End(i^e)` homogeneous, and of composites of homogeneous maps through
words ending in `i^{e+1}`. Input to Brundan–Ellis, arXiv:1701.04133v2, Theorem 11.3, read off
the shuffle basis (Hill–Wang, arXiv:1202.2769v2, Proposition 6.4). -/
theorem homPiece_le_span_tail {s s' : List I} (hs : s'.length = s.length) (i : I) (e : ℕ)
    (n : ℤ) (p : ZMod 2) :
    homPiece D Sc sy hc (s ++ List.replicate e i) (s' ++ List.replicate e i) n p ≤
      Submodule.span k (tailParabolic D Sc sy hc s s' (List.replicate e i) n p ∪
        tailThrough D Sc sy hc s s' i e n p) := by
  classical
  set r := List.replicate e i
  set t := s ++ r
  have hN : s'.length + r.length = t.length := by simp [t, hs]
  let b : ShIdx hN → (hObj D Sc sy hc t ⟶ hObj D Sc sy hc (s' ++ r)) := fun x => shElt D Sc x
  have key : ∀ x, ∃ np : ℤ × ZMod 2, b x ∈ homPiece D Sc sy hc t (s' ++ r) np.1 np.2 ∧
      b x ∈ tailParabolic D Sc sy hc s s' r np.1 np.2 ∪
        tailThrough D Sc sy hc s s' i e np.1 np.2 := by
    rintro ⟨⟨d, hd⟩, a, c⟩
    by_cases hd1 : d = 1
    · subst hd1
      have hcw : cw (canWord t.length 1) = [] := by
        have := length_canWord t.length 1
        rw [length_one] at this
        rw [List.eq_nil_of_length_eq_zero this, cw_nil]
      have htop : shTop t 1 = t := by rw [shTop, hcw, tgt_nil]
      obtain ⟨n', p', h₁, h₂⟩ := cl_comp_mem_tailParabolic (D := D) (Sc := Sc) (sy := sy)
        (hc := hc) (s := s) (s' := s') (r := r)
        (show shL t s'.length 1 = s by rw [shL, htop]; simp [t, hs])
        (show shR t s'.length 1 = r by rw [shR, htop]; simp [t, hs]) _ hcw _ a c
      exact ⟨(n', p'), h₁, Or.inl h₂⟩
    · have hR := eq_replicate_of_nfIdx c
      have hsuf := replicate_suffix_shTop hN hd hd1 hR
      have hrest := comp_mem_homPiece (whiskerLeft_mem_homPiece _ (c.nf_mem_homPiece D Sc sy hc))
        (whiskerRight_mem_homPiece r (a.nf_mem_homPiece D Sc sy hc))
      have hpsi := cl_mem_homPiece D Sc sy hc (t := t)
        (t' := shL t s'.length d ++ shR t s'.length d) (cw (canWord t.length d))
        (by rw [shL_append_shR]; exact sChain_pl _ _)
      refine ⟨(_, _), comp_mem_homPiece hpsi hrest, Or.inr ?_⟩
      exact ⟨_, by rw [shL_append_shR]; exact hsuf, _, _, _, _, _, _, hpsi, hrest, rfl, rfl, rfl⟩
  choose np hnp using key
  have hrange : Set.range b = Set.range (shuffleBasis D Sc hN) :=
    congrArg Set.range (funext fun x => (shuffleBasis_apply (D := D) (Sc := Sc) x).symm)
  have hspan : Submodule.span k (Set.range b) = ⊤ := by
    rw [hrange]
    exact (shuffleBasis D Sc hN).span_eq
  let _ : DirectSum.Decomposition
      (Supercategory.parity (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t)
        (hObj D Sc sy hc (s' ++ r))) :=
    (Supercategory.isInternal (R := k) (C := HGr D Sc sy hc) _ _).chooseDecomposition
  let _ : DirectSum.Decomposition
      (GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t)
        (hObj D Sc sy hc (s' ++ r))) :=
    (GradedSupercategory.isInternal_degree (R := k) (C := HGr D Sc sy hc) _ _).chooseDecomposition
  have hpar := inf_span_eq_of_homogeneous
    (Supercategory.parity (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t)
      (hObj D Sc sy hc (s' ++ r))) (b := b) (fun x => (np x).2) (fun x => (hnp x).1.2) Set.univ p
  rw [Set.image_univ, hspan, inf_top_eq] at hpar
  have hdeg := inf_span_eq_of_homogeneous
    (GradedSupercategory.degree (R := k) (C := HGr D Sc sy hc) (hObj D Sc sy hc t)
      (hObj D Sc sy hc (s' ++ r))) (b := b) (fun x => (np x).1) (fun x => (hnp x).1.1)
    {x | x ∈ Set.univ ∧ (np x).2 = p} n
  rw [homPiece, hpar, hdeg]
  refine Submodule.span_mono ?_
  rintro _ ⟨x, ⟨⟨-, hxp⟩, hxn⟩, rfl⟩
  have := (hnp x).2
  rwa [hxp, hxn] at this

end OddMath.QuiverHecke
