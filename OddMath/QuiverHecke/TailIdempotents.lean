/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.TailDecomposition

/-!
# Idempotents of `Z ⊗ P(i^{(ε)})` modulo maps through longer tails

Input to the surjectivity half of Brundan–Ellis, arXiv:1701.04133v2, **Theorem 11.3**, along the
route of Khovanov–Lauda, arXiv:0803.4121v2, §3.2, here for projectives. Fix a word `s`, a colour
`i`, `r = i^ε`, an even degree-zero idempotent `z` of `s` and an even degree-zero idempotent `b`
of `r` such that `b c b ∈ k b` for every map `c : r → r` of degree `≤ 0` (the divided-power
idempotents, `OddMath.QuiverHecke.DividedPowerCorner`). Put `e = z ⊗ b`.

If the even degree-zero endomorphisms of `s` in the corner of `z` are all nilpotent or
invertible (`z` cuts out an indecomposable object), then of two orthogonal idempotents in the
corner of `e`, one is a sum of maps through words ending in `i^{ε+1}`
(`tail_idempotent_mem_tailJ`). Equivalently: in a decomposition of `Z ⊗ P(i^{(ε)})`, all
summands but at most one are summands of words with a longer `i`-tail.

Proof. By the tail decomposition (`homPiece_le_span_tail`), an element `f` of the corner of `e` is
`f = T(a) + v` with `T(a) = a ⊗ b` for an even degree-zero `a` in the corner of `z`, and `v` in
`V₁ = N₁ + J`. Here `N_d` is spanned by the maps `a ⊗ c` with `deg a ≤ -d` (the terms with
`deg a ≥ 0` collapse to `T(a)` or `0` because `b c b ∈ k b`), and `J` by maps through words
ending in `i^{ε+1}`. The `V_d = N_d + J` form a multiplicative filtration with `V_d = J` for
large `d`, since the degrees of maps `s → s` are bounded below. If `a` is nilpotent then a power
of `f = f^m` lies in `J` (`pow_mem_of_filtration`). If both idempotents have invertible
leading terms, then `e ∈ V₁`, and again `f ∈ J`.
-/

noncomputable section

open CategoryTheory StringDiagrams MonoidalCategory

namespace OddMath.QuiverHecke

universe u v w

/-! ## A filtration lemma -/

section Filtration

variable {R : Type*} [Ring R] (V : ℕ → AddSubgroup R)

/-- In a ring with a multiplicative decreasing filtration `V`, if `u` normalizes every `V d`
and `u ^ m = 0`, then `(u + v) ^ (m (q + 1)) ∈ V (q + 1)` for `v ∈ V 1`. -/
theorem pow_mem_of_filtration (hanti : Antitone V)
    (hmul : ∀ {d d' : ℕ} {x y : R}, x ∈ V d → y ∈ V d' → x * y ∈ V (d + d'))
    {u : R} (hl : ∀ {d : ℕ} {x : R}, x ∈ V d → u * x ∈ V d)
    (hr : ∀ {d : ℕ} {x : R}, x ∈ V d → x * u ∈ V d)
    {m : ℕ} (hu : u ^ m = 0) {v : R} (hv : v ∈ V 1) (q : ℕ) :
    (u + v) ^ (m * (q + 1)) ∈ V (q + 1) := by
  have hj : ∀ j : ℕ, u ^ j * v ∈ V 1 := by
    intro j
    induction j with
    | zero => simpa using hv
    | succ j ihj => rw [pow_succ', mul_assoc]; exact hl ihj
  have h1 : ∀ j : ℕ, (u + v) ^ j - u ^ j ∈ V 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (u + v) ^ (j + 1) - u ^ (j + 1) =
          ((u + v) ^ j - u ^ j) * u + ((u + v) ^ j - u ^ j) * v + u ^ j * v := by
        rw [pow_succ, pow_succ, mul_add, sub_mul, sub_mul]; abel
      rw [e]
      exact add_mem (add_mem (hr ih) (hanti (by omega) (hmul ih hv))) (hj j)
  have hm : (u + v) ^ m ∈ V 1 := by simpa [hu] using h1 m
  induction q with
  | zero => simpa using hm
  | succ q ih =>
    rw [show m * (q + 1 + 1) = m * (q + 1) + m by ring, pow_add]
    exact hmul ih hm

end Filtration

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- The endomorphisms of the word `t` in `H`. -/
abbrev HEnd (t : List I) := hObj D Sc sy hc t ⟶ hObj D Sc sy hc t

/-! ## Homogeneous pieces -/

section Pieces

variable {D Sc sy hc}

theorem eq_zero_of_mem_homPiece {t t' : List I} {n n' : ℤ} {p p' : ZMod 2}
    {x : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'} (hx : x ∈ homPiece D Sc sy hc t t' n p)
    (hx' : x ∈ homPiece D Sc sy hc t t' n' p') (h : n ≠ n' ∨ p ≠ p') : x = 0 := by
  rcases h with h | h
  · exact Submodule.disjoint_def.1
      ((DirectSum.IsInternal.submodule_iSupIndep (GradedSupercategory.isInternal_degree
        (R := k) (C := HGr D Sc sy hc) _ _)).pairwiseDisjoint h) x hx.1 hx'.1
  · exact Submodule.disjoint_def.1
      ((DirectSum.IsInternal.submodule_iSupIndep (Supercategory.isInternal
        (R := k) (C := HGr D Sc sy hc) _ _)).pairwiseDisjoint h) x hx.2 hx'.2

theorem homPiece_eq_bot_of_lt (t t' : List I) :
    ∃ N : ℤ, ∀ n p, n < N → homPiece D Sc sy hc t t' n p = ⊥ := by
  obtain ⟨N, hN⟩ := exists_le_deg D sy t t'
  refine ⟨N, fun n p hn => ?_⟩
  rw [homPiece_eq_span, Submodule.span_eq_bot]
  rintro _ ⟨j, ⟨-, hj⟩, -⟩
  have := hN j
  omega

theorem mem_homPiece_cast {t t' : List I} {n n' : ℤ} {p p' : ZMod 2}
    {x : hObj D Sc sy hc t ⟶ hObj D Sc sy hc t'} (hx : x ∈ homPiece D Sc sy hc t t' n p)
    (hn : n = n') (hp : p = p') : x ∈ homPiece D Sc sy hc t t' n' p' := hn ▸ hp ▸ hx

end Pieces

/-! ## The filtration of `End(s i^ε)` -/

section Tail

variable (s : List I) (i : I) (ε : ℕ)

/-- The maps `(1_s ⊗ c)(a ⊗ 1_r) : s r → s r`, `r = i^ε`, of degree zero and parity `p`, with
`a` and `c` homogeneous and `deg a ≤ -d`. -/
def tailP (d : ℕ) (p : ZMod 2) :
    Set (HEnd D Sc sy hc (s ++ List.replicate ε i)) :=
  {f | ∃ (n₁ n₂ : ℤ) (p₁ p₂ : ZMod 2) (a : HEnd D Sc sy hc s)
    (c : HEnd D Sc sy hc (List.replicate ε i)),
    a ∈ homPiece D Sc sy hc s s n₁ p₁ ∧
    c ∈ homPiece D Sc sy hc (List.replicate ε i) (List.replicate ε i) n₂ p₂ ∧
    n₁ + n₂ = 0 ∧ p₁ + p₂ = p ∧ n₁ ≤ -(d : ℤ) ∧
    f = (hObj D Sc sy hc s ◁ c) ≫ (a ▷ hObj D Sc sy hc (List.replicate ε i))}

/-- The span `N_d` of `tailP d` (in parity `p`). -/
abbrev tailN (d : ℕ) (p : ZMod 2) :
    Submodule k (hObj D Sc sy hc (s ++ List.replicate ε i) ⟶
      hObj D Sc sy hc (s ++ List.replicate ε i)) :=
  Submodule.span k (tailP D Sc sy hc s i ε d p)

/-- The span `J` of the degree-zero maps of parity `p` through words ending in `i^{ε+1}`. -/
abbrev tailJ (p : ZMod 2) :
    Submodule k (hObj D Sc sy hc (s ++ List.replicate ε i) ⟶
      hObj D Sc sy hc (s ++ List.replicate ε i)) :=
  Submodule.span k (tailThrough D Sc sy hc s s i ε 0 p)

/-- The filtration `V_d = N_d + J` (in parity `p`). -/
abbrev tailV (d : ℕ) (p : ZMod 2) :
    Submodule k (hObj D Sc sy hc (s ++ List.replicate ε i) ⟶
      hObj D Sc sy hc (s ++ List.replicate ε i)) :=
  tailN D Sc sy hc s i ε d p ⊔ tailJ D Sc sy hc s i ε p

variable {D Sc sy hc s i ε}


theorem tailP_mem_homPiece {d : ℕ} {p : ZMod 2} {f : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hf : f ∈ tailP D Sc sy hc s i ε d p) :
    f ∈ homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 p := by
  obtain ⟨n₁, n₂, p₁, p₂, a, c, ha, hc', hn, hp, -, rfl⟩ := hf
  exact mem_homPiece_cast (comp_mem_homPiece (whiskerLeft_mem_homPiece _ hc')
    (whiskerRight_mem_homPiece _ ha)) (by omega) (by rw [add_comm, hp])

theorem tailN_le (d : ℕ) (p : ZMod 2) :
    tailN D Sc sy hc s i ε d p ≤
      homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 p :=
  Submodule.span_le.2 fun _ hf => tailP_mem_homPiece hf

theorem tailN_antitone (p : ZMod 2) : Antitone fun d => tailN D Sc sy hc s i ε d p := by
  intro d d' h
  refine Submodule.span_mono ?_
  rintro _ ⟨n₁, n₂, p₁, p₂, a, c, ha, hc', hn, hp, hd, rfl⟩
  exact ⟨n₁, n₂, p₁, p₂, a, c, ha, hc', hn, hp, by omega, rfl⟩

theorem tailN_eq_bot : ∃ B : ℕ, ∀ p, tailN D Sc sy hc s i ε B p = ⊥ := by
  obtain ⟨N, hN⟩ := homPiece_eq_bot_of_lt (D := D) (Sc := Sc) (sy := sy) (hc := hc) s s
  refine ⟨N.natAbs + 1, fun p => ?_⟩
  rw [Submodule.span_eq_bot]
  rintro _ ⟨n₁, n₂, p₁, p₂, a, c, ha, hc', hn, hp, hd, rfl⟩
  have ha0 : a = 0 := by
    have := hN n₁ p₁ (by omega)
    rw [this] at ha
    exact (Submodule.mem_bot k).1 ha
  rw [ha0, MonoidalSupercategory.zero_whiskerRight k, Limits.comp_zero]

theorem comp_mem_tailJ_left {p q : ZMod 2} {x y : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hx : x ∈ homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 q)
    (hy : y ∈ tailJ D Sc sy hc s i ε p) : x ≫ y ∈ tailJ D Sc sy hc s i ε (q + p) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, n₁, n₂, p₁, p₂, g₁, g₂, hg₁, hg₂, hn, hp, rfl⟩ := hy
    refine Submodule.subset_span ⟨w, hw, n₁, n₂, q + p₁, p₂, x ≫ g₁, g₂,
      mem_homPiece_cast (comp_mem_homPiece hx hg₁) (zero_add _) rfl, hg₂, hn,
      by rw [add_assoc, hp], (Category.assoc _ _ _).symm⟩
  | zero => rw [Limits.comp_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [Preadditive.comp_add]; exact add_mem h h'
  | smul c y _ h => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c h

theorem comp_mem_tailJ_right {p q : ZMod 2} {x y : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hx : x ∈ homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 q)
    (hy : y ∈ tailJ D Sc sy hc s i ε p) : y ≫ x ∈ tailJ D Sc sy hc s i ε (p + q) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, n₁, n₂, p₁, p₂, g₁, g₂, hg₁, hg₂, hn, hp, rfl⟩ := hy
    refine Submodule.subset_span ⟨w, hw, n₁, n₂, p₁, p₂ + q, g₁, g₂ ≫ x, hg₁,
      mem_homPiece_cast (comp_mem_homPiece hg₂ hx) (add_zero _) rfl, hn,
      by rw [← add_assoc, hp], Category.assoc _ _ _⟩
  | zero => rw [Limits.zero_comp]; exact zero_mem _
  | add y y' _ _ h h' => rw [Preadditive.add_comp]; exact add_mem h h'
  | smul c y _ h => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c h

theorem tailP_comp {d d' : ℕ} {p p' : ZMod 2} {f f' : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hf : f ∈ tailP D Sc sy hc s i ε d p)
    (hf' : f' ∈ tailP D Sc sy hc s i ε d' p') :
    f ≫ f' ∈ tailN D Sc sy hc s i ε (d + d') (p + p') := by
  obtain ⟨n₁, n₂, p₁, p₂, a, c, ha, hc', hn, hp, hd, rfl⟩ := hf
  obtain ⟨n₁', n₂', p₁', p₂', a', c', ha', hc'', hn', hp', hd', rfl⟩ := hf'
  have e : ((hObj D Sc sy hc s ◁ c) ≫ (a ▷ hObj D Sc sy hc (List.replicate ε i))) ≫
      ((hObj D Sc sy hc s ◁ c') ≫ (a' ▷ hObj D Sc sy hc (List.replicate ε i))) =
      Supercategory.koszulSign p₁ p₂' • ((hObj D Sc sy hc s ◁ (c ≫ c')) ≫
        ((a ≫ a') ▷ hObj D Sc sy hc (List.replicate ε i))) := by
    rw [Category.assoc, ← Category.assoc (a ▷ hObj D Sc sy hc (List.replicate ε i)),
      MonoidalSupercategory.super_interchange (R := k) ha.2 hc''.2,
      MonoidalSupercategory.whiskerLeft_comp (R := k),
      MonoidalSupercategory.comp_whiskerRight (R := k)]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [e]
  refine zsmul_mem (Submodule.subset_span (show _ ∈ tailP D Sc sy hc s i ε (d + d') (p + p') from
    ⟨n₁ + n₁', n₂ + n₂', p₁ + p₁', p₂ + p₂',
    a ≫ a', c ≫ c', comp_mem_homPiece ha ha', comp_mem_homPiece hc' hc'', by omega,
    by rw [show p₁ + p₁' + (p₂ + p₂') = (p₁ + p₂) + (p₁' + p₂') by abel, hp, hp'],
    by push_cast; omega, rfl⟩)) _

theorem tailN_comp {d d' : ℕ} {p p' : ZMod 2} {f f' : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hf : f ∈ tailN D Sc sy hc s i ε d p)
    (hf' : f' ∈ tailN D Sc sy hc s i ε d' p') :
    f ≫ f' ∈ tailN D Sc sy hc s i ε (d + d') (p + p') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    induction hf' using Submodule.span_induction with
    | mem f' hf' => exact tailP_comp hf hf'
    | zero => rw [Limits.comp_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [Preadditive.comp_add]; exact add_mem h h'
    | smul c y _ h => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c h
  | zero => rw [Limits.zero_comp]; exact zero_mem _
  | add y y' _ _ h h' => rw [Preadditive.add_comp]; exact add_mem h h'
  | smul c y _ h => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c h

theorem tailV_le (d : ℕ) (p : ZMod 2) :
    tailV D Sc sy hc s i ε d p ≤
      homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 p := by
  refine sup_le (tailN_le d p) (Submodule.span_le.2 ?_)
  rintro _ ⟨w, hw, n₁, n₂, p₁, p₂, g₁, g₂, hg₁, hg₂, hn, hp, rfl⟩
  exact mem_homPiece_cast (comp_mem_homPiece hg₁ hg₂) hn hp

theorem tailV_comp {d d' : ℕ} {p p' : ZMod 2} {f f' : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hf : f ∈ tailV D Sc sy hc s i ε d p)
    (hf' : f' ∈ tailV D Sc sy hc s i ε d' p') :
    f ≫ f' ∈ tailV D Sc sy hc s i ε (d + d') (p + p') := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hf
  obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.1 hf'
  have hy0 := tailV_le d p (Submodule.mem_sup_right hy)
  rw [Preadditive.comp_add, Preadditive.add_comp, Preadditive.add_comp]
  refine add_mem (add_mem (Submodule.mem_sup_left (tailN_comp hx hx'))
    (Submodule.mem_sup_right (comp_mem_tailJ_right (tailN_le d' p' hx') hy)))
    (Submodule.mem_sup_right ?_)
  rw [← Preadditive.add_comp]
  exact comp_mem_tailJ_left (add_mem (tailN_le d p hx) hy0) hy'

/-! ## The leading term -/

variable (s) in
/-- `T(a) = a ⊗ b`. -/
def tailT (b : HEnd D Sc sy hc (List.replicate ε i)) (a : HEnd D Sc sy hc s) :
    HEnd D Sc sy hc (s ++ List.replicate ε i) :=
  (hObj D Sc sy hc s ◁ b) ≫ (a ▷ hObj D Sc sy hc (List.replicate ε i))

variable {b : HEnd D Sc sy hc (List.replicate ε i)}

theorem tailT_add (a a' : HEnd D Sc sy hc s) : tailT s b (a + a') = tailT s b a + tailT s b a' := by
  rw [tailT, tailT, tailT, MonoidalSupercategory.add_whiskerRight (R := k), Preadditive.comp_add]

theorem tailT_smul (c : k) (a : HEnd D Sc sy hc s) : tailT s b (c • a) = c • tailT s b a := by
  rw [tailT, tailT, MonoidalSupercategory.smul_whiskerRight (R := k), Linear.comp_smul]

theorem tailT_zero : tailT s b (0 : HEnd D Sc sy hc s) = 0 := by
  rw [tailT, MonoidalSupercategory.zero_whiskerRight k, Limits.comp_zero]

variable (hb : b ≫ b = b)
  (hb0 : b ∈ homPiece D Sc sy hc (List.replicate ε i) (List.replicate ε i) 0 0)
include hb hb0

theorem tailT_comp {p : ZMod 2} {a a' : HEnd D Sc sy hc s}
    (ha : a ∈ Supercategory.parity (R := k) (hObj D Sc sy hc s) (hObj D Sc sy hc s) p) :
    tailT s b a ≫ tailT s b a' = tailT s b (a ≫ a') := by
  rw [tailT, tailT, tailT, Category.assoc,
    ← Category.assoc (a ▷ hObj D Sc sy hc (List.replicate ε i)),
    MonoidalSupercategory.interchange_of_even_right (R := k) ha hb0.2, Category.assoc,
    ← Category.assoc (hObj D Sc sy hc s ◁ b),
    ← MonoidalSupercategory.whiskerLeft_comp (R := k), hb,
    ← MonoidalSupercategory.comp_whiskerRight (R := k)]

omit hb in
theorem tailT_mem_tailN {p : ZMod 2} {a : HEnd D Sc sy hc s}
    (ha : a ∈ homPiece D Sc sy hc s s 0 p) : tailT s b a ∈ tailN D Sc sy hc s i ε 0 p :=
  Submodule.subset_span ⟨0, 0, p, 0, a, b, ha, hb0, rfl, add_zero p, le_rfl, rfl⟩

omit hb in
/-- Conjugating `(1 ⊗ c)(a ⊗ 1)` by `e = z ⊗ b`. -/
theorem tailT_conj {z : HEnd D Sc sy hc s} (hz0 : z ∈ homPiece D Sc sy hc s s 0 0) {p q : ZMod 2}
    {a : HEnd D Sc sy hc s}
    (ha : a ∈ Supercategory.parity (R := k) (hObj D Sc sy hc s) (hObj D Sc sy hc s) p)
    {c : HEnd D Sc sy hc (List.replicate ε i)}
    (hc' : c ∈ Supercategory.parity (R := k) (hObj D Sc sy hc (List.replicate ε i))
      (hObj D Sc sy hc (List.replicate ε i)) q) :
    tailT s b z ≫ ((hObj D Sc sy hc s ◁ c) ≫
        (a ▷ hObj D Sc sy hc (List.replicate ε i))) ≫ tailT s b z =
      (hObj D Sc sy hc s ◁ (b ≫ c ≫ b)) ≫
        ((z ≫ a ≫ z) ▷ hObj D Sc sy hc (List.replicate ε i)) := by
  simp only [tailT, Category.assoc]
  rw [← Category.assoc (z ▷ hObj D Sc sy hc (List.replicate ε i)) (hObj D Sc sy hc s ◁ c),
    MonoidalSupercategory.interchange_of_even_left (R := k) hz0.2 hc', Category.assoc,
    ← Category.assoc (a ▷ hObj D Sc sy hc (List.replicate ε i)) (hObj D Sc sy hc s ◁ b),
    MonoidalSupercategory.interchange_of_even_right (R := k) ha hb0.2, Category.assoc,
    ← Category.assoc (z ▷ hObj D Sc sy hc (List.replicate ε i)) (hObj D Sc sy hc s ◁ b),
    MonoidalSupercategory.interchange_of_even_right (R := k) hz0.2 hb0.2]
  simp only [MonoidalSupercategory.whiskerLeft_comp (R := k),
    MonoidalSupercategory.comp_whiskerRight (R := k), Category.assoc]

variable (hcorner : ∀ {n : ℤ} {p : ZMod 2} {c : HEnd D Sc sy hc (List.replicate ε i)},
  c ∈ homPiece D Sc sy hc (List.replicate ε i) (List.replicate ε i) n p → n ≤ 0 →
    b ≫ c ≫ b ∈ k ∙ b)
include hcorner

omit hb in
/-- **Leading term.** Every degree-zero map `f : s i^ε → s i^ε` of parity `p`, conjugated by
`e = z ⊗ b`, is `T(a) + v` with `a` a degree-zero map of parity `p` in the corner of `z` and
`v ∈ V₁`. -/
theorem tailT_conj_sub_mem {z : HEnd D Sc sy hc s} (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz : z ≫ z = z) {p : ZMod 2} {f : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hf : f ∈ homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 p) :
    ∃ a : HEnd D Sc sy hc s, a ∈ homPiece D Sc sy hc s s 0 p ∧ z ≫ a ≫ z = a ∧
      tailT s b z ≫ f ≫ tailT s b z - tailT s b a ∈ tailV D Sc sy hc s i ε 1 p := by
  have hgen := homPiece_le_span_tail (D := D) (Sc := Sc) (sy := sy) (hc := hc) (s := s)
    (s' := s) rfl i ε 0 p hf
  clear hf
  induction hgen using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨n₁, n₂, p₁, p₂, a, c, ha, hc', hn, hp, rfl⟩ |
      ⟨w, hw, n₁, n₂, p₁, p₂, g₁, g₂, hg₁, hg₂, hn, hp, rfl⟩
    · rw [tailT_conj hb0 hz0 ha.2 hc'.2]
      have hzaz : z ≫ a ≫ z ∈ homPiece D Sc sy hc s s n₁ p₁ :=
        mem_homPiece_cast (comp_mem_homPiece hz0 (comp_mem_homPiece ha hz0)) (by simp)
          (by simp)
      have hbcb : b ≫ c ≫ b ∈ homPiece D Sc sy hc _ _ n₂ p₂ :=
        mem_homPiece_cast (comp_mem_homPiece hb0 (comp_mem_homPiece hc' hb0)) (by simp)
          (by simp)
      by_cases hneg : n₁ ≤ -1
      · refine ⟨0, zero_mem _, by simp, ?_⟩
        rw [tailT_zero, sub_zero]
        exact Submodule.mem_sup_left (Submodule.subset_span
          ⟨n₁, n₂, p₁, p₂, _, _, hzaz, hbcb, hn, hp, by push_cast; omega, rfl⟩)
      · obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 (hcorner hc' (by omega))
        by_cases h00 : n₁ = 0 ∧ p₁ = p
        · obtain ⟨rfl, rfl⟩ := h00
          refine ⟨μ • (z ≫ a ≫ z), Submodule.smul_mem _ _ hzaz, ?_, ?_⟩
          · simp only [Linear.comp_smul, Linear.smul_comp, ← Category.assoc, hz]
            simp only [Category.assoc, hz]
          · rw [← hμ, MonoidalSupercategory.whiskerLeft_smul (R := k), Linear.smul_comp,
              tailT_smul, tailT, sub_self]
            exact zero_mem _
        · have hz' : μ • b = 0 := by
            refine eq_zero_of_mem_homPiece (hμ ▸ hbcb) (Submodule.smul_mem _ μ hb0) ?_
            by_cases h' : n₁ = 0
            · right; intro hp2; apply h00; refine ⟨h', ?_⟩
              rw [hp2, add_zero] at hp; exact hp
            · left; omega
          refine ⟨0, zero_mem _, by simp, ?_⟩
          rw [← hμ, hz', MonoidalSupercategory.whiskerLeft_zero k, Limits.zero_comp, tailT_zero,
            sub_zero]
          exact zero_mem _
    · refine ⟨0, zero_mem _, by simp, ?_⟩
      rw [tailT_zero, sub_zero]
      have he := tailT_mem_tailN hb0 hz0 |> tailN_le 0 0
      refine Submodule.mem_sup_right (Submodule.subset_span ⟨w, hw, n₁, n₂, p₁, p₂,
        tailT s b z ≫ g₁, g₂ ≫ tailT s b z,
        mem_homPiece_cast (comp_mem_homPiece he hg₁) (zero_add _) (zero_add _),
        mem_homPiece_cast (comp_mem_homPiece hg₂ he) (add_zero _) (add_zero _), hn, hp, ?_⟩)
      simp only [Category.assoc]
  | zero =>
    refine ⟨0, zero_mem _, by simp, ?_⟩
    simp only [Limits.zero_comp, Limits.comp_zero, tailT_zero, sub_zero]
    exact zero_mem _
  | add f f' _ _ h h' =>
    obtain ⟨a, ha, haz, hv⟩ := h
    obtain ⟨a', ha', haz', hv'⟩ := h'
    refine ⟨a + a', add_mem ha ha', by
      rw [Preadditive.add_comp, Preadditive.comp_add, haz, haz'], ?_⟩
    rw [Preadditive.add_comp, Preadditive.comp_add, tailT_add]
    convert add_mem hv hv' using 1
    abel
  | smul μ f _ h =>
    obtain ⟨a, ha, haz, hv⟩ := h
    refine ⟨μ • a, Submodule.smul_mem _ μ ha, by
      rw [Linear.smul_comp, Linear.comp_smul, haz], ?_⟩
    rw [Linear.smul_comp, Linear.comp_smul, tailT_smul, ← smul_sub]
    exact Submodule.smul_mem _ μ hv

omit hcorner in
theorem tailT_pow_succ {a : HEnd D Sc sy hc s} (ha : a ∈ homPiece D Sc sy hc s s 0 0) (m : ℕ) :
    (id (tailT s b a) : End (hObj D Sc sy hc (s ++ List.replicate ε i))) ^ (m + 1) =
      tailT s b ((id a : End (hObj D Sc sy hc s)) ^ (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ (id a : End (hObj D Sc sy hc s))]
    exact tailT_comp hb hb0 ha.2

omit hb hb0 hcorner in
theorem tailV_antitone (p : ZMod 2) : Antitone fun d => tailV D Sc sy hc s i ε d p :=
  fun _ _ h => sup_le_sup_right (tailN_antitone p h) _

omit hcorner in
/-- An even map `w` with `w - T(a) ∈ V₁` for a nilpotent `a` has a power in `J`. -/
theorem pow_mem_tailJ_of_isNilpotent {w : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    {a : HEnd D Sc sy hc s} (ha : a ∈ homPiece D Sc sy hc s s 0 0)
    (han : IsNilpotent (id a : End (hObj D Sc sy hc s)))
    (hv : w - tailT s b a ∈ tailV D Sc sy hc s i ε 1 0) :
    ∃ M : ℕ, (id w : End (hObj D Sc sy hc (s ++ List.replicate ε i))) ^ (M + 1) ∈
      tailJ D Sc sy hc s i ε 0 := by
  obtain ⟨B, hB⟩ := tailN_eq_bot (D := D) (Sc := Sc) (sy := sy) (hc := hc) (s := s) (i := i)
    (ε := ε)
  obtain ⟨m, hm⟩ := han
  let V : ℕ → AddSubgroup (End (hObj D Sc sy hc (s ++ List.replicate ε i))) :=
    fun d => (tailV D Sc sy hc s i ε d 0).toAddSubgroup
  have hu0 : tailT s b a ∈ tailV D Sc sy hc s i ε 0 0 :=
    Submodule.mem_sup_left (tailT_mem_tailN hb0 ha)
  have key := pow_mem_of_filtration V (fun _ _ h => tailV_antitone 0 h)
    (fun {d d' x y} hx hy => by
      change y ≫ x ∈ tailV D Sc sy hc s i ε (d + d') 0
      rw [add_comm]; simpa using tailV_comp hy hx)
    (u := (id (tailT s b a) : End (hObj D Sc sy hc (s ++ List.replicate ε i))))
    (fun {d x} hx => by
      change x ≫ tailT s b a ∈ tailV D Sc sy hc s i ε d 0
      simpa using tailV_comp hx hu0)
    (fun {d x} hx => by
      change tailT s b a ≫ x ∈ tailV D Sc sy hc s i ε d 0
      simpa using tailV_comp hu0 hx)
    (m := m + 1) (by rw [tailT_pow_succ hb hb0 ha, pow_succ, hm, zero_mul, tailT_zero]) hv B
  rw [id, add_sub_cancel, show (m + 1) * (B + 1) = (m * B + m + B) + 1 by ring] at key
  refine ⟨m * B + m + B, ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 key
  have : x = 0 := by
    rw [← Submodule.mem_bot k, ← hB 0]; exact tailN_antitone 0 (Nat.le_succ B) hx
  rw [id, ← hxy, this, zero_add]; exact hy

omit hcorner in
/-- An idempotent `f` with `f - T(a) ∈ V₁` for a nilpotent `a` lies in `J`. -/
theorem idem_mem_tailJ_of_isNilpotent {f : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hf : f ≫ f = f) {a : HEnd D Sc sy hc s} (ha : a ∈ homPiece D Sc sy hc s s 0 0)
    (han : IsNilpotent (id a : End (hObj D Sc sy hc s)))
    (hv : f - tailT s b a ∈ tailV D Sc sy hc s i ε 1 0) : f ∈ tailJ D Sc sy hc s i ε 0 := by
  obtain ⟨M, hM⟩ := pow_mem_tailJ_of_isNilpotent hb hb0 ha han hv
  have hidem : IsIdempotentElem (id f : End (hObj D Sc sy hc (s ++ List.replicate ε i))) := hf
  rw [id] at hidem
  rwa [id, hidem.pow_succ_eq] at hM

/-- **At most one summand outside `J`.** Let `z` be an even degree-zero idempotent of `s` whose
corner consists of nilpotent and invertible elements, and `e = z ⊗ b`. Of two idempotents
`f₁, f₂` in the corner of `e` with `f₁ f₂ = 0`, one lies in `J`: it is a sum of maps through
words ending in `i^{ε+1}`. -/
theorem tail_idempotent_mem_tailJ {z : HEnd D Sc sy hc s} (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)
    (hz : z ≫ z = z)
    (hloc : ∀ a : HEnd D Sc sy hc s, a ∈ homPiece D Sc sy hc s s 0 0 → z ≫ a ≫ z = a →
      IsNilpotent (id a : End (hObj D Sc sy hc s)) ∨ ∃ a' : HEnd D Sc sy hc s,
        a' ∈ homPiece D Sc sy hc s s 0 0 ∧ a ≫ a' = z ∧ a' ≫ a = z)
    {f₁ f₂ : HEnd D Sc sy hc (s ++ List.replicate ε i)}
    (hf₁ : f₁ ∈ homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 0)
    (hf₂ : f₂ ∈ homPiece D Sc sy hc (s ++ List.replicate ε i) (s ++ List.replicate ε i) 0 0)
    (he₁ : tailT s b z ≫ f₁ ≫ tailT s b z = f₁)
    (he₂ : tailT s b z ≫ f₂ ≫ tailT s b z = f₂)
    (hi₁ : f₁ ≫ f₁ = f₁) (hi₂ : f₂ ≫ f₂ = f₂) (h₁₂ : f₁ ≫ f₂ = 0) :
    f₁ ∈ tailJ D Sc sy hc s i ε 0 ∨ f₂ ∈ tailJ D Sc sy hc s i ε 0 := by
  obtain ⟨a₁, ha₁, hc₁, hv₁⟩ := tailT_conj_sub_mem hb0 hcorner hz0 hz hf₁
  obtain ⟨a₂, ha₂, hc₂, hv₂⟩ := tailT_conj_sub_mem hb0 hcorner hz0 hz hf₂
  rw [he₁] at hv₁
  rw [he₂] at hv₂
  rcases hloc a₁ ha₁ hc₁ with hn₁ | ⟨a₁', ha₁', hu₁, hu₁'⟩
  · exact Or.inl (idem_mem_tailJ_of_isNilpotent hb hb0 hi₁ ha₁ hn₁ hv₁)
  rcases hloc a₂ ha₂ hc₂ with hn₂ | ⟨a₂', ha₂', hu₂, hu₂'⟩
  · exact Or.inr (idem_mem_tailJ_of_isNilpotent hb hb0 hi₂ ha₂ hn₂ hv₂)
  left
  have hT : ∀ {a : HEnd D Sc sy hc s}, a ∈ homPiece D Sc sy hc s s 0 0 →
      tailT s b a ∈ tailV D Sc sy hc s i ε 0 0 :=
    fun ha => Submodule.mem_sup_left (tailT_mem_tailN hb0 ha)
  have hV10 : tailV D Sc sy hc s i ε 1 0 ≤ tailV D Sc sy hc s i ε 0 0 :=
    tailV_antitone 0 (Nat.zero_le 1)
  have hf₁0 : f₁ ∈ tailV D Sc sy hc s i ε 0 0 := by
    simpa using add_mem (hT ha₁) (hV10 hv₁)
  have hf₂0 : f₂ ∈ tailV D Sc sy hc s i ε 0 0 := by
    simpa using add_mem (hT ha₂) (hV10 hv₂)
  -- `T(a₁ a₂) ∈ V₁`
  have h12 : tailT s b a₁ ≫ tailT s b a₂ ∈ tailV D Sc sy hc s i ε 1 0 := by
    have e : tailT s b a₁ ≫ tailT s b a₂ = f₁ ≫ f₂ - f₁ ≫ (f₂ - tailT s b a₂) -
        (f₁ - tailT s b a₁) ≫ f₂ + (f₁ - tailT s b a₁) ≫ (f₂ - tailT s b a₂) := by
      simp only [Preadditive.comp_sub, Preadditive.sub_comp]; abel
    rw [e, h₁₂, zero_sub]
    refine add_mem (sub_mem (neg_mem ?_) ?_) (tailV_antitone 0 (by omega)
      (show _ ∈ tailV D Sc sy hc s i ε 2 0 by simpa using tailV_comp hv₁ hv₂))
    · simpa using tailV_comp hf₁0 hv₂
    · simpa using tailV_comp hv₁ hf₂0
  -- hence `e = T(z) ∈ V₁`
  have he : tailT s b z ∈ tailV D Sc sy hc s i ε 1 0 := by
    have hz1 : a₁ ≫ z = a₁ := by rw [← hc₁]; simp only [Category.assoc, hz]
    have e : tailT s b z =
        tailT s b a₁' ≫ (tailT s b a₁ ≫ tailT s b a₂) ≫ tailT s b a₂' := by
      rw [tailT_comp hb hb0 ha₁.2, tailT_comp hb hb0 (comp_mem_homPiece ha₁ ha₂).2,
        tailT_comp hb hb0 ha₁'.2]
      congr 1
      simp only [Category.assoc]
      rw [hu₂, hz1, hu₁']
    rw [e]
    simpa using tailV_comp (hT ha₁') (tailV_comp h12 (hT ha₂'))
  have hf₁1 : f₁ ∈ tailV D Sc sy hc s i ε 1 0 := by
    rw [← he₁]; simpa using tailV_comp he (tailV_comp hf₁0 (hT hz0))
  exact idem_mem_tailJ_of_isNilpotent hb hb0 hi₁ (zero_mem _) IsNilpotent.zero
    (by rwa [tailT_zero, sub_zero])

end Tail

end OddMath.QuiverHecke
