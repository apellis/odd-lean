/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RelationsNF

/-!
# Dot slides through upward crossings (Brundan–Ellis, Lemma 3.1 (3.1), (3.2))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 3.1 (TeX label
`firstlemma`), relations (3.1) (`upcross1`) and (3.2) (`upcross2`): for all `n ≥ 0`,

* (3.1) `(xⁿ ⊗ 1) ≫ τ - (-1)^{|i||j|n} τ ≫ (1 ⊗ xⁿ) = δᵢⱼ ∑_{r+s=n-1} (-1)^{|i|s} xʳ ⊗ xˢ`,
  where in the paper's picture the `r` dots (left strand) are drawn below the `s` dots (right
  strand): the left dots come first;
* (3.2) `τ ≫ (xⁿ ⊗ 1) - (-1)^{|i||j|n} (1 ⊗ xⁿ) ≫ τ = δᵢⱼ ∑_{r+s=n-1} (-1)^{|i|s} xʳ ⊗ xˢ`,
  where now the `s` dots (right strand) are drawn below the `r` dots: the right dots come first.

(The relative heights of the dots matter: by the super interchange law the two orders differ by
`(-1)^{|i|rs}`.) The paper proves these "inductively from (1.8)"; here the induction is the
general identity `iter_slide` / `iter_slide'` in any linear category, applied to (1.8).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

/-! ## An iterated commutation identity -/

section Cpow

variable {C : Type*} [Category C]

/-- The `n`-th power of an endomorphism under composition. -/
def cpow {A : C} (x : A ⟶ A) : ℕ → (A ⟶ A)
  | 0 => 𝟙 A
  | n + 1 => cpow x n ≫ x

@[simp] theorem cpow_zero {A : C} (x : A ⟶ A) : cpow x 0 = 𝟙 A := rfl

theorem cpow_succ {A : C} (x : A ⟶ A) (n : ℕ) : cpow x (n + 1) = cpow x n ≫ x := rfl

theorem cpow_succ' {A : C} (x : A ⟶ A) (n : ℕ) : cpow x (n + 1) = x ≫ cpow x n := by
  induction n with
  | zero => simp [cpow_succ]
  | succ n ih =>
    conv_lhs => rw [cpow_succ, ih]
    rw [Category.assoc, ← cpow_succ]

end Cpow

section Iter

variable {C : Type*} [Category C] [Preadditive C] {k : Type*} [CommRing k] [Linear k C]

/-- If `x ≫ t = c • (t ≫ y) + d`, then
`xⁿ ≫ t = cⁿ • (t ≫ yⁿ) + ∑_{s < n} cˢ • (x^{n-1-s} ≫ d ≫ yˢ)`. -/
theorem iter_slide {A B : C} (x : A ⟶ A) (y : B ⟶ B) (t d : A ⟶ B) (c : k)
    (h : x ≫ t = c • (t ≫ y) + d) (n : ℕ) :
    cpow x n ≫ t = c ^ n • (t ≫ cpow y n) +
      ∑ s ∈ Finset.range n, c ^ s • (cpow x (n - 1 - s) ≫ d ≫ cpow y s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cpow_succ', Category.assoc, ih, Preadditive.comp_add, Linear.comp_smul, ← Category.assoc,
      h, Preadditive.add_comp, Linear.smul_comp, Category.assoc, smul_add, smul_smul,
      Preadditive.comp_sum, Finset.sum_range_succ, ← pow_succ, ← cpow_succ']
    have hs : ∀ s ∈ Finset.range n, x ≫ (c ^ s • (cpow x (n - 1 - s) ≫ d ≫ cpow y s)) =
        c ^ s • (cpow x (n + 1 - 1 - s) ≫ d ≫ cpow y s) := by
      intro s hs
      rw [Finset.mem_range] at hs
      rw [Linear.comp_smul, ← Category.assoc, show n + 1 - 1 - s = n - 1 - s + 1 by omega,
        cpow_succ' x (n - 1 - s)]
    rw [Finset.sum_congr rfl hs]
    simp only [Nat.add_sub_cancel, Nat.sub_self, cpow_zero, Category.id_comp]
    abel

/-- If `t ≫ y = c • (x ≫ t) + d`, then
`t ≫ yⁿ = cⁿ • (xⁿ ≫ t) + ∑_{s < n} cˢ • (xˢ ≫ d ≫ y^{n-1-s})`. -/
theorem iter_slide' {A B : C} (x : A ⟶ A) (y : B ⟶ B) (t d : A ⟶ B) (c : k)
    (h : t ≫ y = c • (x ≫ t) + d) (n : ℕ) :
    t ≫ cpow y n = c ^ n • (cpow x n ≫ t) +
      ∑ s ∈ Finset.range n, c ^ s • (cpow x s ≫ d ≫ cpow y (n - 1 - s)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cpow_succ, ← Category.assoc, ih, Preadditive.add_comp, Linear.smul_comp, Category.assoc,
      h, Preadditive.comp_add, Linear.comp_smul, ← Category.assoc, smul_add, smul_smul,
      Preadditive.sum_comp, Finset.sum_range_succ, ← pow_succ, ← cpow_succ]
    have hs : ∀ s ∈ Finset.range n, (c ^ s • (cpow x s ≫ d ≫ cpow y (n - 1 - s))) ≫ y =
        c ^ s • (cpow x s ≫ d ≫ cpow y (n + 1 - 1 - s)) := by
      intro s hs
      rw [Finset.mem_range] at hs
      rw [Linear.smul_comp, Category.assoc, Category.assoc,
        show n + 1 - 1 - s = n - 1 - s + 1 by omega, cpow_succ y (n - 1 - s)]
    rw [Finset.sum_congr rfl hs]
    simp only [Nat.add_sub_cancel, Nat.sub_self, cpow_zero, Category.comp_id]
    abel

end Iter

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-! ## Dots as powers -/

/-- `n` dots on the strand `Eᵢ` between `u` and `v` are the `n`-th power of one dot. -/
theorem cl_dotsL_eq_pow (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ)
    {s : List (Letter I)} (hs : s = u ++ [up i] ++ v) :
    cl D Sc μ s s (dotsL u i v n) = cpow (cl D Sc μ s s (dotsL u i v 1)) n := by
  subst hs
  induction n with
  | zero => simp [dotsL, cl_nil]
  | succ n ih =>
    rw [cpow_succ, ← ih, cl_comp (sChain_dotsL u i v n) (sChain_dotsL u i v 1)]
    congr 1
    simp [dotsL, List.replicate_succ']

theorem cl_dotsL_append (μ : X) {s t : List (Letter I)} (u : List (Letter I)) (i : I)
    (v : List (Letter I)) (n : ℕ) (L : List (LayerData I)) (hs : s = u ++ [up i] ++ v)
    (hL : SChain s L t) :
    cl D Sc μ s t (dotsL u i v n ++ L) =
      cl D Sc μ s s (dotsL u i v n) ≫ cl D Sc μ s t L := by
  subst hs
  rw [cl_comp (sChain_dotsL u i v n) hL]

/-! ## Lemma 3.1 (3.1), (3.2) -/

variable (Sc)

/-- **Brundan–Ellis, Lemma 3.1 (3.1), `i ≠ j`.** -/
theorem lemma31_eq1_ne (i j : I) (ν : X) (hij : i ≠ j) (n : ℕ) :
    cl D Sc ν [up i, up j] [up j, up i] (dotsL [] i [up j] n ++ crossL [] i j []) =
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [] ++ dotsL [up j] i [] n) := by
  have hT : SChain [up i, up j] (crossL [] i j []) [up j, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have dL : ∀ m, SChain [up i, up j] (dotsL [] i [up j] m) [up i, up j] :=
    fun m => sChain_dotsL [] i [up j] m
  have dR : ∀ m, SChain [up j, up i] (dotsL [up j] i [] m) [up j, up i] :=
    fun m => sChain_dotsL [up j] i [] m
  have key := iter_slide (cl D Sc ν [up i, up j] [up i, up j] (dotsL [] i [up j] 1))
    (cl D Sc ν [up j, up i] [up j, up i] (dotsL [up j] i [] 1))
    (cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [])) 0
    (zsign k (D.parity i * D.parity j)) ?_ n
  · simp only [Limits.zero_comp, Limits.comp_zero, smul_zero, Finset.sum_const_zero,
      add_zero] at key
    rw [← cl_comp (dL n) hT, cl_dotsL_eq_pow (s := [up i, up j]) ν [] i [up j] n rfl, key,
      ← cl_comp hT (dR n), cl_dotsL_eq_pow (s := [up j, up i]) ν [up j] i [] n rfl, zsign_natCast_mul]
  · rw [add_zero, cl_comp (dL 1) hT, cl_comp hT (dR 1)]
    exact cl_slideL Sc i j ν hij

theorem zmod2_mul_self (a : ZMod 2) : a * a = a := by
  have hz : ∀ a : ZMod 2, a * a = a := by decide
  exact hz a

/-- **Brundan–Ellis, Lemma 3.1 (3.1), `i = j`.** The `r = n - 1 - s` dots on the left strand
come before the `s` dots on the right strand. -/
theorem lemma31_eq1_eq (i : I) (ν : X) (n : ℕ) :
    cl D Sc ν [up i, up i] [up i, up i] (dotsL [] i [up i] n ++ crossL [] i i []) -
      zsign k (D.parity i * D.parity i * n) •
        cl D Sc ν [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [up i] i [] n) =
      ∑ s ∈ Finset.range n, zsign k (D.parity i * s) •
        cl D Sc ν [up i, up i] [up i, up i]
          (dotsL [] i [up i] (n - 1 - s) ++ dotsL [up i] i [] s) := by
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have dL : ∀ m, SChain [up i, up i] (dotsL [] i [up i] m) [up i, up i] :=
    fun m => sChain_dotsL [] i [up i] m
  have dR : ∀ m, SChain [up i, up i] (dotsL [up i] i [] m) [up i, up i] :=
    fun m => sChain_dotsL [up i] i [] m
  have key := iter_slide (cl D Sc ν [up i, up i] [up i, up i] (dotsL [] i [up i] 1))
    (cl D Sc ν [up i, up i] [up i, up i] (dotsL [up i] i [] 1))
    (cl D Sc ν [up i, up i] [up i, up i] (crossL [] i i []))
    (cl D Sc ν [up i, up i] [up i, up i] []) (zsign k (D.parity i * D.parity i)) ?_ n
  · rw [← cl_comp (dL n) hT, cl_dotsL_eq_pow (s := [up i, up i]) ν [] i [up i] n rfl, key,
      ← cl_comp hT (dR n), cl_dotsL_eq_pow (s := [up i, up i]) ν [up i] i [] n rfl, zsign_natCast_mul,
      add_sub_cancel_left]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [zmod2_mul_self, ← zsign_natCast_mul, cl_nil, Category.id_comp,
      ← cl_dotsL_eq_pow (s := [up i, up i]) ν [] i [up i] _ rfl, ← cl_dotsL_eq_pow (s := [up i, up i]) ν [up i] i [] _ rfl,
      cl_comp (dL _) (dR s)]
  · rw [cl_comp (dL 1) hT, cl_comp hT (dR 1)]
    exact cl_slideLEq Sc i ν

/-- **Brundan–Ellis, Lemma 3.1 (3.2), `i ≠ j`.** -/
theorem lemma31_eq2_ne (i j : I) (ν : X) (hij : i ≠ j) (n : ℕ) :
    cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [] ++ dotsL [] j [up i] n) =
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc ν [up i, up j] [up j, up i] (dotsL [up i] j [] n ++ crossL [] i j []) := by
  have hT : SChain [up i, up j] (crossL [] i j []) [up j, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have dL : ∀ m, SChain [up j, up i] (dotsL [] j [up i] m) [up j, up i] :=
    fun m => sChain_dotsL [] j [up i] m
  have dR : ∀ m, SChain [up i, up j] (dotsL [up i] j [] m) [up i, up j] :=
    fun m => sChain_dotsL [up i] j [] m
  have key := iter_slide' (cl D Sc ν [up i, up j] [up i, up j] (dotsL [up i] j [] 1))
    (cl D Sc ν [up j, up i] [up j, up i] (dotsL [] j [up i] 1))
    (cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [])) 0
    (zsign k (D.parity i * D.parity j)) ?_ n
  · simp only [Limits.zero_comp, Limits.comp_zero, smul_zero, Finset.sum_const_zero,
      add_zero] at key
    rw [← cl_comp hT (dL n), cl_dotsL_eq_pow (s := [up j, up i]) ν [] j [up i] n rfl, key,
      ← cl_comp (dR n) hT, cl_dotsL_eq_pow (s := [up i, up j]) ν [up i] j [] n rfl, zsign_natCast_mul]
  · rw [add_zero, cl_comp hT (dL 1), cl_comp (dR 1) hT]
    exact cl_slideR Sc i j ν hij

/-- **Brundan–Ellis, Lemma 3.1 (3.2), `i = j`.** The `s` dots on the right strand come before
the `r = n - 1 - s` dots on the left strand. -/
theorem lemma31_eq2_eq (i : I) (ν : X) (n : ℕ) :
    cl D Sc ν [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [] i [up i] n) -
      zsign k (D.parity i * D.parity i * n) •
        cl D Sc ν [up i, up i] [up i, up i] (dotsL [up i] i [] n ++ crossL [] i i []) =
      ∑ s ∈ Finset.range n, zsign k (D.parity i * s) •
        cl D Sc ν [up i, up i] [up i, up i]
          (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s)) := by
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have dL : ∀ m, SChain [up i, up i] (dotsL [] i [up i] m) [up i, up i] :=
    fun m => sChain_dotsL [] i [up i] m
  have dR : ∀ m, SChain [up i, up i] (dotsL [up i] i [] m) [up i, up i] :=
    fun m => sChain_dotsL [up i] i [] m
  have key := iter_slide' (cl D Sc ν [up i, up i] [up i, up i] (dotsL [up i] i [] 1))
    (cl D Sc ν [up i, up i] [up i, up i] (dotsL [] i [up i] 1))
    (cl D Sc ν [up i, up i] [up i, up i] (crossL [] i i []))
    (cl D Sc ν [up i, up i] [up i, up i] []) (zsign k (D.parity i * D.parity i)) ?_ n
  · rw [← cl_comp hT (dL n), cl_dotsL_eq_pow (s := [up i, up i]) ν [] i [up i] n rfl, key,
      ← cl_comp (dR n) hT, cl_dotsL_eq_pow (s := [up i, up i]) ν [up i] i [] n rfl, zsign_natCast_mul,
      add_sub_cancel_left]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [zmod2_mul_self, ← zsign_natCast_mul, cl_nil, Category.id_comp,
      ← cl_dotsL_eq_pow (s := [up i, up i]) ν [up i] i [] _ rfl, ← cl_dotsL_eq_pow (s := [up i, up i]) ν [] i [up i] _ rfl,
      cl_comp (dR s) (dL _)]
  · rw [cl_comp hT (dL 1), cl_comp (dR 1) hT]
    exact cl_slideREq Sc i ν

end OddMath.SKM
