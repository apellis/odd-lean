/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPKilling

/-!
# The all-prefix QP identity

`DeformedGlobalQP.md`, §3 (the deformed form of Kang–Kashiwara–Oh, arXiv:1206.5933v2,
(8.14)–(8.17)): for every word `μ`, modulo endomorphisms of `i :: μ` that kill the
prescribed prepend target in every right context,

  `f_i(x₁) Tₙ Vₙ ≡ f_i(x₁) A_μ`,

where `A_μ` is the product over the positions `a` of `μ` of `Q_(i,μ_a)(x₁, x_(a+1))` when
`μ_a ≠ i`, of `(x_(a+1) − x₁)²` when `μ_a = i` is odd, and of `−1` when `μ_a = i` is even.

* `KillAll s Y`: `Y ⊗ 1_σ` kills on `i :: (s ++ σ)` for every right context `σ`;
* `goodAll`: the precompositions preserving `KillAll`, a subalgebra containing every
  `1_i ⊗ f` and the first dot;
* `KillAll.whiskerRight_cons`: adjoining a last spectator;
* `KillAll.of_sq_sub`, `KillAll.of_linear_even`: the two cancellations;
* `qpProduct`: the product `A_μ`;
* `killAll_qp`: the identity above.

The sign `−1` for an even repeated colour comes from the crossing convention of the
two-strand nilHecke relations used here (`EvenTwo`); with the opposite sign of the crossing
it disappears, as in the written argument.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Algebra

/-- Two elements commuting up to a scalar of square one: the square difference commutes with
the difference. -/
theorem squareDiff_mul_sub_comm {B : Type*} [Ring B] [Algebra k B] {x y : B} {c : k}
    (h : y * x = c • (x * y)) (hc : c * c = 1) :
    (y ^ 2 - x ^ 2) * (y - x) = (y - x) * (y ^ 2 - x ^ 2) := by
  have h1 : y ^ 2 * x = x * y ^ 2 := by
    rw [pow_two, mul_assoc, h, mul_smul_comm, ← mul_assoc, h, smul_mul_assoc, smul_smul, hc,
      one_smul, mul_assoc]
  have h2 : y * x ^ 2 = x ^ 2 * y := by
    rw [pow_two, ← mul_assoc, h, smul_mul_assoc, mul_assoc, h, mul_smul_comm, smul_smul, hc,
      one_smul, mul_assoc]
  rw [sub_mul, mul_sub, mul_sub, sub_mul, h1, ← h2]
  noncomm_ring

end Algebra

section Product

variable {D Sc}

theorem map_qPoly {A B : (pres D Sc).Presented} (φ : End A →ₐ[k] End B) (x y : End A)
    (j l : I) : φ (qPoly D Sc x y j l) = qPoly D Sc (φ x) (φ y) j l := by
  unfold qPoly
  split_ifs <;> simp only [map_sum, map_add, map_smul, map_mul, map_pow, map_one]

variable (D Sc) (i : I)

open Classical in
/-- The factor of `A_μ` at the position `b` of `μ`, whose letter is `x`:
`Q_(i,x)(x₁, x_(b+2))` for `x ≠ i`, `(x_(b+2) − x₁)²` for `x = i` odd and `−1` for `x = i`
even. -/
def qpFactor (μ : List I) (x : I) (b : ℕ) : End ((pres D Sc).obj (ob D (i :: μ))) :=
  if x = i then
    (if D.parity i = 1 then (dotE D Sc (i :: μ) (b + 1) - dotE D Sc (i :: μ) 0) ^ 2 else -1)
  else qPoly D Sc (dotE D Sc (i :: μ) 0) (dotE D Sc (i :: μ) (b + 1)) i x

/-- The product `A_μ` of the factors over the positions of `μ`. -/
def qpProduct (μ : List I) : End ((pres D Sc).obj (ob D (i :: μ))) :=
  ((List.range μ.length).map fun b => qpFactor D Sc i μ (μ.getD b i) b).prod

theorem qpFactor_whiskerRight (μ s : List I) (x : I) {b : ℕ} (hb : b < μ.length) :
    whiskerWordAlgHom D Sc (i :: μ) s (qpFactor D Sc i μ x b) =
      qpFactor D Sc i (μ ++ s) x b := by
  have h0 : whiskerWordAlgHom D Sc (i :: μ) s (dotE D Sc (i :: μ) 0) =
      dotE D Sc (i :: (μ ++ s)) 0 :=
    dotE_whiskerRight D Sc (i :: μ) s 0 (by simp)
  have h1 : whiskerWordAlgHom D Sc (i :: μ) s (dotE D Sc (i :: μ) (b + 1)) =
      dotE D Sc (i :: (μ ++ s)) (b + 1) :=
    dotE_whiskerRight D Sc (i :: μ) s (b + 1) (by simp; omega)
  unfold qpFactor
  split_ifs <;> simp only [map_pow, map_sub, map_neg, map_one, map_qPoly, h0, h1]

theorem qpProduct_append (μ : List I) (x : I) :
    qpProduct D Sc i (μ ++ [x]) =
      @id (End ((pres D Sc).obj (ob D (i :: (μ ++ [x])))))
          (whiskerWordAlgHom D Sc (i :: μ) [x] (qpProduct D Sc i μ)) *
        qpFactor D Sc i (μ ++ [x]) x μ.length := by
  unfold qpProduct
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.prod_append, map_list_prod, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left fun b hb => ?_
    rw [List.mem_range] at hb
    simp only [Function.comp_apply]
    rw [qpFactor_whiskerRight D Sc i μ [x] _ hb, List.getD_append _ _ _ _ hb]
  · simp

theorem dotE_last_mul_first (μ : List I) :
    dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) * dotE D Sc (i :: (μ ++ [i])) 0 =
      SKM.zsign k (D.parity i * D.parity i) •
        (dotE D Sc (i :: (μ ++ [i])) 0 * dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) :=
  genE_interchange D Sc [] μ [] (.dot i) (.dot i) rfl rfl (by simp [Shape.dom]) rfl
    (by simp [Shape.dom])

end Product

variable [Fintype I] (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

section Context

/-- `Y` kills on `i :: (s ++ σ)` after right whiskering by every right context `σ`. -/
def KillAll (s : List I) (Y : End ((pres D Sc).obj (ob D (i :: s)))) : Prop :=
  ∀ (σ : List I) (h : (s ++ σ).length = n + 1),
    KillE D Sc i β a ha n ⟨s ++ σ, h⟩
      (Y ▷ (pres D Sc).obj (ob D σ) : End ((pres D Sc).obj (ob D (i :: (s ++ σ)))))

variable {D Sc i β a ha n} {s : List I}

/- The combinators below take morphisms `i :: s ⟶ i :: s`, so that sums and composites
are formed in the morphism groups. -/

theorem KillAll.add {Y Z : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (hZ : KillAll D Sc i β a ha n s Z) :
    KillAll D Sc i β a ha n s (Y + Z) := fun σ h => by
  rw [MonoidalSupercategory.add_whiskerRight (R := k)]
  exact (hY σ h).add (hZ σ h)

theorem KillAll.neg {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) : KillAll D Sc i β a ha n s (-Y) := fun σ h => by
  rw [MonoidalSupercategory.neg_whiskerRight (R := k)]
  exact (hY σ h).neg

theorem KillAll.sub {Y Z : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (hZ : KillAll D Sc i β a ha n s Z) :
    KillAll D Sc i β a ha n s (Y - Z) := by
  rw [sub_eq_add_neg]
  exact hY.add hZ.neg

theorem KillAll.smul {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (c : k) :
    KillAll D Sc i β a ha n s (c • Y) := fun σ h => by
  rw [MonoidalSupercategory.smul_whiskerRight (R := k)]
  exact (hY σ h).smul c

theorem KillAll.zero : KillAll D Sc i β a ha n s (0 : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))) := fun σ h => by
  rw [MonoidalSupercategory.zero_whiskerRight (R := k)]
  exact killE_zero (w := ⟨s ++ σ, h⟩)

theorem KillAll.of_eq {Y Z : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (h : Y = Z) : KillAll D Sc i β a ha n s Z := h ▸ hY

end Context

section Equation

end Equation

end OddMath.QuiverHecke
