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

theorem qPoly_mem {A : (pres D Sc).Presented} (S : Subalgebra k (End A)) {x y : End A}
    (hx : x ∈ S) (hy : y ∈ S) (j l : I) : qPoly D Sc x y j l ∈ S := by
  unfold qPoly
  split_ifs
  · exact S.smul_mem S.one_mem _
  · exact S.add_mem (S.sum_mem fun p _ => S.sum_mem fun q _ =>
      S.smul_mem (S.mul_mem (S.pow_mem hx _) (S.pow_mem hy _)) _)
      (S.add_mem (S.smul_mem (S.pow_mem hx _) _) (S.smul_mem (S.pow_mem hy _) _))

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

/-- Even linear cancellation at the morphism level: for `p(i) = 0` a factor
`1_i ⊗ c − x₁` can be removed. -/
theorem KillE.of_linear_even (hp : D.parity i = 0) {w : Word I (n + 1)}
    (c : End (wordObj D Sc w)) {Y : End (wordObj D Sc (prependWord i w))}
    (h : KillE D Sc i β a ha n w
      (((show End ((pres D Sc).obj (ob D (i :: w.1))) from
        (pres D Sc).obj (ob D [i]) ◁ c) - dotE D Sc (i :: w.1) 0) ≫ Y)) :
    KillE D Sc i β a ha n w Y := by
  unfold KillE at h ⊢
  rw [← End.mul_def, map_mul, map_sub, cornerMap_whiskerLeft, cornerMap_dotZero] at h
  refine PrependKills.of_linear_even hp (FiniteHomMatrix.cornerMap w c) (h.of_eq ?_)
  set e := cornerUnit D Sc i w
  set f := affineFirstDot D Sc i (n + 1)
  have hz := cornerMap_mul_cornerUnit (D := D) (Sc := Sc) (i := i) Y
  have hef : e * f = f * e := cornerUnit_comm_firstDot
  rw [mul_sub, mul_sub]
  congr 1
  rw [← hef, ← mul_assoc, hz]

/-- Transport of killing along an equality of words. -/
theorem KillE.congr_word {w w' : Word I (n + 1)} (e : w.1 = w'.1)
    {Y : End ((pres D Sc).obj (ob D (i :: w.1)))} (hY : KillE D Sc i β a ha n w Y) :
    KillE D Sc i β a ha n w'
      (eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e.symm) ≫ Y ≫
        eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e)) := by
  obtain ⟨l, hl⟩ := w
  obtain ⟨l', hl'⟩ := w'
  dsimp only at e
  subst e
  simpa using hY

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

variable (D Sc i β a ha n s) in
/-- The precompositions preserving `KillAll`. -/
def goodAll : Subalgebra k (End ((pres D Sc).obj (ob D (i :: s)))) where
  carrier := {g | ∀ (σ : List I) (h : (s ++ σ).length = n + 1),
    GoodE D Sc i β a ha n ⟨s ++ σ, h⟩ (g ▷ (pres D Sc).obj (ob D σ))}
  mul_mem' {g g'} hg hg' σ h := by
    change GoodE D Sc i β a ha n ⟨s ++ σ, h⟩ (whiskerWordAlgHom D Sc (i :: s) σ (g * g'))
    rw [map_mul]
    exact (goodSubalgebra D Sc i β a ha n ⟨s ++ σ, h⟩).mul_mem (hg σ h) (hg' σ h)
  add_mem' {g g'} hg hg' σ h := by
    change GoodE D Sc i β a ha n ⟨s ++ σ, h⟩ (whiskerWordAlgHom D Sc (i :: s) σ (g + g'))
    rw [map_add]
    exact (goodSubalgebra D Sc i β a ha n ⟨s ++ σ, h⟩).add_mem (hg σ h) (hg' σ h)
  algebraMap_mem' c σ h := by
    change GoodE D Sc i β a ha n ⟨s ++ σ, h⟩ (whiskerWordAlgHom D Sc (i :: s) σ (algebraMap k _ c))
    rw [AlgHom.commutes]
    exact (goodSubalgebra D Sc i β a ha n ⟨s ++ σ, h⟩).algebraMap_mem c

theorem KillAll.good_comp {g : End ((pres D Sc).obj (ob D (i :: s)))} {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hg : g ∈ goodAll D Sc i β a ha n s) (hY : KillAll D Sc i β a ha n s Y) :
    KillAll D Sc i β a ha n s (g ≫ Y) := fun σ h => by
  rw [MonoidalSupercategory.comp_whiskerRight (R := k)]
  exact hg σ h _ (hY σ h)

theorem whiskerLeft_mem_goodAll (f : End ((pres D Sc).obj (ob D s))) :
    ((pres D Sc).obj (ob D [i]) ◁ f : End ((pres D Sc).obj (ob D (i :: s)))) ∈
      goodAll D Sc i β a ha n s := fun σ h => by
  rw [whiskerLeft_whiskerRight_cons]
  exact goodE_whiskerLeft (w := ⟨s ++ σ, h⟩) (f ▷ (pres D Sc).obj (ob D σ))

theorem dotE_zero_mem_goodAll : dotE D Sc (i :: s) 0 ∈ goodAll D Sc i β a ha n s :=
  fun σ h => by
    rw [dotE_whiskerRight D Sc (i :: s) σ 0 (by simp)]
    exact goodE_dotZero (w := ⟨s ++ σ, h⟩)

theorem dotE_succ_mem_goodAll (b : ℕ) : dotE D Sc (i :: s) (b + 1) ∈ goodAll D Sc i β a ha n s := by
  rw [← whiskerLeft_dotE_cons]
  exact whiskerLeft_mem_goodAll _

/-- Adjoining a last spectator. -/
theorem KillAll.whiskerRight_cons {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))} (x : I)
    (hY : KillAll D Sc i β a ha n s Y) :
    KillAll D Sc i β a ha n (s ++ [x])
      (Y ▷ (pres D Sc).obj (ob D [x]) : End ((pres D Sc).obj (ob D (i :: (s ++ [x]))))) :=
  fun σ h => by
    have h' : (s ++ (x :: σ)).length = n + 1 := by simpa using h
    have e : (⟨s ++ (x :: σ), h'⟩ : Word I (n + 1)).1 = (⟨s ++ [x] ++ σ, h⟩ : Word I (n + 1)).1 :=
      by simp
    have := KillE.congr_word D Sc i β a ha n e (hY (x :: σ) h')
    rw [whiskerRight_whiskerRight_word]
    exact this

theorem KillAll.of_sq_sub (c : End ((pres D Sc).obj (ob D s)))
    {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (h : KillAll D Sc i β a ha n s
      ((dotE D Sc (i :: s) 0 ^ 2 - (show End ((pres D Sc).obj (ob D (i :: s))) from
        (pres D Sc).obj (ob D [i]) ◁ c)) ≫ Y)) :
    KillAll D Sc i β a ha n s Y := fun σ hσ => by
  refine KillE.of_sq_sub (w := ⟨s ++ σ, hσ⟩) (c ▷ (pres D Sc).obj (ob D σ)) ?_
  have := h σ hσ
  rw [MonoidalSupercategory.comp_whiskerRight (R := k), ← whiskerWordAlgHom_apply D Sc
    (i :: s) σ (_ - _), map_sub, map_pow, whiskerWordAlgHom_apply, whiskerWordAlgHom_apply,
    dotE_whiskerRight D Sc (i :: s) σ 0 (by simp), whiskerLeft_whiskerRight_cons] at this
  exact this

theorem KillAll.of_linear_even (hp : D.parity i = 0) (c : End ((pres D Sc).obj (ob D s)))
    {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (h : KillAll D Sc i β a ha n s
      (((show End ((pres D Sc).obj (ob D (i :: s))) from
        (pres D Sc).obj (ob D [i]) ◁ c) - dotE D Sc (i :: s) 0) ≫ Y)) :
    KillAll D Sc i β a ha n s Y := fun σ hσ => by
  refine KillE.of_linear_even D Sc i β a ha n hp (w := ⟨s ++ σ, hσ⟩) (c ▷ (pres D Sc).obj (ob D σ)) ?_
  have := h σ hσ
  rw [MonoidalSupercategory.comp_whiskerRight (R := k), ← whiskerWordAlgHom_apply D Sc
    (i :: s) σ (_ - _), map_sub, whiskerWordAlgHom_apply, whiskerWordAlgHom_apply,
    dotE_whiskerRight D Sc (i :: s) σ 0 (by simp), whiskerLeft_whiskerRight_cons] at this
  exact this

end Context

section Equation

/-- The statement of `DeformedGlobalQP.md` (3) for the word `μ`:
`f_i(x₁) (Tₙ Vₙ − A_μ)` kills in every right context. -/
def QPIdentity (μ : List I) : Prop :=
  KillAll D Sc i β a ha n μ
    (((moveHom D Sc i [] μ ≫ lastToFirstHom D Sc i μ :
          (pres D Sc).obj (ob D (i :: μ)) ⟶ (pres D Sc).obj (ob D (i :: μ))) ≫
        _root_.Polynomial.aeval (dotE D Sc (i :: μ) 0) (a i)) -
      qpProduct D Sc i μ ≫ _root_.Polynomial.aeval (dotE D Sc (i :: μ) 0) (a i))

theorem qpIdentity_nil : QPIdentity D Sc i β a ha n [] := by
  refine KillAll.zero.of_eq ?_
  simp [moveHom, lastToFirstHom, qpProduct, End.one_def]

/-- Distinct letters: `Tₙ₊₁Vₙ₊₁ − A = Q_(i,x)(x₁, x_(n+2)) ((TₙVₙ − A_μ) ⊗ 1_x)`. -/
theorem qpIdentity_append_ne (μ : List I) {x : I} (hx : x ≠ i)
    (ih : QPIdentity D Sc i β a ha n μ) : QPIdentity D Sc i β a ha n (μ ++ [x]) := by
  have hq := qPoly_mem (goodAll D Sc i β a ha n (μ ++ [x])) dotE_zero_mem_goodAll
    (dotE_succ_mem_goodAll μ.length) i x
  refine (KillAll.good_comp hq (ih.whiskerRight_cons x)).of_eq ?_
  rw [moveHom_lastToFirstHom_append_ne D Sc (Ne.symm hx) μ, qpProduct_append, End.mul_def,
    qpFactor, ite_eq_right_of_eq_false _ _ (eq_false hx)]
  simp only [sub_eq_add_neg, MonoidalSupercategory.add_whiskerRight (R := k),
    MonoidalSupercategory.neg_whiskerRight (R := k),
    MonoidalSupercategory.comp_whiskerRight (R := k),
    aeval_dotE_whiskerRight D Sc (i :: μ) [x] (by simp), Preadditive.comp_add, Preadditive.comp_neg, Category.assoc, whiskerWordAlgHom_apply, id_eq]
  rfl

/-- (K) as a `KillAll` statement on `μ ++ [i]`. -/
theorem killAll_relation (μ : List I) :
    KillAll D Sc i β a ha n (μ ++ [i])
      ((moveHom D Sc i [] (μ ++ [i]) ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ≫ _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i)) := fun σ h => by
  rw [MonoidalSupercategory.comp_whiskerRight (R := k),
    aeval_dotE_whiskerRight D Sc _ σ (by simp)]
  exact killE_relation_context D Sc i β a ha n μ σ h

/-- The induction hypothesis on `μ`, right whiskered by `1_i`. -/
theorem qpIdentity_whiskerRight_self (μ : List I) (ih : QPIdentity D Sc i β a ha n μ) :
    KillAll D Sc i β a ha n (μ ++ [i]) ((moveWhisker D Sc i μ ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i])) ≫ _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i)) - (@id (End ((pres D Sc).obj (ob D (i :: (μ ++ [i]))))) (qpProduct D Sc i μ ▷ (pres D Sc).obj (ob D [i])) ≫ _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i))) := by
  refine (ih.whiskerRight_cons i).of_eq ?_
  simp only [sub_eq_add_neg, MonoidalSupercategory.add_whiskerRight (R := k),
    MonoidalSupercategory.neg_whiskerRight (R := k),
    MonoidalSupercategory.comp_whiskerRight (R := k),
    aeval_dotE_whiskerRight D Sc (i :: μ) [i] (by simp), Category.assoc]
  rfl

omit [Fintype I] in
theorem sub_sq_sub_eq_neg_squareDiff (μ : List I) :
    (dotE D Sc (i :: (μ ++ [i])) 0 ^ 2 - (show End ((pres D Sc).obj (ob D (i :: (μ ++ [i])))) from dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) ≫ dotE D Sc (i :: (μ ++ [i])) (μ.length + 1))) = -OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (μ ++ [i])) 0) (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) := by
  rw [OddNilHecke.Intertwiner.squareDiff, neg_sub]
  congr 1
  rw [pow_two, End.mul_def]

/-- Odd repeated letter. -/
theorem qpIdentity_append_odd (hp : D.parity i = 1) (μ : List I)
    (ih : QPIdentity D Sc i β a ha n μ) : QPIdentity D Sc i β a ha n (μ ++ [i]) := by
  have hE : (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) - dotE D Sc (i :: (μ ++ [i])) 0) ∈ goodAll D Sc i β a ha n (μ ++ [i]) :=
    Subalgebra.sub_mem _ (dotE_succ_mem_goodAll μ.length) dotE_zero_mem_goodAll
  have hDE : OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (μ ++ [i])) 0) (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) * (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) - dotE D Sc (i :: (μ ++ [i])) 0) = (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) - dotE D Sc (i :: (μ ++ [i])) 0) * OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (μ ++ [i])) 0) (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) :=
    squareDiff_mul_sub_comm (dotE_last_mul_first D Sc i μ) (zsign_mul_self _)
  have hED : ∀ {T : (pres D Sc).Presented} (Z : (pres D Sc).obj (ob D (i :: (μ ++ [i]))) ⟶ T),
      (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) - dotE D Sc (i :: (μ ++ [i])) 0) ≫ OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (μ ++ [i])) 0) (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) ≫ Z = OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (μ ++ [i])) 0) (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) ≫ (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) - dotE D Sc (i :: (μ ++ [i])) 0) ≫ Z := fun Z => by
    rw [← Category.assoc, ← Category.assoc, ← End.mul_def, ← End.mul_def, hDE]
  have hS : -SKM.zsign k (D.parity i * wordSumParity D μ) * SKM.zsign k (D.parity i * wordSumParity D μ) = -1 := by rw [neg_mul, zsign_mul_self]
  have hKc := KillAll.of_sq_sub
    (dotE D Sc (μ ++ [i]) μ.length ≫ dotE D Sc (μ ++ [i]) μ.length)
    ((killAll_relation D Sc i β a ha n μ).neg.of_eq (Z :=
      (dotE D Sc (i :: (μ ++ [i])) 0 ^ 2 - (show End ((pres D Sc).obj (ob D (i :: (μ ++ [i])))) from (pres D Sc).obj (ob D [i]) ◁
        (dotE D Sc (μ ++ [i]) μ.length ≫ dotE D Sc (μ ++ [i]) μ.length))) ≫
        (SKM.zsign k (D.parity i * wordSumParity D μ) • ((dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) - dotE D Sc (i :: (μ ++ [i])) 0) ≫ (moveWhisker D Sc i μ ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i])) ≫ _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i))) - OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (μ ++ [i])) 0) (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) ≫ (moveWhisker D Sc i μ ≫ crossE D Sc (μ ++ [i] ++ [i]) μ.length ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i])) ≫ _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i)))) (by
      rw [MonoidalSupercategory.whiskerLeft_comp (R := k), whiskerLeft_dotE_cons,
        sub_sq_sub_eq_neg_squareDiff, Preadditive.neg_comp, moveHom_append_self,
        moveWhisker_comp_sameIntertwiner_odd D Sc i hp μ]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul, Category.assoc]))
  refine (((KillAll.good_comp hE hKc).smul (-SKM.zsign k (D.parity i * wordSumParity D μ))).add (KillAll.good_comp hE
    (KillAll.good_comp hE (qpIdentity_whiskerRight_self D Sc i β a ha n μ ih)))).of_eq ?_
  rw [moveHom_lastToFirstHom_append_self_odd D Sc i hp μ, lastToFirstHom_append_self,
    qpProduct_append, End.mul_def, qpFactor, ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true hp), pow_two, End.mul_def]
  simp only [Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul, Category.assoc, whiskerWordAlgHom_apply, smul_sub, smul_smul, hS, one_smul, neg_smul, hED]
  abel

/-- Even repeated letter. -/
theorem qpIdentity_append_even (hp : D.parity i = 0) (μ : List I)
    (ih : QPIdentity D Sc i β a ha n μ) : QPIdentity D Sc i β a ha n (μ ++ [i]) := by
  have hp' : ¬D.parity i = 1 := by rw [hp]; decide
  have hKc := KillAll.of_linear_even hp (dotE D Sc (μ ++ [i]) μ.length)
    ((killAll_relation D Sc i β a ha n μ).of_eq (Z :=
      ((show End ((pres D Sc).obj (ob D (i :: (μ ++ [i])))) from (pres D Sc).obj (ob D [i]) ◁ dotE D Sc (μ ++ [i]) μ.length) -
          dotE D Sc (i :: (μ ++ [i])) 0) ≫ ((moveWhisker D Sc i μ ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i])) ≫ _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i)) + (dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) - dotE D Sc (i :: (μ ++ [i])) 0) ≫ (moveWhisker D Sc i μ ≫ crossE D Sc (μ ++ [i] ++ [i]) μ.length ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i])) ≫ _root_.Polynomial.aeval (dotE D Sc (i :: (μ ++ [i])) 0) (a i)))) (by
      rw [whiskerLeft_dotE_cons, moveHom_append_self,
        moveWhisker_comp_sameIntertwiner_even D Sc i hp μ]
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]))
  refine (hKc.sub (qpIdentity_whiskerRight_self D Sc i β a ha n μ ih)).of_eq ?_
  rw [moveHom_lastToFirstHom_append_self_even D Sc i hp μ, lastToFirstHom_append_self,
    qpProduct_append, qpFactor, ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_right_of_eq_false _ _ (eq_false hp'), mul_neg_one, Preadditive.neg_comp]
  simp only [Category.assoc, whiskerWordAlgHom_apply]
  abel

/-- `DeformedGlobalQP.md` (3): `f_i(x₁) Tₙ Vₙ ≡ f_i(x₁) A_μ` modulo endomorphisms killing in
every right context, for every word `μ`. -/
theorem qpIdentity (μ : List I) : QPIdentity D Sc i β a ha n μ := by
  induction μ using List.reverseRecOn with
  | nil => exact qpIdentity_nil D Sc i β a ha n
  | append_singleton μ x ih =>
    by_cases hx : x = i
    · subst hx
      rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (D.parity x) with hp | hp
      · exact qpIdentity_append_even D Sc _ β a ha n hp μ ih
      · exact qpIdentity_append_odd D Sc _ β a ha n hp μ ih
    · exact qpIdentity_append_ne D Sc i β a ha n μ hx ih

end Equation

end OddMath.QuiverHecke
