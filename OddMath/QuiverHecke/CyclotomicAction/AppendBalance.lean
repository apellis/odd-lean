/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerNaturality
import OddMath.QuiverHecke.CyclotomicAction.LastToFirstSnoc
import OddMath.QuiverHecke.CyclotomicAction.Parity
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerMeet
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPDistinct

/-!
# Balance of the append Mackey map `P`

`docs/Nondegeneracy/AppendMackeySource.md` (the old-generator balance of
`DeformedGlobalQP.md`, §4, mirror form of Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1). For an old word `s` and the moving colour `i`, `W_s = T_s ≫ f_i(x₁)` takes the last
strand of `s ++ [i]` to the front and applies the cyclotomic polynomial of `i` to it. For an old
morphism `g : s ⟶ t` the error

  `E(g) = (g ▷ i) ≫ W_t - W_s ≫ (i ◁ tw_(q_s) g)`

lies in the span of the morphisms `(y ▷ i) ≫ h` with `y` in the old cyclotomic ideal.

## Main results

* `whiskerLeft_comp_whiskerRight_twist`: super interchange for an arbitrary morphism;
* `crossLast_comp_whiskerRight`: a crossing of the last two strands passes a whiskered morphism;
* `appendError_mem_appendKill`: the balance of `P`, for every morphism `g`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open SKM (zsign)

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

set_option quotPrecheck false in
local notation "O[" l "]" => (pres D Sc).obj (ob D l)

section Interchange

/-- Super interchange for an arbitrary (possibly inhomogeneous) morphism `y`: passing a
homogeneous `c` of parity `q` twists `y` by `q`. -/
theorem whiskerLeft_comp_whiskerRight_twist {A A' B B' : (pres D Sc).Presented} {q : ZMod 2}
    {c : B ⟶ B'} (hc : c ∈ Supercategory.parity (R := k) B B' q) (y : A ⟶ A') :
    A ◁ c ≫ y ▷ B' = Supercategory.twist k q y ▷ B ≫ A' ◁ c := by
  refine Supercategory.induction_on (R := k) y ?_ (fun p g hg => ?_) (fun g h hg hh => ?_)
  · rw [map_zero, MonoidalSupercategory.zero_whiskerRight (R := k),
      MonoidalSupercategory.zero_whiskerRight (R := k), Limits.comp_zero, Limits.zero_comp]
  · rw [Supercategory.twist_of_mem q hg, MonoidalSupercategory.smul_whiskerRight (R := k),
      Linear.smul_comp, MonoidalSupercategory.super_interchange (R := k) hg hc,
      Supercategory.koszulSign_smul (R := k), smul_smul, mul_comm q p,
      Supercategory.sign_mul_self, one_smul]
  · rw [map_add, MonoidalSupercategory.add_whiskerRight (R := k),
      MonoidalSupercategory.add_whiskerRight (R := k), Preadditive.comp_add,
      Preadditive.add_comp, hg, hh]

/-- The parity twist commutes with left whiskering. -/
theorem twist_whiskerLeft_obj (p : ZMod 2) {A B : (pres D Sc).Presented} (Z : (pres D Sc).Presented)
    (f : A ⟶ B) :
    Supercategory.twist k p (Z ◁ f) = Z ◁ Supercategory.twist k p f := by
  refine Supercategory.induction_on (R := k) f ?_ (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [map_zero, MonoidalSupercategory.whiskerLeft_zero (R := k), map_zero]
  · rw [Supercategory.twist_of_mem p hg,
      Supercategory.twist_of_mem p (MonoidalSupercategory.whiskerLeft_mem (R := k) Z hg),
      MonoidalSupercategory.whiskerLeft_smul (R := k)]
  · rw [MonoidalSupercategory.whiskerLeft_add (R := k), map_add, map_add, hg, hh,
      MonoidalSupercategory.whiskerLeft_add (R := k)]

theorem sign_eq_zsign (p : ZMod 2) : Supercategory.sign k p = zsign k p := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) p with rfl | rfl <;>
    simp [Supercategory.sign, zsign]

end Interchange

section Whisker

/-- The parity twist commutes with right whiskering. -/
theorem twist_whiskerRight_obj' (p : ZMod 2) {A B : (pres D Sc).Presented} (f : A ⟶ B)
    (Z : (pres D Sc).Presented) :
    Supercategory.twist k p (f ▷ Z) = Supercategory.twist k p f ▷ Z := by
  refine Supercategory.induction_on (R := k) f ?_ (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [map_zero, MonoidalSupercategory.zero_whiskerRight k Z, map_zero]
  · rw [Supercategory.twist_of_mem p hg,
      Supercategory.twist_of_mem p (MonoidalSupercategory.whiskerRight_mem (R := k) Z hg),
      MonoidalSupercategory.smul_whiskerRight (R := k)]
  · rw [MonoidalSupercategory.add_whiskerRight (R := k), map_add, map_add, hg, hh,
      MonoidalSupercategory.add_whiskerRight (R := k)]

/-- Right whiskering of a left whiskering by a letter, on words. -/
theorem whiskerLeft_whiskerRight_letter (i : I) {t t' : List I} (g : O[t] ⟶ O[t'])
    (σ : List I) :
    ((pres D Sc).obj (ob D [i]) ◁ g) ▷ O[σ] =
      ((pres D Sc).obj (ob D [i]) ◁ (g ▷ O[σ]) : O[i :: (t ++ σ)] ⟶ O[i :: (t' ++ σ)]) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [i]))) g (𝟙 O[σ])
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  simpa using h

/-- Right whiskering by two words is right whiskering by their concatenation. -/
theorem whiskerRight_whiskerRight_list {w w' : List I} (f : O[w] ⟶ O[w']) (s t : List I) :
    (f ▷ O[s]) ▷ O[t] =
      eqToHom (congrArg (fun x => O[x]) (List.append_assoc w s t)) ≫
        (f ▷ O[s ++ t]) ≫ eqToHom (congrArg (fun x => O[x]) (List.append_assoc w' s t).symm) := by
  have h := MonoidalSupercategory.associator_naturality (R := k) f (𝟙 O[s]) (𝟙 O[t])
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  rw [comp_eqToHom_iff] at h
  rw [h, Category.assoc]
  rfl

/-- Right whiskering by a word, as a homomorphism of `k`-algebras. -/
def whiskerListAlgHom (w s : List I) : End O[w] →ₐ[k] End O[w ++ s] where
  __ := whiskerWordRingHom D Sc w s
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change (c • 𝟙 _) ▷ _ = c • 𝟙 _
    rw [MonoidalSupercategory.smul_whiskerRight (R := k),
      MonoidalSupercategory.id_whiskerRight (R := k)]
    rfl

@[simp] theorem whiskerListAlgHom_apply (w s : List I) (f : End O[w]) :
    whiskerListAlgHom D Sc w s f = f ▷ O[s] := rfl

/-- A polynomial in the first dot keeps its meaning after right whiskering. -/
theorem aeval_firstDot_whiskerRight (w s : List I) (hw : 0 < w.length)
    (q : _root_.Polynomial k) :
    _root_.Polynomial.aeval (dotE D Sc w 0) q ▷ O[s] =
      _root_.Polynomial.aeval (dotE D Sc (w ++ s) 0) q := by
  rw [← whiskerListAlgHom_apply, ← _root_.Polynomial.aeval_algHom_apply,
    whiskerListAlgHom_apply, dotE_whiskerRight D Sc w s 0 hw]

/-- Words related by a positioned word have the same letters. -/
theorem wordSumParity_tgt (t : List I) (gs : List PG) :
    wordSumParity D (tgt t gs) = wordSumParity D t := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    change wordSumParity D (tgt (g.act t) gs) = _
    rw [ih]
    cases g with
    | dot p => rfl
    | cross a =>
      simp only [PG.act]
      split
      · next x y r h =>
        conv_rhs => rw [← List.take_append_drop a t, h]
        simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append,
          List.sum_cons]
        abel
      · rfl

end Whisker

section Defs
variable (a : I → _root_.Polynomial k) (i : I)

/-- The right whiskering by a fixed object, as a `k`-linear map. -/
def whiskerRightLin {A B : (pres D Sc).Presented} (Z : (pres D Sc).Presented) :
    (A ⟶ B) →ₗ[k] (A ⊗ Z ⟶ B ⊗ Z) where
  toFun f := f ▷ Z
  map_add' f g := MonoidalSupercategory.add_whiskerRight (R := k) f g Z
  map_smul' c f := MonoidalSupercategory.smul_whiskerRight (R := k) c f Z

/-- The left whiskering by a fixed object, as a `k`-linear map. -/
def whiskerLeftLin {A B : (pres D Sc).Presented} (Z : (pres D Sc).Presented) :
    (A ⟶ B) →ₗ[k] (Z ⊗ A ⟶ Z ⊗ B) where
  toFun f := Z ◁ f
  map_add' f g := MonoidalSupercategory.whiskerLeft_add (R := k) Z f g
  map_smul' c f := MonoidalSupercategory.whiskerLeft_smul (R := k) Z c f

theorem sub_whiskerRight' {A B : (pres D Sc).Presented} (f g : A ⟶ B)
    (Z : (pres D Sc).Presented) : (f - g) ▷ Z = f ▷ Z - g ▷ Z :=
  map_sub (whiskerRightLin D Sc Z) f g

/-- The first-dot polynomial `f_j(x₁)` on the word `j :: w`. -/
def firstDotPoly (j : I) (w : List I) : O[j :: w] ⟶ O[j :: w] :=
  _root_.Polynomial.aeval (dotE D Sc (j :: w) 0) (a j)

/-- The old cyclotomic ideal, as spaces of morphisms: the span of the morphisms
`p ≫ f_j(x₁) ≫ q`. -/
def cycHom (s u : List I) : Submodule k (O[s] ⟶ O[u]) :=
  Submodule.span k {f | ∃ (j : I) (w : List I) (p : O[s] ⟶ O[j :: w]) (q : O[j :: w] ⟶ O[u]),
    f = p ≫ firstDotPoly D Sc a j w ≫ q}

/-- The morphisms killed in the induced module: the span of `(y ▷ i) ≫ h` with `y` in the old
cyclotomic ideal. -/
def appendKill (s t : List I) : Submodule k (O[s ++ [i]] ⟶ O[i :: t]) :=
  Submodule.span k {f | ∃ (u : List I) (y : O[s] ⟶ O[u]) (h : O[u ++ [i]] ⟶ O[i :: t]),
    y ∈ cycHom D Sc a s u ∧ f = (y ▷ O[[i]]) ≫ h}

/-- The crossing of the last two strands of `s ++ [x] ++ [z]`. -/
def crossLast (s : List I) (x z : I) : O[s ++ [x] ++ [z]] ⟶ O[s ++ [z] ++ [x]] :=
  cl D Sc (s ++ [x] ++ [z]) (s ++ [z] ++ [x]) [.cross s.length]
    (by simpa using sChain_crossAt s [] x z)

/-- `W_s = T_s ≫ f_i(x₁)`: the last strand moved to the front, then the cyclotomic polynomial of
`i` on it. -/
def appendW (ν : List I) : O[ν ++ [i]] ⟶ O[i :: ν] :=
  lastToFirstHom D Sc i ν ≫ firstDotPoly D Sc a i ν

/-- The parity of `W_ν`. -/
def appendQ (ν : List I) : ZMod 2 :=
  (a i).natDegree • D.parity i + D.parity i * wordSumParity D ν

/-- The balance error `E(g) = (g ▷ i) ≫ W_t - W_s ≫ (i ◁ tw_(q_s) g)`. -/
def appendError (s t : List I) : (O[s] ⟶ O[t]) →ₗ[k] (O[s ++ [i]] ⟶ O[i :: t]) where
  toFun g := ((g ▷ O[[i]]) ≫ appendW D Sc a i t : O[s ++ [i]] ⟶ O[i :: t]) -
    (appendW D Sc a i s ≫ (O[[i]] ◁ Supercategory.twist k (appendQ D a i s) g) :
      O[s ++ [i]] ⟶ O[i :: t])
  map_add' f g := by
    simp only [map_add, MonoidalSupercategory.add_whiskerRight (R := k),
      MonoidalSupercategory.whiskerLeft_add (R := k), Preadditive.add_comp,
      Preadditive.comp_add]
    abel
  map_smul' c f := by
    simp only [map_smul, MonoidalSupercategory.smul_whiskerRight (R := k),
      MonoidalSupercategory.whiskerLeft_smul (R := k), Linear.smul_comp, Linear.comp_smul,
      RingHom.id_apply, smul_sub]

theorem appendError_apply {s t : List I} (g : O[s] ⟶ O[t]) :
    appendError D Sc a i s t g =
      ((g ▷ O[[i]]) ≫ appendW D Sc a i t : O[s ++ [i]] ⟶ O[i :: t]) -
        (appendW D Sc a i s ≫ (O[[i]] ◁ Supercategory.twist k (appendQ D a i s) g) :
          O[s ++ [i]] ⟶ O[i :: t]) := rfl

end Defs

section Basic
variable {a : I → _root_.Polynomial k} {i : I}

theorem appendQ_append (ν : List I) (x : I) :
    appendQ D a i (ν ++ [x]) = appendQ D a i ν + D.parity i * D.parity x := by
  simp only [appendQ, wordSumParity, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  ring

/-- Peeling the last letter: `W_(ν ++ [x]) = σ ≫ (W_ν ▷ x)`. -/
theorem appendW_append (ν : List I) (x : I) :
    appendW D Sc a i (ν ++ [x]) = crossLast D Sc ν x i ≫ (appendW D Sc a i ν ▷ O[[x]]) := by
  rw [appendW, appendW, lastToFirstHom_append_singleton, MonoidalSupercategory.comp_whiskerRight
    (R := k), Category.assoc, firstDotPoly, firstDotPoly,
    aeval_firstDot_whiskerRight D Sc (i :: ν) [x] (by simp)]
  rfl

theorem lastToFirstHom_mem (ν : List I) :
    lastToFirstHom D Sc i ν ∈ Supercategory.parity (R := k) _ _
      (D.parity i * wordSumParity D ν) := by
  induction ν with
  | nil =>
    simpa [lastToFirstHom, wordSumParity] using Supercategory.id_mem (R := k) _
  | cons j ν ih =>
    have hc := cl_mem_chainParity D Sc (k := k) (t := j :: i :: ν) (t' := i :: j :: ν)
      [.cross 0] (by simpa using sChain_crossAt [] ν j i)
      (by intro g hg; simp at hg; subst hg; simp [PG.pos, PG.width])
    have h := Supercategory.comp_mem (MonoidalSupercategory.whiskerLeft_mem (R := k)
      ((pres D Sc).obj (ob D [j])) ih) hc
    have e : D.parity i * wordSumParity D (j :: ν) =
        D.parity i * wordSumParity D ν + chainParity D (j :: i :: ν) [.cross 0] := by
      simp [chainParity, PG.par, wordSumParity]
      ring
    rw [e]
    exact h

variable (a i) in
theorem firstDotPoly_mem (ha : CyclotomicPolynomialParity D a) (j : I) (w : List I) :
    firstDotPoly D Sc a j w ∈ Supercategory.parity (R := k) _ _
      ((a j).natDegree • D.parity j) := by
  rw [firstDotPoly, _root_.Polynomial.aeval_def, _root_.Polynomial.eval₂_eq_sum]
  change (∑ m ∈ (a j).support, algebraMap k _ ((a j).coeff m) * dotE D Sc (j :: w) 0 ^ m) ∈ _
  apply Submodule.sum_mem
  intro m hm
  rw [← Algebra.smul_def]
  apply Submodule.smul_mem
  rw [← ha j m (_root_.Polynomial.mem_support_iff.mp hm)]
  exact firstDot_pow_parity D Sc j w m

theorem appendW_mem (ha : CyclotomicPolynomialParity D a) (ν : List I) :
    appendW D Sc a i ν ∈ Supercategory.parity (R := k) _ _ (appendQ D a i ν) := by
  have := Supercategory.comp_mem (lastToFirstHom_mem D Sc (i := i) ν)
    (firstDotPoly_mem D Sc a ha i ν)
  rw [appendQ, add_comm]
  exact this

end Basic

section CrossLast

/-- The crossing of two strands `x, z`. -/
def crossTwo (x z : I) : O[[x, z]] ⟶ O[[z, x]] :=
  cl D Sc [x, z] [z, x] [.cross 0] (by simpa using sChain_crossAt [] [] x z)

theorem crossTwo_mem (x z : I) :
    crossTwo D Sc x z ∈ Supercategory.parity (R := k) _ _ (D.parity x * D.parity z) := by
  have h := cl_mem_chainParity D Sc (k := k) (t := [x, z]) (t' := [z, x]) [.cross 0]
    (by simpa using sChain_crossAt [] [] x z)
    (by intro g hg; simp at hg; subst hg; simp [PG.pos, PG.width])
  unfold crossTwo
  simpa [chainParity, PG.par] using h

theorem crossLast_eq (s : List I) (x z : I) :
    crossLast D Sc s x z =
      eqToHom (congrArg (fun w => O[w]) (List.append_assoc s [x] [z])) ≫
        (O[s] ◁ crossTwo D Sc x z) ≫
          eqToHom (congrArg (fun w => O[w]) (List.append_assoc s [z] [x]).symm) := by
  rw [crossTwo, cl_whiskerLeft, eq_comm, eqToHom_comp_iff, comp_eqToHom_iff, Category.assoc,
    crossLast, IntertwinerMeet.eqToHom_cl_eqToHom D Sc (e₂ := rfl)
      (gs' := List.map (PG.shift s.length) [PG.cross 0]) (hg := by simp)]
  · simp only [eqToHom_refl, Category.comp_id]
    rfl
  · simp
  · exact List.append_assoc s [z] [x]

/-- A crossing of the last two strands passes a morphism whiskered by both strands, twisting it
by the parity of the crossing. -/
theorem crossLast_comp_whiskerRight {s u : List I} (x z : I) (y : O[s] ⟶ O[u]) :
    crossLast D Sc s x z ≫ ((y ▷ O[[z]]) ▷ O[[x]]) =
      ((Supercategory.twist k (D.parity x * D.parity z) y ▷ O[[x]]) ▷ O[[z]]) ≫
        crossLast D Sc u x z := by
  rw [crossLast_eq, crossLast_eq, whiskerRight_whiskerRight_list D Sc y [z] [x],
    whiskerRight_whiskerRight_list D Sc _ [x] [z]]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  erw [reassoc_of% (whiskerLeft_comp_whiskerRight_twist D Sc (crossTwo_mem D Sc x z) y)]
  rfl

end CrossLast

end OddMath.QuiverHecke
