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

/-- The parity twist commutes with right whiskering, on words. -/
theorem twist_whiskerRight_word (p : ZMod 2) {ν ν' : List I} (f : O[ν] ⟶ O[ν']) (σ : List I) :
    (Supercategory.twist k p (f ▷ O[σ]) : O[ν ++ σ] ⟶ O[ν' ++ σ]) =
      Supercategory.twist k p f ▷ O[σ] := by
  refine Supercategory.induction_on (R := k) f ?_ (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [map_zero, MonoidalSupercategory.zero_whiskerRight k, map_zero]
  · have hm : (g ▷ O[σ] : O[ν ++ σ] ⟶ O[ν' ++ σ]) ∈
        Supercategory.parity (R := k) O[ν ++ σ] O[ν' ++ σ] q :=
      MonoidalSupercategory.whiskerRight_mem (R := k) O[σ] hg
    rw [Supercategory.twist_of_mem p hg, Supercategory.twist_of_mem p hm,
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

section Closure
variable {a : I → _root_.Polynomial k} {i : I}

theorem cycHom_comp_left {s' s u : List I} (p : O[s'] ⟶ O[s]) {y : O[s] ⟶ O[u]}
    (hy : y ∈ cycHom D Sc a s u) : p ≫ y ∈ cycHom D Sc a s' u := by
  induction hy using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, w, p', q, rfl⟩ := hf
    exact Submodule.subset_span ⟨j, w, p ≫ p', q, by simp⟩
  | zero => simp
  | add f g _ _ hf hg => rw [Preadditive.comp_add]; exact add_mem hf hg
  | smul c f _ hf => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hf

theorem cycHom_comp_right {s u u' : List I} {y : O[s] ⟶ O[u]} (hy : y ∈ cycHom D Sc a s u)
    (q : O[u] ⟶ O[u']) : y ≫ q ∈ cycHom D Sc a s u' := by
  induction hy using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, w, p', q', rfl⟩ := hf
    exact Submodule.subset_span ⟨j, w, p', q' ≫ q, by simp⟩
  | zero => simp
  | add f g _ _ hf hg => rw [Preadditive.add_comp]; exact add_mem hf hg
  | smul c f _ hf => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hf

theorem cycHom_whiskerRight {s u : List I} {y : O[s] ⟶ O[u]} (hy : y ∈ cycHom D Sc a s u)
    (r : List I) : (y ▷ O[r] : O[s ++ r] ⟶ O[u ++ r]) ∈ cycHom D Sc a (s ++ r) (u ++ r) := by
  induction hy using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, w, p', q', rfl⟩ := hf
    refine Submodule.subset_span ⟨j, w ++ r, p' ▷ O[r], q' ▷ O[r], ?_⟩
    rw [MonoidalSupercategory.comp_whiskerRight (R := k),
      MonoidalSupercategory.comp_whiskerRight (R := k), firstDotPoly, firstDotPoly,
      aeval_firstDot_whiskerRight D Sc (j :: w) r (by simp)]
    rfl
  | zero => rw [MonoidalSupercategory.zero_whiskerRight k]; exact zero_mem _
  | add f g _ _ hf hg =>
    rw [MonoidalSupercategory.add_whiskerRight (R := k)]; exact add_mem hf hg
  | smul c f _ hf =>
    rw [MonoidalSupercategory.smul_whiskerRight (R := k)]; exact Submodule.smul_mem _ c hf

theorem cycHom_twist (ha : CyclotomicPolynomialParity D a) (q : ZMod 2) {s u : List I}
    {y : O[s] ⟶ O[u]} (hy : y ∈ cycHom D Sc a s u) :
    Supercategory.twist k q y ∈ cycHom D Sc a s u := by
  induction hy using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, w, p', q', rfl⟩ := hf
    rw [Supercategory.twist_comp, Supercategory.twist_comp,
      Supercategory.twist_of_mem q (firstDotPoly_mem D Sc a ha j w), Linear.smul_comp,
      Linear.comp_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, w, _, _, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul c f _ hf => rw [map_smul]; exact Submodule.smul_mem _ c hf

variable (a i) in
theorem cyc_mem_appendKill {s u t : List I} {y : O[s] ⟶ O[u]} (hy : y ∈ cycHom D Sc a s u)
    (h : O[u ++ [i]] ⟶ O[i :: t]) :
    ((y ▷ O[[i]]) ≫ h : O[s ++ [i]] ⟶ O[i :: t]) ∈ appendKill D Sc a i s t :=
  Submodule.subset_span ⟨u, y, h, hy, rfl⟩

theorem appendKill_comp {s t t' : List I} {K : O[s ++ [i]] ⟶ O[i :: t]}
    (hK : K ∈ appendKill D Sc a i s t) (h' : O[i :: t] ⟶ O[i :: t']) :
    K ≫ h' ∈ appendKill D Sc a i s t' := by
  induction hK using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, y, h, hy, rfl⟩ := hf
    rw [Category.assoc]
    exact cyc_mem_appendKill D Sc a i hy _
  | zero => simp
  | add f g _ _ hf hg => rw [Preadditive.add_comp]; exact add_mem hf hg
  | smul c f _ hf => rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hf

theorem whiskerRight_comp_mem_appendKill {s' s t : List I} (e : O[s'] ⟶ O[s])
    {K : O[s ++ [i]] ⟶ O[i :: t]} (hK : K ∈ appendKill D Sc a i s t) :
    ((e ▷ O[[i]]) ≫ K : O[s' ++ [i]] ⟶ O[i :: t]) ∈ appendKill D Sc a i s' t := by
  induction hK using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, y, h, hy, rfl⟩ := hf
    rw [← Category.assoc, ← MonoidalSupercategory.comp_whiskerRight (R := k)]
    exact cyc_mem_appendKill D Sc a i (cycHom_comp_left D Sc e hy) _
  | zero => simp
  | add f g _ _ hf hg => rw [Preadditive.comp_add]; exact add_mem hf hg
  | smul c f _ hf => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hf

/-- `Kill` is stable under `K ↦ σ ≫ (K ▷ x)`. -/
theorem crossLast_comp_mem_appendKill (ha : CyclotomicPolynomialParity D a) {s t : List I}
    (x : I) {K : O[s ++ [i]] ⟶ O[i :: t]} (hK : K ∈ appendKill D Sc a i s t) :
    (crossLast D Sc s x i ≫ (K ▷ O[[x]]) : O[s ++ [x] ++ [i]] ⟶ O[i :: (t ++ [x])]) ∈
      appendKill D Sc a i (s ++ [x]) (t ++ [x]) := by
  induction hK using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, y, h, hy, rfl⟩ := hf
    rw [MonoidalSupercategory.comp_whiskerRight (R := k),
      reassoc_of% (crossLast_comp_whiskerRight D Sc x i y)]
    exact cyc_mem_appendKill D Sc a i
      (cycHom_whiskerRight D Sc (cycHom_twist D Sc ha _ hy) [x]) _
  | zero => rw [MonoidalSupercategory.zero_whiskerRight k]; simp
  | add f g _ _ hf hg =>
    rw [MonoidalSupercategory.add_whiskerRight (R := k), Preadditive.comp_add]
    exact add_mem hf hg
  | smul c f _ hf =>
    rw [MonoidalSupercategory.smul_whiskerRight (R := k), Linear.comp_smul]
    exact Submodule.smul_mem _ c hf

end Closure

section Error
variable {a : I → _root_.Polynomial k} {i : I}

/-- The error of a composite: `E(g₁ ≫ g₂) = (g₁ ▷ i) ≫ E(g₂) + E(g₁) ≫ (i ◁ tw g₂)`. -/
theorem appendError_comp {s u t : List I} (hq : appendQ D a i s = appendQ D a i u)
    (g₁ : O[s] ⟶ O[u]) (g₂ : O[u] ⟶ O[t]) :
    appendError D Sc a i s t (g₁ ≫ g₂) =
      ((g₁ ▷ O[[i]]) ≫ appendError D Sc a i u t g₂ : O[s ++ [i]] ⟶ O[i :: t]) +
        (appendError D Sc a i s u g₁ ≫
          (O[[i]] ◁ Supercategory.twist k (appendQ D a i s) g₂) : O[s ++ [i]] ⟶ O[i :: t]) := by
  simp only [appendError_apply, Supercategory.twist_comp, MonoidalSupercategory.comp_whiskerRight
    (R := k), MonoidalSupercategory.whiskerLeft_comp (R := k), Preadditive.comp_sub,
    Preadditive.sub_comp, Category.assoc, hq]
  abel

theorem appendError_comp_mem {s u t : List I} (hq : appendQ D a i s = appendQ D a i u)
    {g₁ : O[s] ⟶ O[u]} {g₂ : O[u] ⟶ O[t]} (h₁ : appendError D Sc a i s u g₁ ∈ appendKill D Sc a i s u)
    (h₂ : appendError D Sc a i u t g₂ ∈ appendKill D Sc a i u t) :
    appendError D Sc a i s t (g₁ ≫ g₂) ∈ appendKill D Sc a i s t := by
  rw [appendError_comp D Sc hq]
  exact add_mem (whiskerRight_comp_mem_appendKill D Sc g₁ h₂) (appendKill_comp D Sc h₁ _)

/-- The error of a morphism whiskered by the last strand: (a) of the written proof. -/
theorem appendError_whiskerRight {ν ν' : List I} (x : I) (f : O[ν] ⟶ O[ν']) :
    appendError D Sc a i (ν ++ [x]) (ν' ++ [x]) (f ▷ O[[x]]) =
      (crossLast D Sc ν x i ≫
        (appendError D Sc a i ν ν' (Supercategory.twist k (D.parity i * D.parity x) f) ▷ O[[x]]) :
          O[ν ++ [x] ++ [i]] ⟶ O[i :: (ν' ++ [x])]) := by
  rw [appendError_apply, appendError_apply, appendW_append, appendW_append, sub_whiskerRight',
    Preadditive.comp_sub]
  congr 1
  · have h := crossLast_comp_whiskerRight D Sc x i
      (Supercategory.twist k (D.parity i * D.parity x) f)
    rw [mul_comm (D.parity x), Supercategory.twist_twist] at h
    rw [MonoidalSupercategory.comp_whiskerRight (R := k), reassoc_of% h]
  · have e₁ : (Supercategory.twist k (D.parity i * D.parity x) (f ▷ O[[x]]) :
        O[ν ++ [x]] ⟶ O[ν' ++ [x]]) =
        Supercategory.twist k (D.parity i * D.parity x) f ▷ O[[x]] :=
      twist_whiskerRight_word D Sc _ f [x]
    have e₂ : (Supercategory.twist k (appendQ D a i ν)
        (Supercategory.twist k (D.parity i * D.parity x) f ▷ O[[x]]) :
          O[ν ++ [x]] ⟶ O[ν' ++ [x]]) =
        Supercategory.twist k (appendQ D a i ν)
          (Supercategory.twist k (D.parity i * D.parity x) f) ▷ O[[x]] :=
      twist_whiskerRight_word D Sc _ _ [x]
    rw [MonoidalSupercategory.comp_whiskerRight (R := k), Category.assoc, appendQ_append,
      Supercategory.twist_add, e₁, e₂, whiskerLeft_whiskerRight_letter]

theorem appendError_whiskerRight_mem (ha : CyclotomicPolynomialParity D a) {ν ν' : List I}
    (x : I) {f : O[ν] ⟶ O[ν']}
    (hf : ∀ q, appendError D Sc a i ν ν' (Supercategory.twist k q f) ∈ appendKill D Sc a i ν ν') :
    appendError D Sc a i (ν ++ [x]) (ν' ++ [x]) (f ▷ O[[x]]) ∈
      appendKill D Sc a i (ν ++ [x]) (ν' ++ [x]) := by
  rw [appendError_whiskerRight]
  exact crossLast_comp_mem_appendKill D Sc ha x (hf _)

end Error

section LastDot
variable {a : I → _root_.Polynomial k} {i : I}

/-- The dot slide (1.8) for equal colours, on any word presented as `l ++ [j, j] ++ r`. -/
theorem slide_left_eq_gen {t : List I} (l r : List I) (j : I) {p : ℕ} (hp : l.length = p)
    (ht : t = l ++ [j, j] ++ r) (h₁ : SChain t (pl t [.dot p, .cross p]) t)
    (h₂ : SChain t (pl t [.cross p, .dot (p + 1)]) t) :
    cl D Sc t t [.dot p, .cross p] h₁ =
      zsign k (D.parity j * D.parity j) • cl D Sc t t [.cross p, .dot (p + 1)] h₂ +
        cl D Sc t t [] rfl := by
  subst hp ht
  exact slide_left_eq D Sc l r j h₁ h₂

/-- A dot whiskered on the left by a letter moves one strand to the right. -/
theorem whiskerLeft_letter_dotE (j : I) (w : List I) (b : ℕ) :
    (pres D Sc).obj (ob D [j]) ◁ dotE D Sc w b = dotE D Sc (j :: w) (b + 1) := by
  rw [dotE_eq, cl_whiskerLeft, dotE_eq]
  exact cl_congr_gs D Sc (by simp [PG.shift]; omega) _ _

/-- The dot on the second-to-last strand slides through the last crossing (distinct colours). -/
theorem dotE_comp_crossLast_ne (ν : List I) {x : I} (hx : x ≠ i) :
    dotE D Sc (ν ++ [x] ++ [i]) ν.length ≫ crossLast D Sc ν x i =
      zsign k (D.parity x * D.parity i) •
        (crossLast D Sc ν x i ≫ dotE D Sc (ν ++ [i] ++ [x]) (ν.length + 1)) := by
  rw [dotE_eq, dotE_eq, crossLast, cl_comp, cl_comp]
  exact slide_left_ne_gen D Sc ν [] x i hx rfl (by simp) (by simp) _ _

/-- The dot on the second-to-last strand slides through the last crossing (equal colours). -/
theorem dotE_comp_crossLast_self (ν : List I) :
    dotE D Sc (ν ++ [i] ++ [i]) ν.length ≫ crossLast D Sc ν i i =
      zsign k (D.parity i * D.parity i) •
        (crossLast D Sc ν i i ≫ dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1)) + 𝟙 _ := by
  rw [dotE_eq, dotE_eq, crossLast, cl_comp, cl_comp, ← cl_nil D Sc (ν ++ [i] ++ [i]) rfl]
  exact slide_left_eq_gen D Sc ν [] i rfl (by simp) _ _

theorem zsign_lastDot (px pi q : ZMod 2) :
    zsign k (px * pi) * zsign k (px * q) = zsign k ((q + pi * px) * px) := by
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have e : (q + pi * px) * px = px * pi + px * q := by
    rcases hz px with rfl | rfl <;> ring
  rw [e]
  rcases hz (px * pi) with h₁ | h₁ <;> rcases hz (px * q) with h₂ | h₂ <;>
    rw [h₁, h₂] <;> simp [zsign]

/-- The error of the dot on the last old strand: `0` for `x ≠ i`, `W_ν ▷ i` for `x = i`; (b) of
the written proof. -/
theorem appendError_lastDot_mem (ha : CyclotomicPolynomialParity D a) (ν : List I) (x : I) :
    appendError D Sc a i (ν ++ [x]) (ν ++ [x]) (dotE D Sc (ν ++ [x]) ν.length) ∈
      appendKill D Sc a i (ν ++ [x]) (ν ++ [x]) := by
  have hd : dotE D Sc [x] 0 ∈ Supercategory.parity (R := k) _ _ (D.parity x) :=
    firstDot_parity D Sc x []
  have hg : dotE D Sc (ν ++ [x]) ν.length = O[ν] ◁ dotE D Sc [x] 0 :=
    (whiskerLeft_dotE D Sc ν x rfl).symm
  have hgm : dotE D Sc (ν ++ [x]) ν.length ∈ Supercategory.parity (R := k) _ _ (D.parity x) := by
    rw [hg]; exact MonoidalSupercategory.whiskerLeft_mem (R := k) O[ν] hd
  have hR : (O[[i]] ◁ dotE D Sc (ν ++ [x]) ν.length : O[i :: (ν ++ [x])] ⟶ O[i :: (ν ++ [x])]) =
      (O[i :: ν] ◁ dotE D Sc [x] 0 : O[i :: (ν ++ [x])] ⟶ O[i :: (ν ++ [x])]) := by
    rw [whiskerLeft_letter_dotE, whiskerLeft_dotE D Sc (i :: ν) x (a := ν.length + 1) (by simp)]
    rfl
  have hL : (dotE D Sc (ν ++ [i] ++ [x]) (ν.length + 1) ≫ (appendW D Sc a i ν ▷ O[[x]]) :
      O[ν ++ [i] ++ [x]] ⟶ O[i :: (ν ++ [x])]) =
      zsign k (D.parity x * appendQ D a i ν) •
        ((appendW D Sc a i ν ▷ O[[x]]) ≫ (O[i :: ν] ◁ dotE D Sc [x] 0) :
          O[ν ++ [i] ++ [x]] ⟶ O[i :: (ν ++ [x])]) := by
    rw [← whiskerLeft_dotE D Sc (ν ++ [i]) x (by simp)]
    erw [whiskerLeft_comp_whiskerRight_twist D Sc hd]
    rw [Supercategory.twist_of_mem _ (appendW_mem D Sc ha ν),
      MonoidalSupercategory.smul_whiskerRight (R := k), Linear.smul_comp, sign_eq_zsign]
  rw [appendError_apply, appendW_append,
    dotE_whiskerRight D Sc (ν ++ [x]) [i] ν.length (by simp),
    Supercategory.twist_of_mem _ hgm, MonoidalSupercategory.whiskerLeft_smul (R := k), hR,
    sign_eq_zsign, appendQ_append, ← Category.assoc]
  rcases eq_or_ne x i with rfl | hx
  · rw [dotE_comp_crossLast_self, Preadditive.add_comp, Linear.smul_comp, Category.assoc]
    erw [hL]
    rw [Category.id_comp, Linear.comp_smul, Linear.comp_smul, smul_smul, zsign_lastDot,
      Category.assoc, add_sub_cancel_left]
    have hW : appendW D Sc a x ν ∈ cycHom D Sc a (ν ++ [x]) (x :: ν) :=
      Submodule.subset_span ⟨x, ν, lastToFirstHom D Sc x ν, 𝟙 _, by rw [Category.comp_id]; rfl⟩
    have h := cyc_mem_appendKill D Sc a x hW
      (𝟙 O[x :: (ν ++ [x])] : O[(x :: ν) ++ [x]] ⟶ O[x :: (ν ++ [x])])
    erw [Category.comp_id] at h
    exact h
  · rw [dotE_comp_crossLast_ne D Sc ν hx, Linear.smul_comp, Category.assoc]
    erw [hL]
    rw [Linear.comp_smul, Linear.comp_smul, smul_smul, zsign_lastDot, Category.assoc, sub_self]
    exact zero_mem _

end LastDot

section LastCross
variable {a : I → _root_.Polynomial k} {i : I}

theorem zsign_add_aux (p q : ZMod 2) : zsign k (p + q) = zsign k p * zsign k q := by
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hz p with rfl | rfl <;> rcases hz q with rfl | rfl <;> simp [zsign]

theorem parity_lastCross (q pi pc px : ZMod 2) :
    (q + pi * pc + pi * px) * (pc * px) + pc * px * q = 0 := by
  revert q pi pc px; decide

theorem crossLast_mem (s : List I) (x z : I) :
    crossLast D Sc s x z ∈ Supercategory.parity (R := k) _ _ (D.parity x * D.parity z) := by
  have h := cl_mem_chainParity D Sc (k := k) (t := s ++ [x] ++ [z]) (t' := s ++ [z] ++ [x])
    [.cross s.length] (by simpa using sChain_crossAt s [] x z)
    (by intro g hg; simp at hg; subst hg; simp [PG.pos, PG.width])
  unfold crossLast
  simpa [chainParity, PG.par] using h

theorem cl_comp_three {t t₁ t₂ t' : List I} (Q R S : List PG) (h₁ : SChain t (pl t Q) t₁)
    (h₂ : SChain t₁ (pl t₁ R) t₂) (h₃ : SChain t₂ (pl t₂ S) t') :
    cl D Sc t t₁ Q h₁ ≫ cl D Sc t₁ t₂ R h₂ ≫ cl D Sc t₂ t' S h₃ =
      cl D Sc t t' (Q ++ R ++ S) (by
        rw [List.append_assoc]; exact sChain_append_of h₁ (sChain_append_of h₂ h₃)) := by
  rw [cl_comp, cl_comp]
  exact cl_congr_gs D Sc (List.append_assoc _ _ _).symm _ _

theorem crossLast_whiskerRight_cl (s : List I) (x z y : I) :
    crossLast D Sc s x z ▷ O[[y]] =
      cl D Sc (s ++ [x] ++ [z] ++ [y]) (s ++ [z] ++ [x] ++ [y]) [.cross s.length]
        (by simpa using sChain_crossAt s [y] x z) := by
  rw [crossLast, cl_whiskerRight D Sc _ _ [y]
    (by intro g hg; simp at hg; subst hg; simp [PG.pos, PG.width])]

theorem whiskerLeft_crossLast (j : I) (s : List I) (x z : I) :
    (O[[j]] ◁ crossLast D Sc s x z : O[j :: (s ++ [x] ++ [z])] ⟶ O[j :: (s ++ [z] ++ [x])]) =
      crossLast D Sc (j :: s) x z := by
  rw [crossLast, cl_whiskerLeft, crossLast]
  exact cl_congr_gs D Sc (by simp [PG.shift, add_comm]) _ _

/-- The error of the crossing of the last two old strands, as the difference of the two braid
words in the window `(c, x, i)` followed by `W_m`; (c) of the written proof. -/
theorem appendError_crossLast (ha : CyclotomicPolynomialParity D a) (m : List I) (c x : I) :
    appendError D Sc a i (m ++ [c] ++ [x]) (m ++ [x] ++ [c]) (crossLast D Sc m c x) =
      (((crossLast D Sc m c x ▷ O[[i]] : O[m ++ [c] ++ [x] ++ [i]] ⟶ O[m ++ [x] ++ [c] ++ [i]]) ≫
          crossLast D Sc (m ++ [x]) c i ≫
          (crossLast D Sc m x i ▷ O[[c]] : O[m ++ [x] ++ [i] ++ [c]] ⟶ O[m ++ [i] ++ [x] ++ [c]]) :
          O[m ++ [c] ++ [x] ++ [i]] ⟶ O[m ++ [i] ++ [x] ++ [c]]) -
        (crossLast D Sc (m ++ [c]) x i ≫
          (crossLast D Sc m c i ▷ O[[x]] : O[m ++ [c] ++ [i] ++ [x]] ⟶ O[m ++ [i] ++ [c] ++ [x]]) ≫
          crossLast D Sc (m ++ [i]) c x :
          O[m ++ [c] ++ [x] ++ [i]] ⟶ O[m ++ [i] ++ [x] ++ [c]])) ≫
        ((appendW D Sc a i m ▷ O[[x]]) ▷ O[[c]] :
          O[m ++ [i] ++ [x] ++ [c]] ⟶ O[i :: (m ++ [x] ++ [c])]) := by
  have hs : Supercategory.sign k (appendQ D a i (m ++ [c] ++ [x]) * (D.parity c * D.parity x)) *
      Supercategory.sign k (D.parity c * D.parity x * appendQ D a i m) = 1 := by
    rw [sign_eq_zsign, sign_eq_zsign, ← zsign_add_aux, appendQ_append, appendQ_append,
      parity_lastCross]
    simp [zsign]
  have hsw : ((appendW D Sc a i m ▷ O[[c]]) ▷ O[[x]]) ≫ crossLast D Sc (i :: m) c x =
      Supercategory.sign k (D.parity c * D.parity x * appendQ D a i m) •
        (crossLast D Sc (m ++ [i]) c x ≫ ((appendW D Sc a i m ▷ O[[x]]) ▷ O[[c]])) := by
    have h := crossLast_comp_whiskerRight D Sc c x
      (Supercategory.twist k (D.parity c * D.parity x) (appendW D Sc a i m))
    rw [Supercategory.twist_twist, Supercategory.twist_of_mem _ (appendW_mem D Sc ha m),
      MonoidalSupercategory.smul_whiskerRight (R := k),
      MonoidalSupercategory.smul_whiskerRight (R := k), Linear.comp_smul] at h
    exact h.symm
  rw [appendError_apply, Supercategory.twist_of_mem _ (crossLast_mem D Sc m c x),
    MonoidalSupercategory.whiskerLeft_smul (R := k), whiskerLeft_crossLast,
    appendW_append D Sc (m ++ [x]) c, appendW_append D Sc (m ++ [c]) x,
    appendW_append D Sc m x, appendW_append D Sc m c]
  simp only [MonoidalSupercategory.comp_whiskerRight (R := k), Category.assoc, Linear.comp_smul]
  erw [hsw]
  rw [Linear.comp_smul, Linear.comp_smul, smul_smul, hs, one_smul, Preadditive.sub_comp]
  simp only [Category.assoc]

theorem sub_comp_mem_of_eq {A B C : (pres D Sc).Presented} {f g : A ⟶ B} (h : f = g)
    (Z : B ⟶ C) (K : Submodule k (A ⟶ C)) : (f - g) ≫ Z ∈ K := by
  rw [h, sub_self, Limits.zero_comp]
  exact zero_mem _

/-- The last dot on the moving strand passes an old cyclotomic morphism whiskered by `i`. -/
theorem whiskerLeft_dotPow_comp_mem_appendKill (ha : CyclotomicPolynomialParity D a)
    {n t : List I} {Y : O[n] ⟶ O[i :: t]} (hY : Y ∈ cycHom D Sc a n (i :: t)) (e : ℕ) :
    ((O[n] ◁ (dotE D Sc [i] 0 ^ e)) ≫ (Y ▷ O[[i]]) : O[n ++ [i]] ⟶ O[i :: (t ++ [i])]) ∈
      appendKill D Sc a i n (t ++ [i]) := by
  erw [whiskerLeft_comp_whiskerRight_twist D Sc (firstDot_pow_parity D Sc i [] e) Y]
  exact cyc_mem_appendKill D Sc a i (cycHom_twist D Sc ha _ hY) _

/-- The braid correction in the window `(i, x, i)`, followed by `W_m`, is killed. -/
theorem braid_comp_mem_appendKill (ha : CyclotomicPolynomialParity D a) (m : List I) {x : I}
    (hx : i ≠ x) {LA LB : List PG}
    (eA : LA = [.cross m.length, .cross (m.length + 1), .cross m.length])
    (eB : LB = [.cross (m.length + 1), .cross m.length, .cross (m.length + 1)])
    (hA : SChain (m ++ [i] ++ [x] ++ [i]) (pl (m ++ [i] ++ [x] ++ [i]) LA) (m ++ [i] ++ [x] ++ [i]))
    (hB : SChain (m ++ [i] ++ [x] ++ [i]) (pl (m ++ [i] ++ [x] ++ [i]) LB)
      (m ++ [i] ++ [x] ++ [i])) :
    ((cl D Sc _ _ _ hA - cl D Sc _ _ _ hB) ≫ ((appendW D Sc a i m ▷ O[[x]]) ▷ O[[i]]) :
      O[m ++ [i] ++ [x] ++ [i]] ⟶ O[i :: (m ++ [x] ++ [i])]) ∈
        appendKill D Sc a i (m ++ [i] ++ [x]) (m ++ [x] ++ [i]) := by
  subst eA eB
  rw [IntertwinerMeet.braid_iji_gen D Sc m [] hx (by simp) rfl hA hB]
  have hu : ∀ (q : ℕ), q < (m ++ [i] ++ [x]).length → ∀ e : ℕ,
      dotE D Sc (m ++ [i] ++ [x] ++ [i]) q ^ e = (dotE D Sc (m ++ [i] ++ [x]) q ^ e) ▷ O[[i]] := by
    intro q hq e
    rw [← whiskerListAlgHom_apply, map_pow, whiskerListAlgHom_apply,
      dotE_whiskerRight D Sc _ [i] q hq]
  have hw : ∀ e : ℕ, dotE D Sc (m ++ [i] ++ [x] ++ [i]) (m.length + 2) ^ e =
      O[m ++ [i] ++ [x]] ◁ (dotE D Sc [i] 0 ^ e) := by
    intro e
    rw [dotE_pow, dotE_pow, cl_whiskerLeft]
    exact cl_congr_gs D Sc (by simp [PG.shift]) _ _
  have hW : appendW D Sc a i m ∈ cycHom D Sc a (m ++ [i]) (i :: m) :=
    Submodule.subset_span ⟨i, m, lastToFirstHom D Sc i m, 𝟙 _, by rw [Category.comp_id]; rfl⟩
  let L : (O[m ++ [i] ++ [x] ++ [i]] ⟶ O[m ++ [i] ++ [x] ++ [i]]) →ₗ[k]
      (O[m ++ [i] ++ [x] ++ [i]] ⟶ O[i :: (m ++ [x] ++ [i])]) :=
    { toFun := fun f => f ≫ ((appendW D Sc a i m ▷ O[[x]]) ▷ O[[i]])
      map_add' := fun f g => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun c f => Linear.smul_comp _ _ _ _ _ _ }
  have hmon : ∀ e₁ e₂ e₃ : ℕ,
      (dotE D Sc (m ++ [i] ++ [x] ++ [i]) m.length ^ e₁ *
          dotE D Sc (m ++ [i] ++ [x] ++ [i]) (m.length + 1) ^ e₂ *
          dotE D Sc (m ++ [i] ++ [x] ++ [i]) (m.length + 2) ^ e₃) ∈
        (appendKill D Sc a i (m ++ [i] ++ [x]) (m ++ [x] ++ [i])).comap L := by
    intro e₁ e₂ e₃
    rw [Submodule.mem_comap]
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    rw [End.mul_def, End.mul_def, hw, hu _ (by simp) e₁, hu _ (by simp) e₂]
    have hY := cycHom_comp_left D Sc (dotE D Sc (m ++ [i] ++ [x]) (m.length + 1) ^ e₂)
      (cycHom_comp_left D Sc (dotE D Sc (m ++ [i] ++ [x]) m.length ^ e₁)
        (cycHom_whiskerRight D Sc hW [x]))
    have h := whiskerLeft_dotPow_comp_mem_appendKill D Sc ha (t := m ++ [x]) hY e₃
    rw [MonoidalSupercategory.comp_whiskerRight (R := k),
      MonoidalSupercategory.comp_whiskerRight (R := k)] at h
    simpa only [Category.assoc] using h
  change L _ ∈ _
  rw [← Submodule.mem_comap]
  unfold IntertwinerMeet.braidCorr
  refine add_mem (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_)
    (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
      Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hmon _ _ _))
  have h := hmon (D.dn i x - 1 - r) 0 r
  rwa [pow_zero, mul_one] at h

/-- The error of the crossing of the last two old strands is killed. -/
theorem appendError_crossLast_mem (ha : CyclotomicPolynomialParity D a) (m : List I)
    (c x : I) :
    appendError D Sc a i (m ++ [c] ++ [x]) (m ++ [x] ++ [c]) (crossLast D Sc m c x) ∈
      appendKill D Sc a i (m ++ [c] ++ [x]) (m ++ [x] ++ [c]) := by
  rw [appendError_crossLast D Sc ha, crossLast_whiskerRight_cl, crossLast_whiskerRight_cl,
    crossLast_whiskerRight_cl, crossLast, crossLast, crossLast, cl_comp_three, cl_comp_three]
  by_cases hb : c = i ∧ c ≠ x
  · obtain ⟨rfl, hx⟩ := hb
    refine braid_comp_mem_appendKill D Sc ha m hx ?_ ?_ _ _ <;> simp
  · refine sub_comp_mem_of_eq D Sc ?_ _ _
    refine (braid_ne_gen D Sc m [] c x i hb ?_ ?_ ?_ ?_ _ _).symm <;> simp

end LastCross

section Main
variable {a : I → _root_.Polynomial k} {i : I}

theorem appendQ_act (g : PG) (t : List I) : appendQ D a i (g.act t) = appendQ D a i t := by
  simp only [appendQ]
  rw [show g.act t = tgt t [g] from rfl, wordSumParity_tgt]

/-- A generator that does not fit on the word acts as the identity. -/
theorem ld_act_of_lt {g : PG} {t : List I} (hg : t.length < g.pos + g.width) :
    g.ld t = [] ∧ g.act t = t := by
  cases g with
  | dot p =>
    simp only [PG.pos, PG.width] at hg
    have h : t.drop p = [] := List.drop_eq_nil_of_le (by omega)
    simp [PG.ld, PG.act, h]
  | cross b =>
    simp only [PG.pos, PG.width] at hg
    have hl : (t.drop b).length < 2 := by simp; omega
    rcases h : t.drop b with _ | ⟨x, _ | ⟨y, r⟩⟩
    · simp [PG.ld, PG.act, h]
    · simp [PG.ld, PG.act, h]
    · rw [h] at hl; simp at hl

theorem appendError_id (s : List I) : appendError D Sc a i s s (𝟙 _) = 0 := by
  rw [appendError_apply, Supercategory.twist_id, sub_eq_zero]
  have e1 : (𝟙 O[s] ▷ O[[i]] : O[s] ⊗ O[[i]] ⟶ O[s] ⊗ O[[i]]) = 𝟙 _ :=
    MonoidalSupercategory.id_whiskerRight (R := k) ..
  have e2 : (O[[i]] ◁ 𝟙 O[s] : O[[i]] ⊗ O[s] ⟶ O[[i]] ⊗ O[s]) = 𝟙 _ :=
    MonoidalSupercategory.whiskerLeft_id (R := k) ..
  calc _ = 𝟙 _ ≫ appendW D Sc a i s := congrArg (· ≫ appendW D Sc a i s) e1
    _ = appendW D Sc a i s ≫ 𝟙 _ := by rw [Category.id_comp, Category.comp_id]
    _ = _ := (congrArg (appendW D Sc a i s ≫ ·) e2).symm

/-- The balance for one positioned generator, given the balance on shorter words. -/
theorem appendError_gen_mem (ha : CyclotomicPolynomialParity D a) {n : ℕ}
    (ih : ∀ s t : List I, s.length < n → ∀ g : O[s] ⟶ O[t],
      appendError D Sc a i s t g ∈ appendKill D Sc a i s t)
    (g : PG) {u u' : List I} (hu : u.length = n) (h : SChain u (pl u [g]) u') :
    appendError D Sc a i u u' (cl D Sc u u' [g] h) ∈ appendKill D Sc a i u u' := by
  by_cases hfit : g.pos + g.width ≤ u.length
  swap
  · obtain ⟨hld, -⟩ := ld_act_of_lt (g := g) (t := u) (by omega)
    have hpl : pl u [g] = pl u [] := by simp [hld]
    have h' : SChain u (pl u []) u' := hpl ▸ h
    have hu' : u = u' := h'
    subst hu'
    rw [cl_congr D Sc h h' hpl, cl_nil, appendError_id]
    exact zero_mem _
  obtain rfl | ⟨ν, x, rfl⟩ : u = [] ∨ ∃ ν x, u = ν ++ [x] := by
    rcases List.eq_nil_or_concat u with h | ⟨ν, x, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨ν, x, by simpa using h⟩
  · cases g <;> simp [PG.pos, PG.width] at hfit
  by_cases hin : g.pos + g.width ≤ ν.length
  · have hF : Fits ν.length [g] := by intro g' hg'; simp at hg'; subst hg'; exact hin
    obtain rfl : tgt ν [g] ++ [x] = u' :=
      sChain_target (sChain_append_one x (sChain_pl ν [g]) hF) h
    have e : cl D Sc (ν ++ [x]) (tgt ν [g] ++ [x]) [g] h =
        cl D Sc ν (tgt ν [g]) [g] (sChain_pl ν [g]) ▷ O[[x]] :=
      (cl_whiskerRight D Sc [g] _ [x] hF).symm
    rw [e]
    subst hu
    exact appendError_whiskerRight_mem D Sc ha x fun q => ih _ _ (by simp) _
  · cases g with
    | dot p =>
      simp only [PG.pos, PG.width, List.length_append, List.length_singleton] at hfit hin
      obtain rfl : p = ν.length := by omega
      obtain rfl : ν ++ [x] = u' := sChain_target (sChain_dotAny _ ν.length) h
      rw [← dotE_eq_cl D Sc h]
      exact appendError_lastDot_mem D Sc ha ν x
    | cross b =>
      simp only [PG.pos, PG.width, List.length_append, List.length_singleton] at hfit hin
      obtain rfl | ⟨m, c, rfl⟩ : ν = [] ∨ ∃ m c, ν = m ++ [c] := by
        rcases List.eq_nil_or_concat ν with h | ⟨m, c, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨m, c, by simpa using h⟩
      · simp at hfit hin
      simp only [List.length_append, List.length_singleton] at hfit hin
      obtain rfl : b = m.length := by omega
      obtain rfl : m ++ [x] ++ [c] = u' :=
        sChain_target (by simpa using sChain_crossAt m [] c x) h
      exact appendError_crossLast_mem D Sc ha m c x

/-- The balance along a positioned word, given the balance on shorter words. -/
theorem appendError_cl_mem (ha : CyclotomicPolynomialParity D a) {n : ℕ}
    (ih : ∀ s t : List I, s.length < n → ∀ g : O[s] ⟶ O[t],
      appendError D Sc a i s t g ∈ appendKill D Sc a i s t)
    (gs : List PG) {u u' : List I} (hu : u.length = n) (h : SChain u (pl u gs) u') :
    appendError D Sc a i u u' (cl D Sc u u' gs h) ∈ appendKill D Sc a i u u' := by
  induction gs generalizing u with
  | nil =>
    obtain rfl : u = u' := h
    rw [cl_nil, appendError_id]
    exact zero_mem _
  | cons g gs ihg =>
    have e := cl_append D Sc [g] gs h
    rw [show cl D Sc u u' (g :: gs) h = _ from e]
    refine appendError_comp_mem D Sc (appendQ_act D g u).symm
      (appendError_gen_mem D Sc ha ih g hu _) (ihg ?_ _)
    rw [length_act, hu]

/-- **Balance of `P`.** For every morphism `g : s ⟶ t` of words, the error
`(g ▷ i) ≫ W_t - W_s ≫ (i ◁ tw_(q_s) g)` lies in the span of the morphisms `(y ▷ i) ≫ h` with
`y` in the old cyclotomic ideal (`docs/Nondegeneracy/AppendMackeySource.md`, §2). -/
theorem appendError_mem_appendKill (ha : CyclotomicPolynomialParity D a) {s t : List I}
    (g : O[s] ⟶ O[t]) : appendError D Sc a i s t g ∈ appendKill D Sc a i s t := by
  suffices H : ∀ n (s t : List I), s.length = n → ∀ g : O[s] ⟶ O[t],
      appendError D Sc a i s t g ∈ appendKill D Sc a i s t from H _ s t rfl g
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hs g
    have ih' : ∀ s t : List I, s.length < n → ∀ g : O[s] ⟶ O[t],
        appendError D Sc a i s t g ∈ appendKill D Sc a i s t :=
      fun s t hlt g => ih _ hlt s t rfl g
    have hle : Submodule.span k {f : O[s] ⟶ O[t] |
        ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < s.length) ∧
          ∃ w : Equiv.Perm (Fin s.length),
            ∃ h, cl D Sc s t (l.map PG.dot ++ cw (Categorification.TypeA.canWord s.length w)) h = f} ≤
        (appendKill D Sc a i s t).comap (appendError D Sc a i s t) := by
      rw [Submodule.span_le]
      rintro _ ⟨l, -, -, w, h, rfl⟩
      exact appendError_cl_mem D Sc ha ih' _ hs h
    rw [span_normalForms D Sc s t] at hle
    exact hle Submodule.mem_top

end Main

end OddMath.QuiverHecke
