import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import Mathlib.LinearAlgebra.Quotient.Bilinear
import StringDiagrams.Super.GSBim
import StringDiagrams.Super.GSCat

/-!
# Truncated append

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Append-old relations over the ELV coefficient category

This is the append-strand counterpart of the old relation span used in
`DeformedGlobalQP.md`: extend an old cyclotomic ideal element by an identity
strand on the right, then allow an arbitrary ambient continuation. The span
uses the full ELV Hom spaces, with every cutoff and exterior coefficient intact.

The span is stable under ambient postcomposition and under precomposition by
right extensions of old morphisms. These are relation-space statements only;
no balance for the moving-strand map or descent of a prescribed map is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Append an identity strand to an old ideal element and allow any ambient continuation. -/
def appendRelations (i : I) (v w : List I) :
    Submodule k (hom D Sc cutoff (v ++ [i]) w) :=
  Submodule.span k {f | ∃ t, ∃ r : hom D Sc cutoff v t,
    r ∈ ideal D Sc cutoff v t ∧ ∃ h : hom D Sc cutoff (t ++ [i]) w,
      rightContext D Sc cutoff [i] v t r ≫ h = f}

/-- The append-old quotient, without imposing a moving-strand cyclotomic relation. -/
abbrev AppendTarget (i : I) (v w : List I) :=
  hom D Sc cutoff (v ++ [i]) w ⧸ appendRelations D Sc cutoff i v w

/-- The canonical linear projection to the append-old quotient. -/
def appendProjection (i : I) (v w : List I) :
    hom D Sc cutoff (v ++ [i]) w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (appendRelations D Sc cutoff i v w).mkQ

/-- Every right-extended old ideal element followed by a continuation is a relation. -/
theorem appendRelations_mem (i : I) {v t w : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    rightContext D Sc cutoff [i] v t r ≫ h ∈ appendRelations D Sc cutoff i v w :=
  Submodule.subset_span ⟨t, r, hr, h, rfl⟩

/-- In particular, the right extension itself belongs to the append-old span. -/
theorem rightContext_mem_appendRelations (i : I) {v t : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t) :
    rightContext D Sc cutoff [i] v t r ∈ appendRelations D Sc cutoff i v (t ++ [i]) := by
  simpa only [Category.comp_id] using appendRelations_mem D Sc cutoff i hr (𝟙 _)

/-- The ambient continuation can be postcomposed by an arbitrary ELV morphism. -/
theorem appendRelations_comp (i : I) {v t w : List I}
    {r : hom D Sc cutoff (v ++ [i]) t} (hr : r ∈ appendRelations D Sc cutoff i v t)
    (h : hom D Sc cutoff t w) : r ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨s, b, hb, a, rfl⟩ := hr
    exact Submodule.subset_span ⟨s, b, hb, a ≫ h, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs =>
    rw [Preadditive.add_comp]
    exact Submodule.add_mem _ hr hs
  | smul c r _ hr =>
    rw [Linear.smul_comp]
    exact Submodule.smul_mem _ c hr

/-- Precomposition is allowed for right extensions of old morphisms, not arbitrary ambient ones. -/
theorem comp_appendRelations (i : I) {u v w : List I}
    (a : hom D Sc cutoff u v) {r : hom D Sc cutoff (v ++ [i]) w}
    (hr : r ∈ appendRelations D Sc cutoff i v w) :
    rightContext D Sc cutoff [i] u v a ≫ r ∈ appendRelations D Sc cutoff i u w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨t, b, hb, h, rfl⟩ := hr
    apply Submodule.subset_span
    refine ⟨t, a ≫ b, comp_ideal D Sc cutoff a hb, h, ?_⟩
    rw [rightContext_comp, Category.assoc]
  | zero => simp
  | add r s _ _ hr hs =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ hr hs
  | smul c r _ hr =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c hr

/-- Append-old relations lie in the enlarged old cyclotomic ideal. -/
theorem appendRelations_le_ideal (i : I) (v w : List I) :
    appendRelations D Sc cutoff i v w ≤ ideal D Sc cutoff (v ++ [i]) w := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, r, hr, h, rfl⟩
  exact ideal_comp D Sc cutoff (ideal_rightContext D Sc cutoff [i] hr) h

/-- The quotient kills each canonical append-old relation. -/
theorem appendProjection_old_ideal (i : I) {v t w : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    appendProjection D Sc cutoff i v w (rightContext D Sc cutoff [i] v t r ≫ h) = 0 := by
  change (appendRelations D Sc cutoff i v w).mkQ _ = 0
  exact (Submodule.Quotient.mk_eq_zero (appendRelations D Sc cutoff i v w)).mpr
    (appendRelations_mem D Sc cutoff i hr h)

/-- No relations beyond the specified span are hidden in the projection. -/
theorem appendProjection_eq_zero_iff (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    appendProjection D Sc cutoff i v w h = 0 ↔ h ∈ appendRelations D Sc cutoff i v w :=
  Submodule.Quotient.mk_eq_zero _

/-- Every append-old quotient class has an ambient representative. -/
theorem appendProjection_surjective (i : I) (v w : List I) :
    Function.Surjective (appendProjection D Sc cutoff i v w) := Submodule.mkQ_surjective _

end OddMath.QuiverHecke.ELV
end

end

section

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

theorem sign_eq_zsign (p : ZMod 2) : Supercategory.sign k p = zsign k p := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) p with rfl | rfl <;>
    simp [Supercategory.sign, zsign]

end Interchange

section Whisker

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
end

end

section

/-! # The coefficient-truncated ELV category

Words carry the quotient Hom modules `TruncatedOld`. Composition descends through
both two-sided ideals. The integer grading and super parity are independent.
No monoidal structure is asserted: prepending need not preserve the first-position
cyclotomic relation.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Words in the coefficient-truncated old ELV category. -/
structure TruncatedCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (cutoff : I → ℕ) (N : ℕ) where
  word : List I

/-- Quotient composition, in categorical order. -/
def truncatedComp (v t w : List I) :
    TruncatedOld D Sc cutoff N v t →ₗ[k]
      TruncatedOld D Sc cutoff N t w →ₗ[k] TruncatedOld D Sc cutoff N v w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (truncatedIdeal D Sc cutoff N v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
       hom D Sc cutoff v t →ₗ[k] hom D Sc cutoff t w →ₗ[k] TruncatedOld D Sc cutoff N v w)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (truncatedIdeal_comp D Sc cutoff N hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (comp_truncatedIdeal D Sc cutoff N f hg))

@[simp] theorem truncatedComp_mk (v t w : List I)
    (f : hom D Sc cutoff v t) (g : hom D Sc cutoff t w) :
    truncatedComp D Sc cutoff N v t w
      ((truncatedIdeal D Sc cutoff N v t).mkQ f)
      ((truncatedIdeal D Sc cutoff N t w).mkQ g) =
      (truncatedIdeal D Sc cutoff N v w).mkQ (f ≫ g) := rfl

instance truncatedCategory : Category (TruncatedCategory D Sc cutoff N) where
  Hom v w := TruncatedOld D Sc cutoff N v.word w.word
  id v := (truncatedIdeal D Sc cutoff N v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := truncatedComp D Sc cutoff N v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    exact congrArg (truncatedIdeal D Sc cutoff N v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    exact congrArg (truncatedIdeal D Sc cutoff N v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (truncatedIdeal D Sc cutoff N t.word w.word).mkQ_surjective g
    obtain ⟨h, rfl⟩ := (truncatedIdeal D Sc cutoff N w.word z.word).mkQ_surjective h
    exact congrArg (truncatedIdeal D Sc cutoff N v.word z.word).mkQ (Category.assoc f g h)

instance truncatedPreadditive : Preadditive (TruncatedCategory D Sc cutoff N) where
  homGroup v w := inferInstanceAs (AddCommGroup (TruncatedOld D Sc cutoff N v.word w.word))
  add_comp := by
    intro v t w f g h
    exact LinearMap.map_add₂ (truncatedComp D Sc cutoff N v.word t.word w.word) f g h
  comp_add := by
    intro v t w f g h
    exact (truncatedComp D Sc cutoff N v.word t.word w.word f).map_add g h

instance truncatedLinear : Linear k (TruncatedCategory D Sc cutoff N) where
  homModule v w := inferInstanceAs (Module k (TruncatedOld D Sc cutoff N v.word w.word))
  smul_comp := by
    intro v t w r f g
    exact LinearMap.map_smul₂ (truncatedComp D Sc cutoff N v.word t.word w.word) r f g
  comp_smul := by
    intro v t w f r g
    exact (truncatedComp D Sc cutoff N v.word t.word w.word f).map_smul r g

instance truncatedSupercategory : Supercategory k (TruncatedCategory D Sc cutoff N) where
  parity v w := truncatedParity D Sc cutoff N v.word w.word
  isInternal v w := truncatedParity_internal D Sc cutoff N v.word w.word
  id_mem v := Submodule.mem_map_of_mem (Supercategory.id_mem (obj D Sc cutoff v.word))
  comp_mem := by
    rintro v t w p q f g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact Submodule.mem_map_of_mem (Supercategory.comp_mem ha hb)

/-- The categorical projection agrees with the descended quotient projection. -/
theorem truncatedCategory_proj (v w : TruncatedCategory D Sc cutoff N)
    (p : ZMod 2) (f : v ⟶ w) :
    Supercategory.proj k p f = truncatedProj D Sc cutoff N v.word w.word p f := by
  refine Supercategory.induction_on (R := k) f (by simp) (fun q f hf => ?_)
    (fun f g hf hg => by simp only [map_add, hf, hg])
  ·
    rw [truncatedProj_of_mem D Sc cutoff N hf p]
    by_cases h : q = p
    · subst q
      rw [ite_eq_left rfl, Supercategory.proj_of_mem hf]
    · rw [ite_eq_right h, Supercategory.proj_of_mem_ne hf h]

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

@[instance_reducible]
def truncatedGradedSupercategory :
    GradedSupercategory k (TruncatedCategory D Sc cutoff N) where
  degree v w := truncatedDegree D Sc cutoff sy hc N v.word w.word
  isInternal_degree v w := truncatedDegree_internal D Sc cutoff sy hc N v.word w.word
  proj_mem_degree := by
    intro v w n f p hf
    rw [truncatedCategory_proj]
    obtain ⟨a, ha, rfl⟩ := hf
    rw [truncatedProj_mk]
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.proj_mem_degree p ha)
  id_mem_degree v := by
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.id_mem_degree (obj D Sc cutoff v.word))
  comp_mem_degree := by
    rintro v t w m n f g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.comp_mem_degree ha hb)

/-- Ordinary endomorphisms: multiplication is reverse categorical composition. -/
abbrev TruncatedEnd (v : List I) := End (⟨v⟩ : TruncatedCategory D Sc cutoff N)

/-- Parity parts of the endomorphism ring. -/
def truncatedEndParity (v : List I) : ZMod 2 → Submodule k (TruncatedEnd D Sc cutoff N v) :=
  truncatedParity D Sc cutoff N v v

/-- Integer degree parts of the endomorphism ring. -/
def truncatedEndDegree (v : List I) : ℤ → Submodule k (TruncatedEnd D Sc cutoff N v) :=
  truncatedDegree D Sc cutoff sy hc N v v

instance truncatedEndParityMonoid (v : List I) :
    SetLike.GradedMonoid (truncatedEndParity D Sc cutoff N v) where
  one_mem := Supercategory.id_mem (⟨v⟩ : TruncatedCategory D Sc cutoff N)
  mul_mem p q f g hf hg := by
    change g ≫ f ∈ truncatedParity D Sc cutoff N v v (p + q)
    rw [add_comm]
    exact Supercategory.comp_mem (R := k)
      (X := (⟨v⟩ : TruncatedCategory D Sc cutoff N)) (Y := ⟨v⟩) (Z := ⟨v⟩) hg hf

instance truncatedEndParityGrading (v : List I) :
    GradedAlgebra (truncatedEndParity D Sc cutoff N v) :=
  { (truncatedParity_internal D Sc cutoff N v v).chooseDecomposition with }

instance truncatedEndDegreeMonoid (v : List I) :
    SetLike.GradedMonoid (truncatedEndDegree D Sc cutoff N sy hc v) where
  one_mem := by
    let _ := truncatedGradedSupercategory D Sc cutoff N sy hc
    exact GradedSupercategory.id_mem_degree (⟨v⟩ : TruncatedCategory D Sc cutoff N)
  mul_mem p q f g hf hg := by
    let _ := truncatedGradedSupercategory D Sc cutoff N sy hc
    change g ≫ f ∈ truncatedDegree D Sc cutoff sy hc N v v (p + q)
    rw [add_comm]
    exact GradedSupercategory.comp_mem_degree (R := k)
      (X := (⟨v⟩ : TruncatedCategory D Sc cutoff N)) (Y := ⟨v⟩) (Z := ⟨v⟩) hg hf

instance truncatedEndDegreeGrading (v : List I) :
    GradedAlgebra (truncatedEndDegree D Sc cutoff N sy hc v) :=
  { (truncatedDegree_internal D Sc cutoff sy hc N v v).chooseDecomposition with }

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Right append on the coefficient-truncated ELV category

Right contexts preserve both the first-position cyclotomic ideal and the
coefficient weight ideal. The resulting functors use the original signed
coefficient composition; no left-context stability is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

@[simp] theorem rightContext_id (σ v : List I) :
    rightContext D Sc cutoff σ v v (𝟙 (obj D Sc cutoff v)) =
      𝟙 (obj D Sc cutoff (v ++ σ)) := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((𝟙 ((pres D Sc).obj (ob D v))) ▷ (pres D Sc).obj (ob D σ)) = _
  rw [MonoidalSupercategory.id_whiskerRight (R := k)]
  rfl

@[simp] theorem rightContext_coefficientIdentity (σ t : List I) (a : SKM.SYM D k) :
    rightContext D Sc cutoff σ t t (coefficientIdentity D Sc cutoff t a) =
      coefficientIdentity D Sc cutoff (t ++ σ) a := by
  change SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k]
    ((𝟙 ((pres D Sc).obj (ob D t))) ▷ (pres D Sc).obj (ob D σ)) = _
  rw [MonoidalSupercategory.id_whiskerRight (R := k)]
  rfl

/-- Coefficient weights do not change when spectator strands are appended. -/
theorem coefficientHomIdeal_rightContext (N : ℕ) (σ : List I)
    {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w) :
    rightContext D Sc cutoff σ v w f ∈
      coefficientHomIdeal D Sc cutoff N (v ++ σ) (w ++ σ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, a, ha, l, r, rfl⟩ := hf
    rw [rightContext_comp, rightContext_comp, rightContext_coefficientIdentity]
    exact Submodule.subset_span ⟨t ++ σ, a, ha,
      rightContext D Sc cutoff σ v t l, rightContext D Sc cutoff σ t w r, rfl⟩
  | zero => simpa only [map_zero] using
      (coefficientHomIdeal D Sc cutoff N (v ++ σ) (w ++ σ)).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

theorem truncatedIdeal_rightContext (N : ℕ) (σ : List I)
    {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v w) :
    rightContext D Sc cutoff σ v w f ∈
      truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, ideal_rightContext D Sc cutoff σ ha,
    _, coefficientHomIdeal_rightContext D Sc cutoff N σ hb, rfl⟩

variable (N : ℕ)

/-- Right extension on the two-ideal quotient. -/
def truncatedRightContext (σ v w : List I) :
    TruncatedOld D Sc cutoff N v w →ₗ[k]
      TruncatedOld D Sc cutoff N (v ++ σ) (w ++ σ) :=
  (truncatedIdeal D Sc cutoff N v w).mapQ
    (truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ))
    (rightContext D Sc cutoff σ v w)
    (fun _ hf => truncatedIdeal_rightContext D Sc cutoff N σ hf)

@[simp] theorem truncatedRightContext_mk (σ v w : List I) (f : hom D Sc cutoff v w) :
    truncatedRightContext D Sc cutoff N σ v w
      ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ)).mkQ
        (rightContext D Sc cutoff σ v w f) := rfl

/-- Append an arbitrary word, without changing coefficients or their cutoff. -/
def truncatedAppend (σ : List I) :
    TruncatedCategory D Sc cutoff N ⥤ TruncatedCategory D Sc cutoff N where
  obj v := ⟨v.word ++ σ⟩
  map {v w} := truncatedRightContext D Sc cutoff N σ v.word w.word
  map_id v := congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ
    (rightContext_id D Sc cutoff σ v.word)
  map_comp {v w z} f g := by
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (truncatedIdeal D Sc cutoff N w.word z.word).mkQ_surjective g
    exact congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ
      (rightContext_comp D Sc cutoff σ f g)

instance truncatedAppend_additive (σ : List I) :
    (truncatedAppend D Sc cutoff N σ).Additive where
  map_add := map_add (truncatedRightContext D Sc cutoff N σ _ _) _ _

instance truncatedAppend_linear (σ : List I) :
    Functor.Linear k (truncatedAppend D Sc cutoff N σ) where
  map_smul f c := map_smul (truncatedRightContext D Sc cutoff N σ _ _) c f

theorem rightContext_proj (σ : List I) {v w : List I} (p : ZMod 2)
    (f : hom D Sc cutoff v w) :
    rightContext D Sc cutoff σ v w (Supercategory.proj k p f) =
      Supercategory.proj k p (rightContext D Sc cutoff σ v w f) := by
  induction f using BoxProd.induction_on_homogeneous with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul q r a f ha hf =>
    have hs := BoxProd.tmul_mem_parity ha hf
    have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff (v ++ σ))
      (Y := obj D Sc cutoff (w ++ σ)) ha
      (MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D σ)) hf)
    by_cases h : q + r = p
    · subst p
      rw [Supercategory.proj_of_mem hs]
      exact (Supercategory.proj_of_mem ht).symm
    · rw [Supercategory.proj_of_mem_ne hs h, map_zero]
      exact (Supercategory.proj_of_mem_ne ht h).symm

theorem rightContext_mem_parity (σ : List I) {v w : List I} {p : ZMod 2}
    {f : hom D Sc cutoff v w}
    (hf : f ∈ Supercategory.parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) p) :
    rightContext D Sc cutoff σ v w f ∈ Supercategory.parity (R := k)
      (obj D Sc cutoff (v ++ σ)) (obj D Sc cutoff (w ++ σ)) p := by
  apply Supercategory.mem_iff_proj.mpr
  rw [← rightContext_proj, Supercategory.proj_of_mem hf]

instance truncatedAppend_super (σ : List I) :
    IsSuperfunctor k (truncatedAppend D Sc cutoff N σ) where
  map_mem := by
    rintro v w p f ⟨a, ha, rfl⟩
    exact Submodule.mem_map_of_mem (rightContext_mem_parity D Sc cutoff σ ha)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem rightContext_mem_degree (σ : List I) {v w : List I} {n : ℤ}
    {f : hom D Sc cutoff v w} (hf : f ∈ elvHomDegree D sy Sc hc cutoff v w n) :
    rightContext D Sc cutoff σ v w f ∈
      elvHomDegree D sy Sc hc cutoff (v ++ σ) (w ++ σ) n := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  refine BoxProd.map_mem_of_homDeg (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) (rightContext D Sc cutoff σ v w) _ ?_ hf
  intro r s hrs a ha g hg
  subst n
  exact BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff (v ++ σ))
    (Y := obj D Sc cutoff (w ++ σ)) ha
    (GradedMonoidalSupercategory.whiskerRight_mem_degree ((pres D Sc).obj (ob D σ)) hg)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Appended affine transformations

Affine morphisms on the appended word act by left whiskering. Their
supernaturality uses total coefficient-plus-diagram parity.
-/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed affine morphism on the right of a word. -/
def appendComponent {σ τ : List I}
    (h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) (v : List I) :
    hom D Sc cutoff (v ++ σ) (v ++ τ) :=
  (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((pres D Sc).obj (ob D v) ◁ h)

theorem appendComponent_mem {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (v : List I) :
    appendComponent D Sc cutoff h v ∈ parity (R := k)
      (obj D Sc cutoff (v ++ σ)) (obj D Sc cutoff (v ++ τ)) p := by
  have he := BoxProd.tmul_mem_parity (X := obj D Sc cutoff (v ++ σ))
    (Y := obj D Sc cutoff (v ++ τ))
    (Supercategory.id_mem (R := k) (obj D Sc cutoff v).fst)
    (MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D v)) hh)
  rw [zero_add] at he
  exact he

private theorem box_append_naturality
    {A : Type*} {C : Type u} [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [MonoidalCategoryStruct C] [MonoidalSupercategory k C]
    (a₀ : A) {V W S T : C} {p q r : ZMod 2}
    {h : S ⟶ T} (hh : h ∈ parity (R := k) _ _ p)
    (a : a₀ ⟶ a₀) (g : V ⟶ W)
    (ha : a ∈ parity (R := k) _ _ q) (hg : g ∈ parity (R := k) _ _ r) :
    BoxProd.tmulHom (k := k) (X := ⟨a₀, V ⊗ S⟩) (Y := ⟨a₀, W ⊗ S⟩) a (g ▷ S) ≫
      BoxProd.tmulHom (k := k) (X := ⟨a₀, W ⊗ S⟩) (Y := ⟨a₀, W ⊗ T⟩) (𝟙 a₀) (W ◁ h) =
    koszulSign p (q + r) • (BoxProd.tmulHom (k := k)
      (X := ⟨a₀, V ⊗ S⟩) (Y := ⟨a₀, V ⊗ T⟩) (𝟙 a₀) (V ◁ h) ≫
      BoxProd.tmulHom (k := k) (X := ⟨a₀, V ⊗ T⟩) (Y := ⟨a₀, W ⊗ T⟩) a (g ▷ T)) := by
  rw [BoxProd.tmulHom_comp_tmulHom ha _ _
    (MonoidalSupercategory.whiskerLeft_mem _ hh),
    BoxProd.tmulHom_comp_tmulHom (X := ⟨a₀, V ⊗ S⟩)
      (Y := ⟨a₀, V ⊗ T⟩) (Z := ⟨a₀, W ⊗ T⟩)
      (Supercategory.id_mem (R := k) a₀) _ _
      (MonoidalSupercategory.whiskerRight_mem _ hg),
    koszulSign_zero_left, one_smul, Category.comp_id, Category.id_comp,
    MonoidalSupercategory.super_interchange hg hh]
  simp only [BoxProd.tmulHom_def, TensorProduct.tmul_smul, smul_smul]
  congr 1
  rw [koszulSign_add_right, koszulSign_comm p q, koszulSign_comm p r]

/-- The sign includes exterior coefficient parity, not only affine parity. -/
theorem appendComponent_naturality_tmul {σ τ v w : List I} {p q r : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p)
    (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
    (g : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (ha : a ∈ parity (R := k) _ _ q) (hg : g ∈ parity (R := k) _ _ r) :
    rightContext D Sc cutoff σ v w (a ⊗ₜ[k] g) ≫ appendComponent D Sc cutoff h w =
      koszulSign p (q + r) • (appendComponent D Sc cutoff h v ≫
        rightContext D Sc cutoff τ v w (a ⊗ₜ[k] g)) := by
  have he := box_append_naturality
    (C := H D Sc) (obj D Sc cutoff v).fst
    (V := (pres D Sc).obj (ob D v)) (W := (pres D Sc).obj (ob D w))
    (S := (pres D Sc).obj (ob D σ)) (T := (pres D Sc).obj (ob D τ)) hh a g ha hg
  exact he

theorem appendComponent_naturality_proj {σ τ v w : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (s : ZMod 2) (f : hom D Sc cutoff v w) :
    rightContext D Sc cutoff σ v w (proj k s f) ≫ appendComponent D Sc cutoff h w =
      koszulSign p s • (appendComponent D Sc cutoff h v ≫
        rightContext D Sc cutoff τ v w (proj k s f)) := by
  induction f using BoxProd.induction_on_homogeneous with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]
  | add f g hf hg =>
    simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg, smul_add]
  | tmul q r a g ha hg =>
    have ht := BoxProd.tmul_mem_parity ha hg
    by_cases hs : q + r = s
    · subst s
      rw [proj_of_mem ht]
      exact appendComponent_naturality_tmul D Sc cutoff hh a g ha hg
    · rw [proj_of_mem_ne ht hs]
      simp only [map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]

theorem appendComponent_naturality {σ τ v w : List I} {p q : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) {f : hom D Sc cutoff v w}
    (hf : f ∈ parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) q) :
    rightContext D Sc cutoff σ v w f ≫ appendComponent D Sc cutoff h w =
      koszulSign p q • (appendComponent D Sc cutoff h v ≫
        rightContext D Sc cutoff τ v w f) := by
  have he := appendComponent_naturality_proj D Sc cutoff hh q f
  rwa [proj_of_mem hf] at he

variable (N : ℕ)

/-- The quotient class of the appended affine morphism. -/
def truncatedAppendComponent {σ τ : List I}
    (h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppend D Sc cutoff N σ).obj v ⟶
      (truncatedAppend D Sc cutoff N τ).obj v :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ (appendComponent D Sc cutoff h v.word)

/-- Every homogeneous affine morphism gives a supernatural right-append transformation. -/
theorem truncatedAppendComponent_supernatural {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    IsSupernatural k p (truncatedAppendComponent D Sc cutoff N h) where
  mem v := Submodule.mem_map_of_mem (appendComponent_mem D Sc cutoff hh v.word)
  naturality := by
    rintro v w q f ⟨a, ha, rfl⟩
    have he := congrArg (truncatedIdeal D Sc cutoff N (v.word ++ σ) (w.word ++ τ)).mkQ
      (appendComponent_naturality D Sc cutoff hh ha)
    rw [map_zsmul, koszulSign_smul (R := k)] at he
    exact he

/-- The affine right-append transformation, retaining its specified parity. -/
def truncatedAppendTransform {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (truncatedAppend D Sc cutoff N σ) (truncatedAppend D Sc cutoff N τ) :=
  (truncatedAppendComponent_supernatural D Sc cutoff N hh).toSuperNatTrans

/-- The appended dot is the prescribed last-strand affine dot. -/
def truncatedAppendDot (i : I) :
    SuperNatTrans k (truncatedAppend D Sc cutoff N [i]) (truncatedAppend D Sc cutoff N [i]) :=
  truncatedAppendTransform D Sc cutoff N (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The appended crossing retains the source and target colour order. -/
def truncatedAppendCross (i j : I) :
    SuperNatTrans k (truncatedAppend D Sc cutoff N [i, j])
      (truncatedAppend D Sc cutoff N [j, i]) :=
  truncatedAppendTransform D Sc cutoff N (crossTwo_mem D Sc i j)

@[simp] theorem truncatedAppendDot_app (i : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v =
      truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) v := by
  simp only [truncatedAppendDot, truncatedAppendTransform,
    IsSupernatural.toSuperNatTrans, ↓reduceIte]

@[simp] theorem truncatedAppendCross_app (i j : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendCross D Sc cutoff N i j).app (D.parity i * D.parity j) v =
      truncatedAppendComponent D Sc cutoff N (crossTwo D Sc i j) v := by
  simp only [truncatedAppendCross, truncatedAppendTransform,
    IsSupernatural.toSuperNatTrans, ↓reduceIte]

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem appendComponent_mem_degree {σ τ : List I} {n : ℤ}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ homDegree D sy Sc σ τ n) (v : List I) :
    appendComponent D Sc cutoff h v ∈
      elvHomDegree D sy Sc hc cutoff (v ++ σ) (v ++ τ) n := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  have he := BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff (v ++ σ))
    (Y := obj D Sc cutoff (v ++ τ))
    (GradedSupercategory.id_mem_degree (R := k) (obj D Sc cutoff v).fst)
    (GradedMonoidalSupercategory.whiskerLeft_mem_degree ((pres D Sc).obj (ob D v)) hh)
  rw [zero_add] at he
  exact he

theorem truncatedAppendComponent_mem_degree {σ τ : List I} {n : ℤ}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ homDegree D sy Sc σ τ n) (v : TruncatedCategory D Sc cutoff N) :
    truncatedAppendComponent D Sc cutoff N h v ∈
      truncatedDegree D Sc cutoff sy hc N (v.word ++ σ) (v.word ++ τ) n :=
  Submodule.mem_map_of_mem (appendComponent_mem_degree D Sc cutoff sy hc hh v.word)

theorem truncatedAppendDot_degree (i : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v ∈
      truncatedDegree D Sc cutoff sy hc N (v.word ++ [i]) (v.word ++ [i])
        (2 * sy.d i) := by
  rw [truncatedAppendDot_app]
  apply truncatedAppendComponent_mem_degree
  unfold dotE genE
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_gdeg_mkD]
    simp [pl, PG.ld, gdeg]
  · exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELV
end

end
