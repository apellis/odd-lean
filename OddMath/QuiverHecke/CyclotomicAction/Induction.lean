/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Quotient
import OddMath.QuiverHecke.ShuffleBasis
import Categorification.Algebra.InductionAlong

/-!
# Strand inclusion for cyclotomic induction

Ports the strand-inclusion input from
`Categorification/KLR/CyclotomicAbsentColour.lean` and
`Categorification/KLR/CyclotomicAction/Induction.lean`. The map adds a rightmost
strand to the existing Hom algebra. Its image of the identity is a colour-cut
idempotent, so it is not asserted to be unital.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Append the induction colour to a word. -/
def appendWord (i : I) {n : ℕ} (w : Word I n) : Word I (n + 1) :=
  ⟨w.1 ++ [i], by simp [w.2]⟩

theorem appendWord_injective (i : I) (n : ℕ) : Function.Injective (appendWord i (n := n)) := by
  intro a b h
  apply Subtype.ext
  exact List.append_cancel_right (congrArg Subtype.val h)

/-- Appending an identity strand to an individual Hom entry. -/
def appendHom (i : I) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k]
      (wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) where
  toFun f := f ▷ (pres D Sc).obj (ob D [i])
  map_add' f g := MonoidalSupercategory.add_whiskerRight (R := k) f g _
  map_smul' c f := MonoidalSupercategory.smul_whiskerRight (R := k) c f _

@[simp] theorem appendHom_comp (i : I) {n : ℕ} (r s t : Word I n)
    (f : wordObj D Sc r ⟶ wordObj D Sc s) (g : wordObj D Sc s ⟶ wordObj D Sc t) :
    appendHom D Sc i r t (f ≫ g) = appendHom D Sc i r s f ≫ appendHom D Sc i s t g :=
  MonoidalSupercategory.comp_whiskerRight (R := k) f g ((pres D Sc).obj (ob D [i]))

/-- The single-entry linear inclusion. -/
def appendEntry (i : I) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc (n + 1) where
  toFun f := FiniteHomMatrix.single (appendWord i t) (appendWord i s)
    (appendHom D Sc i s t f)
  map_add' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_add]
  map_smul' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_smul]

/-- The affine nonunital inclusion, extended entrywise and linearly. -/
def appendLinear (i : I) (n : ℕ) : Hn D Sc n →ₗ[k] Hn D Sc (n + 1) :=
  DFinsupp.lsum k fun p => appendEntry D Sc i p.2 p.1

@[simp] theorem appendLinear_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    appendLinear D Sc i n (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s) (appendHom D Sc i s t f) := by
  let : DecidableEq (Word I n) := Classical.decEq _
  let : DecidableEq (Word I (n + 1)) := Classical.decEq _
  exact DFinsupp.lsum_single (S := k)
    (fun p : Word I n × Word I n => appendEntry D Sc i p.2 p.1) (t, s) f

theorem appendLinear_mul (i : I) (n : ℕ) (a b : Hn D Sc n) :
    appendLinear D Sc i n (a * b) = appendLinear D Sc i n a * appendLinear D Sc i n b := by
  induction a using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [add_mul, ha, hb]
  | hs s t f =>
    induction b using FiniteHomMatrix.induction with
    | hz => simp
    | ha a b ha hb => simp [mul_add, ha, hb]
    | hs r q g =>
      by_cases h : t = r
      · subst r
        simp
      · have h' : appendWord i t ≠ appendWord i r := fun e => h (appendWord_injective i n e)
        simp [FiniteHomMatrix.single_mul_single_of_ne, h, h']

/-- The multiplication law is inherited from actual whiskering of diagrams. -/
def appendAlgebra (i : I) (n : ℕ) : Hn D Sc n →ₙₐ[k] Hn D Sc (n + 1) where
  toFun := appendLinear D Sc i n
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := appendLinear_mul D Sc i n

/-- Right whiskering is unital on each individual endomorphism ring. -/
def appendEnd (i : I) {n : ℕ} (w : Word I n) :
    End (wordObj D Sc w) →ₐ[k] End (wordObj D Sc (appendWord i w)) :=
  AlgHom.ofLinearMap (appendHom D Sc i w w)
    (MonoidalSupercategory.id_whiskerRight (R := k) (wordObj D Sc w)
      ((pres D Sc).obj (ob D [i])))
    (fun x y => appendHom_comp D Sc i w w w y x)

@[simp] theorem appendEnd_dot (i : I) {n : ℕ} (w : Word I (n + 1)) :
    appendEnd D Sc i w (dotE D Sc w.1 0) = dotE D Sc (appendWord i w).1 0 := by
  change dotE D Sc w.1 0 ▷ (pres D Sc).obj (ob D [i]) = _
  simp only [dotE_eq]
  erw [cl_whiskerRight]
  · rfl
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [PG.pos, PG.width, w.2]

variable [Fintype I]

omit [Fintype I] in
@[simp] theorem appendAlgebra_generator (i : I) (a : I → _root_.Polynomial k)
    {n : ℕ} (w : Word I (n + 1)) :
    appendAlgebra D Sc i (n + 1) (cyclotomicGenerator D Sc a w) =
      cyclotomicGenerator D Sc a (appendWord i w) := by
  change appendLinear D Sc i (n + 1) (FiniteHomMatrix.single w w _) = _
  rw [appendLinear_single]
  change FiniteHomMatrix.single _ _ (appendEnd D Sc i w
    (_root_.Polynomial.aeval (R := k) (dotE D Sc w.1 0) _)) = _
  erw [← _root_.Polynomial.aeval_algHom_apply, appendEnd_dot]
  congr 2
  apply congrArg a
  simp [appendWord, List.get_eq_getElem, List.getElem_append_left, w.2]

/-- The affine inclusion preserves the actual two-sided cyclotomic ideal. -/
theorem appendAlgebra_mem_ideal (i : I) (a : I → _root_.Polynomial k) (n : ℕ)
    {z : Hn D Sc (n + 1)} (hz : z ∈ cyclotomicIdeal D Sc a n) :
    appendAlgebra D Sc i (n + 1) z ∈ cyclotomicIdeal D Sc a (n + 1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, b, rfl⟩ := hz
    rw [map_mul, appendAlgebra_generator]
    exact Submodule.subset_span ⟨appendWord i w, appendAlgebra D Sc i (n + 1) b, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    change appendAlgebra D Sc i (n + 1) (c * x) ∈ _
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ hx

/-- Strand inclusion descends to the actual cyclotomic quotients. -/
def cyclotomicAppendLinear (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    CyclotomicAlgebra D Sc a n →ₗ[k] CyclotomicAlgebra D Sc a (n + 1) :=
  (cyclotomicIdeal D Sc a n).restrictScalars k |>.mapQ
    ((cyclotomicIdeal D Sc a (n + 1)).restrictScalars k)
    (appendLinear D Sc i (n + 1)) (fun _ hz => appendAlgebra_mem_ideal D Sc i a n hz)

@[simp] theorem cyclotomicAppendLinear_mk (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) (z : Hn D Sc (n + 1)) :
    cyclotomicAppendLinear D Sc i a n (cyclotomicMk D Sc a n z) =
      cyclotomicMk D Sc a (n + 1) (appendAlgebra D Sc i (n + 1) z) := rfl

/-- The descended inclusion respects multiplication, but need not preserve one. -/
def cyclotomicAppend (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :
    CyclotomicAlgebra D Sc a n →ₙₐ[k] CyclotomicAlgebra D Sc a (n + 1) where
  toFun := cyclotomicAppendLinear D Sc i a n
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change cyclotomicAppendLinear D Sc i a n
      (cyclotomicMk D Sc a n x * cyclotomicMk D Sc a n y) = _
    rw [← map_mul, cyclotomicAppendLinear_mk, map_mul, map_mul]
    rfl

/-- Induction on underlying modules. Odd transformations require the super
module enhancement and are not ordinary natural transformations here. -/
abbrev cyclotomicInduction (i : I) (a : I → _root_.Polynomial k) (n : ℕ) :=
  Categorification.InductionAlong.functor
    (cyclotomicAppend D Sc i a n :
      CyclotomicAlgebra D Sc a n →ₙ+* CyclotomicAlgebra D Sc a (n + 1))

end OddMath.QuiverHecke
