/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PrependBasis
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates

/-!
# Matrix entries of prepend PBW terms

The matrix multiplication formula identifies the affine prepend expansion
with the scalar Hom diagrams. This is the entrywise step towards coordinates
on the whole prepend corner as a right module over the old algebra.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The diagonal dot acts on the target of a single matrix entry. -/
theorem affineFirstDot_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) :
    affineFirstDot D Sc i n * FiniteHomMatrix.single (prependWord i t) (prependWord i s) f =
      FiniteHomMatrix.single (prependWord i t) (prependWord i s)
        (f ≫ inductionFirstDot D Sc i t) := by
  rw [affineFirstDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (prependWord_injective i n h)) _ _
  · simp

/-- Powers include exponent zero in the ambient algebra, without replacing its unit. -/
theorem affineFirstDot_pow_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) (m : ℕ) :
    affineFirstDot D Sc i n ^ m * FiniteHomMatrix.single (prependWord i t) (prependWord i s) f =
      FiniteHomMatrix.single (prependWord i t) (prependWord i s)
        (f ≫ inductionFirstDot D Sc i t ^ m) := by
  induction m with
  | zero => simp [End.one_def]
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, affineFirstDot_mul_single]
    congr 1
    rw [pow_succ', End.mul_def, Category.assoc]

/-- Multiplication by the moving crossing selects the old target word. -/
theorem prependShuffleElement_mul_single (i : I) {n : ℕ} (u : PrependShuffle n)
    (s t : Word I n)
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) :
    prependShuffleElement D Sc i u *
        FiniteHomMatrix.single (prependWord i t) (prependWord i s) f =
      FiniteHomMatrix.single (prependShuffleTarget i u t) (prependWord i s)
        (f ≫ prependShuffleHom D Sc i u t) := by
  rw [prependShuffleElement, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (prependWord_injective i n h)) _ _
  · simp

/-- The coefficient morphism acts first, then the new dots, then the moving crossing. -/
theorem prependPBWTerm_single (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (s t : Word I n) (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    prependPBWTerm D Sc i u m (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single (prependShuffleTarget i u t) (prependWord i s)
        (prependHom D Sc i s t f ≫ (inductionFirstDot D Sc i t ^ m) ≫
          prependShuffleHom D Sc i u t) := by
  unfold prependPBWTerm
  change (_ * _) * prependLinear D Sc i n (FiniteHomMatrix.single t s f) = _
  rw [prependLinear_single, mul_assoc, affineFirstDot_pow_mul_single,
    prependShuffleElement_mul_single, Category.assoc]

/-- The intermediate old target as a word of the original height. -/
def PrependIdx.oldWord {i : I} {s t : List I} (x : PrependIdx i s t) : Word I s.length :=
  ⟨x.oldTarget, by simp [PrependIdx.oldTarget]⟩

/-- The target word has one more strand than the old source. -/
def PrependIdx.targetWord {i : I} {s t : List I} (x : PrependIdx i s t) :
    Word I (s.length + 1) :=
  ⟨t, by rw [← x.moving_target]; simp [PrependIdx.oldTarget]⟩

omit [Fintype I] in
/-- The first dot is the positioned dot at zero. -/
theorem inductionFirstDot_eq_dotE (i : I) {n : ℕ} (s : Word I n) :
    inductionFirstDot D Sc i s = dotE D Sc (i :: s.1) 0 := by
  simp [inductionFirstDot, inductionStrandDot, dotE_eq, cl, wordObj,
    Presentation.diag_whiskerRight, pl, PG.ld]
  exact Presentation.diag_eq_of_layers_eq _ rfl

omit [Fintype I] in
private theorem matrix_single_heq {n : ℕ} {s t t' : Word I n}
    {f : wordObj D Sc s ⟶ wordObj D Sc t} {g : wordObj D Sc s ⟶ wordObj D Sc t'}
    (h : t = t') (hf : HEq f g) :
    FiniteHomMatrix.single t s f = FiniteHomMatrix.single t' s g := by
  subst t'
  cases hf
  rfl

omit [Fintype I] in
private theorem cl_target_heq {s t t' : List I} {l l' : List PG}
    (ht : t = t') (hl : l = l') (h : SChain s (pl s l) t)
    (h' : SChain s (pl s l') t') : HEq (cl D Sc s t l h) (cl D Sc s t' l' h') := by
  subst t'
  subst l'
  rfl

/-- A scalar prepend basis element is exactly the corresponding matrix PBW term. -/
theorem prependPBWTerm_old_nf {i : I} {s t : List I} (x : PrependIdx i s t) :
    prependPBWTerm D Sc i x.1.2.2.2 x.1.1
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)) =
    FiniteHomMatrix.single x.targetWord (prependWord i ⟨s, rfl⟩) (prependElt D Sc x) := by
  rw [prependPBWTerm_single, inductionFirstDot_eq_dotE, dotE_pow]
  apply matrix_single_heq D Sc (Subtype.ext x.moving_target)
  change HEq (((pres D Sc).obj (ob D [i]) ◁ x.old.nf) ≫ _ ≫ _) _
  rw [whiskerLeft_nf]
  simp only [List.singleton_append]
  unfold prependShuffleHom
  dsimp only [PrependIdx.oldWord, PrependIdx.old]
  rw [cl_comp, cl_comp]
  unfold prependElt
  apply cl_target_heq D Sc x.moving_target
  simp [PrependIdx.gens, List.map_append, cw_map_shift, List.map_replicate,
    List.append_assoc]

end OddMath.QuiverHecke
