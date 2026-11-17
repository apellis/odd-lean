import Mathlib.LinearAlgebra.DirectSum.Finsupp
import OddMath.QuiverHecke.Basis
import OddMath.QuiverHecke.CyclotomicAction.CoefficientTransport.CyclotomicTarget
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRight.IntertwinerRightDot
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.InputParabolic
import OddMath.QuiverHecke.PrependBasis
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Prepend coordinates

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Prepend PBW expansion in the Hom algebra

The expansion generators for the input-side decomposition used in KKO I,
arXiv:1206.5933v2, Lemma 8.1. `prependPBWTerm_right` checks the right-old-algebra
compatibility on the original affine algebra, and `prependPBWTerm_corner`
checks the original induction corner. Bijectivity is a written argument in
`docs/Nondegeneracy/PrependCoordinates.md`, not a theorem of this module.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- The target word after moving the first strand along an inverse shuffle. -/
def prependShuffleTarget (i : I) {n : ℕ} (u : PrependShuffle n) (s : Word I n) :
    Word I (n + 1) :=
  ⟨tgt (i :: s.1) (cw (canWord (n + 1) u.1⁻¹)), by simp [s.2]⟩

/-- The reduced crossing diagram moving the prepended strand. -/
def prependShuffleHom (i : I) {n : ℕ} (u : PrependShuffle n) (s : Word I n) :
    wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependShuffleTarget i u s) :=
  cl D Sc (i :: s.1) _ (cw (canWord (n + 1) u.1⁻¹)) (sChain_pl _ _)

/-- Sum over old words, not over colours of a selected matrix entry. -/
def prependShuffleElement (i : I) {n : ℕ} (u : PrependShuffle n) : Hn D Sc (n + 1) :=
  ∑ s : Word I n, FiniteHomMatrix.single (prependShuffleTarget i u s) (prependWord i s)
    (prependShuffleHom D Sc i u s)

/-- A coefficient acts first, followed by new dots and the moving crossings. -/
def prependPBWTerm (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b : Hn D Sc n) : Hn D Sc (n + 1) :=
  prependShuffleElement D Sc i u * affineFirstDot D Sc i n ^ m * prependAlgebra D Sc i n b

/-- Right coefficients require associativity, not centrality or a parity assumption. -/
theorem prependPBWTerm_right (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b r : Hn D Sc n) :
    prependPBWTerm D Sc i u m (b * r) =
      prependPBWTerm D Sc i u m b * prependAlgebra D Sc i n r := by
  simp only [prependPBWTerm, map_mul, mul_assoc]

/-- Every expansion term belongs to the original prepend corner. -/
theorem prependPBWTerm_corner (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b : Hn D Sc n) :
    prependPBWTerm D Sc i u m b * prependAlgebra D Sc i n 1 =
      prependPBWTerm D Sc i u m b := by
  simp only [prependPBWTerm, mul_assoc, ← map_mul, mul_one]

/-- The same term as an element of the induction corner, with no replacement algebra. -/
def prependPBWCorner (i : I) {n : ℕ} (u : PrependShuffle n) (m : ℕ)
    (b : Hn D Sc n) :
    InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  ⟨prependPBWTerm D Sc i u m b, prependPBWTerm_corner D Sc i u m b⟩

end OddMath.QuiverHecke
end

end

section

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

/-- Every allowed matrix entry has a finite expansion by prescribed PBW terms.
The coefficients here are scalar multiples of single old normal forms; regrouping
these terms into unique old-algebra coefficients is a separate step. -/
theorem prepend_single_expansion (i : I) (s : List I) (t : Word I (s.length + 1))
    (f : wordObj D Sc (prependWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t (prependWord i ⟨s, rfl⟩) f =
      ((prependBasis D Sc (i := i) (s := s) (t := t.1)).repr f).sum
        (fun x c => c • prependPBWTerm D Sc i x.1.2.2.2 x.1.1
          (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩
            (NFIdx.nf (D := D) (Sc := Sc) x.old))) := by
  let L : (wordObj D Sc (prependWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) →ₗ[k]
      Hn D Sc (s.length + 1) :=
    { toFun := FiniteHomMatrix.single t (prependWord i ⟨s, rfl⟩)
      map_add' := FiniteHomMatrix.single_add _ _
      map_smul' := fun c g => FiniteHomMatrix.single_smul _ _ c g }
  have h := congrArg L ((prependBasis D Sc (i := i) (s := s) (t := t.1)).linearCombination_repr f)
  change L f = _
  rw [← h]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    prependBasis_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (_ • ·)
  exact (prependPBWTerm_old_nf D Sc x).symm

end OddMath.QuiverHecke
end

end

section

/-!
# Whole affine prepend-corner coordinates

For KKO I, arXiv:1206.5933v2, Lemma 8.1, `prependCoordinateEquiv` identifies
finite old-algebra coefficient families with the original prepend corner.
`prependCoefficients_expansion` proves uniqueness using the scalar prepend
basis and the old normal-form basis. `prependExpansion_projection` proves
existence by finite matrix entries. The forward map is the literal sum of
`prependPBWCorner`; both directions respect the existing right old-algebra
action. Balanced tensor descent and cancellation remain separate steps.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Literal finite old-algebra coefficient expansion in the ambient algebra. -/
def prependExpansion (i : I) (n : ℕ) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) →ₗ[k] Hn D Sc (n + 1) :=
  Finsupp.lsum k fun q =>
    { toFun := prependPBWTerm D Sc i q.1 q.2
      map_add' := by intros; simp [prependPBWTerm, map_add, mul_add]
      map_smul' := by intros; simp [prependPBWTerm, map_smul] }

@[simp] theorem prependExpansion_single (i : I) (n : ℕ)
    (q : PrependShuffle n × ℕ) (b : Hn D Sc n) :
    prependExpansion D Sc i n (Finsupp.single q b) = prependPBWTerm D Sc i q.1 q.2 b :=
  Finsupp.lsum_single _ _ _ _

/-- Regroup one scalar Hom expansion into finite old-algebra coefficients. -/
def prependEntryCoefficients (i : I) (s : List I) (t : Word I (s.length + 1)) :
    (wordObj D Sc (prependWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) →ₗ[k]
      ((PrependShuffle s.length × ℕ) →₀ Hn D Sc s.length) :=
  (Finsupp.linearCombination k (fun x : PrependIdx i s t.1 =>
    Finsupp.single (x.1.2.2.2, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)))).comp
    (prependBasis D Sc (i := i) (s := s) (t := t.1)).repr.toLinearMap

/-- Regrouping retains the actual single-entry matrix, not merely its span. -/
theorem prependExpansion_entry (i : I) (s : List I) (t : Word I (s.length + 1))
    (f : wordObj D Sc (prependWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) :
    prependExpansion D Sc i s.length (prependEntryCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (prependWord i ⟨s, rfl⟩) f := by
  rw [prepend_single_expansion D Sc i s t f]
  simp [prependEntryCoefficients, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    prependPBWTerm]
  rfl

/-- The same entry regrouping at a fixed height. -/
def prependWordCoefficients (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1)) :
    (wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) →ₗ[k]
      ((PrependShuffle n × ℕ) →₀ Hn D Sc n) := by
  rcases s with ⟨s, hs⟩
  subst n
  exact prependEntryCoefficients D Sc i s t

theorem prependExpansion_word (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) :
    prependExpansion D Sc i n (prependWordCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (prependWord i s) f := by
  rcases s with ⟨s, hs⟩
  subst n
  exact prependExpansion_entry D Sc i s t f

/-- Finite matrix-entry assembly of the old-algebra coefficients. -/
def prependCoefficients (i : I) (n : ℕ) : Hn D Sc (n + 1) →ₗ[k]
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) :=
  ∑ s : Word I n, ∑ t : Word I (n + 1),
    (prependWordCoefficients D Sc i s t).comp
      (DFinsupp.lapply (t, prependWord i s))

/-- Reassembly is the projection onto the allowed columns. -/
theorem prependExpansion_coefficients (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    prependExpansion D Sc i n (prependCoefficients D Sc i n a) =
      ∑ s : Word I n, ∑ t : Word I (n + 1),
        FiniteHomMatrix.single t (prependWord i s) (a (t, prependWord i s)) := by
  simp [prependCoefficients, map_sum, prependExpansion_word]

/-- The old normal form and a chosen shuffle specify one prepend index. -/
def prependIndex (i : I) {s t : List I} (y : NFIdx s t)
    (q : PrependShuffle s.length × ℕ) :
    PrependIdx i s (prependShuffleTarget i q.1 ⟨t, by
      rw [← y.tgt_cw]; simp⟩).1 :=
  ⟨(q.2, y.1.1, y.1.2, q.1), y.2.1, y.2.2.1, by
    have he := tgt_shift [i] s (cw (canWord s.length y.1.2))
    simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
    simp only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
    rfl⟩

theorem prependCoefficients_single (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) :
    prependCoefficients D Sc i n (FiniteHomMatrix.single t (prependWord i s) f) =
      prependWordCoefficients D Sc i s t f := by
  classical
  simp only [prependCoefficients, LinearMap.sum_apply, LinearMap.comp_apply,
    DFinsupp.lapply_apply]
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single t]
    · simp [FiniteHomMatrix.single]
    · intro b _ hb
      simp [FiniteHomMatrix.single, Ne.symm hb]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    have h : prependWord i s ≠ prependWord i b := fun h => hb ((prependWord_injective i n h).symm)
    simp [FiniteHomMatrix.single, h]
  · simp

theorem prependCoefficients_old_nf {i : I} {s t : List I} (x : PrependIdx i s t) :
    prependCoefficients D Sc i s.length
      (prependPBWTerm D Sc i x.1.2.2.2 x.1.1
        (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old))) =
    Finsupp.single (x.1.2.2.2, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)) := by
  rw [prependPBWTerm_old_nf, prependCoefficients_single]
  change prependEntryCoefficients D Sc i s x.targetWord (prependElt D Sc x) = _
  rw [← prependBasis_apply D Sc x]
  simp only [prependEntryCoefficients, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [Module.Basis.repr_self]
  simp only [Finsupp.linearCombination_single, one_smul]

theorem prependCoefficients_nf (i : I) (s : List I) (t : Word I s.length)
    (y : NFIdx s t.1) (q : PrependShuffle s.length × ℕ) :
    prependCoefficients D Sc i s.length
      (prependPBWTerm D Sc i q.1 q.2
        (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y))) =
      Finsupp.single q (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y)) := by
  rcases t with ⟨t, ht⟩
  have he := y.tgt_cw
  rcases y with ⟨⟨L, v⟩, hy⟩
  change tgt s (cw (canWord s.length v)) = t at he
  subst t
  simpa [prependIndex, PrependIdx.oldWord, PrependIdx.old, PrependIdx.oldTarget] using
    prependCoefficients_old_nf D Sc (prependIndex i ⟨(L, v), hy⟩ q)

theorem prependCoefficients_term (i : I) {n : ℕ} (q : PrependShuffle n × ℕ)
    (b : Hn D Sc n) :
    prependCoefficients D Sc i n (prependPBWTerm D Sc i q.1 q.2 b) = Finsupp.single q b := by
  let P : Hn D Sc n →ₗ[k] Hn D Sc (n + 1) :=
    (prependExpansion D Sc i n).comp (Finsupp.lsingle q)
  rw [← prependExpansion_single D Sc i n q b]
  change prependCoefficients D Sc i n (P b) = Finsupp.single q b
  induction b using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs t s f =>
    let E : (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc n :=
      { toFun := FiniteHomMatrix.single t s
        map_add' := FiniteHomMatrix.single_add _ _
        map_smul' := fun c g => FiniteHomMatrix.single_smul _ _ c g }
    have h : ((prependCoefficients D Sc i n).comp P).comp E =
        (Finsupp.lsingle q).comp E := by
      apply (basisNF D Sc s.1 t.1).ext
      intro y
      simp only [LinearMap.comp_apply, P, Finsupp.lsingle_apply, prependExpansion_single,
        basisNF_apply, E, LinearMap.coe_mk, AddHom.coe_mk]
      rcases s with ⟨s, hs⟩
      subst n
      exact prependCoefficients_nf D Sc i s t y q
    exact LinearMap.congr_fun h f

/-- Scalar prepend independence recovers every old-algebra coefficient. -/
theorem prependCoefficients_expansion (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) :
    prependCoefficients D Sc i n (prependExpansion D Sc i n b) = b := by
  have h : (prependCoefficients D Sc i n).comp (prependExpansion D Sc i n) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro q b
    simpa only [LinearMap.comp_apply, prependExpansion_single, LinearMap.id_apply] using
      prependCoefficients_term D Sc i q b
  exact LinearMap.congr_fun h b

/-- Uniqueness holds for coefficients in the whole old algebra. -/
theorem prependExpansion_injective (i : I) (n : ℕ) :
    Function.Injective (prependExpansion D Sc i n) :=
  Function.LeftInverse.injective (prependCoefficients_expansion D Sc i n)

private theorem matrix_mul_idem_sum {n : ℕ} (a : Hn D Sc n) (s : Word I n) :
    a * FiniteHomMatrix.idem s =
      ∑ t : Word I n, FiniteHomMatrix.single t s (a (t, s)) := by
  classical
  induction a using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [add_mul, ha, hb, DFinsupp.add_apply,
      Finset.sum_add_distrib]
  | hs t r f =>
    by_cases h : r = s
    · subst r
      rw [FiniteHomMatrix.single_mul_idem]
      symm
      rw [Finset.sum_eq_single t]
      · simp [FiniteHomMatrix.single]
      · intro b _ hb
        simp [FiniteHomMatrix.single, Ne.symm hb]
      · simp
    · rw [FiniteHomMatrix.idem, FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ h]
      symm
      apply Finset.sum_eq_zero
      intro b _
      simp [FiniteHomMatrix.single, h]

/-- The matrix reassembly is multiplication by the actual prepend idempotent. -/
theorem prependExpansion_projection (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    prependExpansion D Sc i n (prependCoefficients D Sc i n a) =
      a * prependAlgebra D Sc i n 1 := by
  rw [prependExpansion_coefficients]
  change _ = a * prependLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)
  simp only [FiniteHomMatrix.localUnit, map_sum, FiniteHomMatrix.idem, prependLinear_single,
    prependHom, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  erw [MonoidalSupercategory.whiskerLeft_id (R := k)]
  exact (matrix_mul_idem_sum D Sc a (prependWord i s)).symm

/-- Every element of the original whole corner has finite old-algebra coefficients. -/
theorem prependExpansion_exists (i : I) (n : ℕ)
    (z : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    ∃ b : (PrependShuffle n × ℕ) →₀ Hn D Sc n, prependExpansion D Sc i n b = z.1 :=
  ⟨prependCoefficients D Sc i n z.1, (prependExpansion_projection D Sc i n z.1).trans z.2⟩

/-- The finite expansion lands in the original corner. -/
def prependCornerExpansion (i : I) (n : ℕ) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun b := ⟨prependExpansion D Sc i n b, by
    have h := prependExpansion_projection D Sc i n (prependExpansion D Sc i n b)
    rw [prependCoefficients_expansion] at h
    exact h.symm⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' c b := Subtype.ext (map_smul _ c b)

/-- Whole affine prepend-corner coordinates (KKO I, Lemma 8.1). -/
def prependCoordinateEquiv (i : I) (n : ℕ) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) ≃ₗ[k]
      InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  LinearEquiv.ofBijective (prependCornerExpansion D Sc i n) ⟨
    fun a b h => prependExpansion_injective D Sc i n (congrArg Subtype.val h), by
      intro z
      obtain ⟨b, hb⟩ := prependExpansion_exists D Sc i n z
      exact ⟨b, Subtype.ext hb⟩⟩

/-- The inverse is the finite entrywise coefficient assembly. -/
theorem prependCoordinateEquiv_symm_apply (i : I) (n : ℕ)
    (z : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    (prependCoordinateEquiv D Sc i n).symm z = prependCoefficients D Sc i n z.1 := by
  apply (prependCoordinateEquiv D Sc i n).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact ((prependExpansion_projection D Sc i n z.1).trans z.2).symm

/-- Coefficientwise right multiplication by an old-algebra element. -/
def prependRightCoefficients {n : ℕ} (r : Hn D Sc n) :
    ((PrependShuffle n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      ((PrependShuffle n × ℕ) →₀ Hn D Sc n) :=
  Finsupp.mapRange.linearMap
    { toFun := fun b => b * r
      map_add' := fun a b => add_mul a b r
      map_smul' := fun c b => smul_mul_assoc c b r }

@[simp] theorem prependRightCoefficients_apply {n : ℕ} (r : Hn D Sc n)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (q : PrependShuffle n × ℕ) :
    prependRightCoefficients D Sc r b q = b q * r := rfl

/-- Right action is inherited from the actual affine multiplication. -/
theorem prependExpansion_right (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (r : Hn D Sc n) :
    prependExpansion D Sc i n (prependRightCoefficients D Sc r b) =
      prependExpansion D Sc i n b * prependAlgebra D Sc i n r := by
  let R : Hn D Sc (n + 1) →ₗ[k] Hn D Sc (n + 1) :=
    { toFun := fun a => a * prependAlgebra D Sc i n r
      map_add' := fun a b => add_mul a b _
      map_smul' := fun c b => smul_mul_assoc c b _ }
  have h : (prependExpansion D Sc i n).comp (prependRightCoefficients D Sc r) =
      R.comp (prependExpansion D Sc i n) := by
    apply Finsupp.lhom_ext
    intro q a
    simp only [LinearMap.comp_apply, prependRightCoefficients, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, LinearMap.coe_mk, AddHom.coe_mk, prependExpansion_single, R]
    exact prependPBWTerm_right D Sc i q.1 q.2 a r
  exact LinearMap.congr_fun h b

theorem prependCoordinateEquiv_right (i : I) (n : ℕ)
    (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (r : Hn D Sc n) :
    prependCoordinateEquiv D Sc i n (prependRightCoefficients D Sc r b) =
      MulOpposite.op r • prependCoordinateEquiv D Sc i n b := by
  apply Subtype.ext
  exact prependExpansion_right D Sc i n b r

/-- The coordinate inverse respects the same right-old-algebra action. -/
theorem prependCoordinateEquiv_symm_right (i : I) (n : ℕ)
    (z : InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)))
    (r : Hn D Sc n) :
    (prependCoordinateEquiv D Sc i n).symm (MulOpposite.op r • z) =
      prependRightCoefficients D Sc r ((prependCoordinateEquiv D Sc i n).symm z) := by
  apply (prependCoordinateEquiv D Sc i n).injective
  rw [LinearEquiv.apply_symm_apply, prependCoordinateEquiv_right, LinearEquiv.apply_symm_apply]

end OddMath.QuiverHecke
end

end

section

/-!
# Balanced prepend coordinates

The explicit balanced extension (9) of `PrependCoordinates.md` descends the
whole affine corner coordinates to any unital left old-algebra module.
`prependTensorEquiv` is additive: no ground-ring action is installed on the
integral quotient. Both maps are prescribed on representatives, and both
round trips use the proved affine coordinate equivalence, not flatness.
The shifted cyclotomic specialization and its commuting right action are
provided in `PrependCoefficientCoordinates`.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc n) M]
local notation "C" => InductionAlong.Corner (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n+1))
local notation "T" => InductionAlong.Ind M (prependAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n+1))
/-- The finite sum of the prescribed elementary tensors. -/
def prependTensorForward : ((PrependShuffle n × ℕ) →₀ M) →+ T :=
  Finsupp.liftAddHom fun q =>
    { toFun := fun y => InductionAlong.Ind.tmul (prependPBWCorner D Sc i q.1 q.2 1) y
      map_zero' := InductionAlong.Ind.tmul_zero _
      map_add' := InductionAlong.Ind.tmul_add _ }

/-- Balanced coordinate extraction using the proved right-old-algebra law. -/
def prependTensorBackward : T →+ ((PrependShuffle n × ℕ) →₀ M) :=
  InductionAlong.Ind.liftAdd
    (fun z y => Finsupp.mapRange (fun b : Hn D Sc n => b • y) (zero_smul _ y)
      ((prependCoordinateEquiv D Sc i n).symm z))
    (by intros; ext q; simp [add_smul])
    (by intros; ext q; simp [smul_add])
    (by intros; ext q; simp [prependCoordinateEquiv_symm_right, mul_smul])
@[simp] theorem prependTensorForward_single (q : PrependShuffle n × ℕ) (y : M) :
    prependTensorForward D Sc i n M (Finsupp.single q y) =
      InductionAlong.Ind.tmul (prependPBWCorner D Sc i q.1 q.2 1) y :=
  Finsupp.liftAddHom_apply_single _ _ _
@[simp] theorem prependTensorBackward_tmul (z : C) (y : M) (q : PrependShuffle n × ℕ) :
    prependTensorBackward D Sc i n M (InductionAlong.Ind.tmul z y) q =
      (prependCoordinateEquiv D Sc i n).symm z q • y := rfl

/-- Extracting a finite tensor expansion recovers its coefficients. -/
theorem prependTensorBackward_forward (x : (PrependShuffle n × ℕ) →₀ M) :
    prependTensorBackward D Sc i n M (prependTensorForward D Sc i n M x) = x := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add q y x _ _ hx =>
    rw [map_add, map_add, hx, prependTensorForward_single]
    congr 1
    ext p
    rw [prependTensorBackward_tmul, prependCoordinateEquiv_symm_apply]
    change prependCoefficients D Sc i n (prependPBWTerm D Sc i q.1 q.2 1) p • y = _
    rw [prependCoefficients_term]
    by_cases h : q = p
    · subst p; simp
    · simp [Finsupp.single_eq_of_ne' h]

/-- Old-algebra coefficients transfer to the module by balancing. -/
theorem prependTensorForward_coefficients (b : (PrependShuffle n × ℕ) →₀ Hn D Sc n) (y : M) :
    prependTensorForward D Sc i n M
      (Finsupp.mapRange (fun c : Hn D Sc n => c • y) (zero_smul _ y) b) =
      InductionAlong.Ind.tmul (prependCoordinateEquiv D Sc i n b) y := by
  induction b using Finsupp.induction with
  | zero => simp [InductionAlong.Ind.zero_tmul]
  | @single_add q c b _ _ hb =>
    rw [Finsupp.mapRange_add (fun a b => add_smul a b y), map_add,
      map_add, InductionAlong.Ind.add_tmul, hb]
    congr 1
    rw [Finsupp.mapRange_single, prependTensorForward_single,
      ← InductionAlong.Ind.op_smul_tmul]
    congr 1
    apply Subtype.ext
    change prependPBWTerm D Sc i q.1 q.2 1 * prependAlgebra D Sc i n c =
      prependExpansion D Sc i n (Finsupp.single q c)
    rw [prependExpansion_single, ← prependPBWTerm_right, one_mul]

/-- Reassembling extracted coordinates recovers every balanced tensor. -/
theorem prependTensorForward_backward (t : T) :
    prependTensorForward D Sc i n M (prependTensorBackward D Sc i n M t) = t := by
  induction t using InductionAlong.Ind.induction_on with
  | zero => simp
  | add t s ht hs => simp [ht, hs]
  | tmul z y =>
    change prependTensorForward D Sc i n M
      (Finsupp.mapRange (fun c : Hn D Sc n => c • y) (zero_smul _ y)
        ((prependCoordinateEquiv D Sc i n).symm z)) = _
    rw [prependTensorForward_coefficients, LinearEquiv.apply_symm_apply]

/-- Explicit additive coordinates on the existing balanced induction quotient. -/
def prependTensorEquiv : ((PrependShuffle n × ℕ) →₀ M) ≃+ T where
  toFun := prependTensorForward D Sc i n M
  invFun := prependTensorBackward D Sc i n M
  left_inv := prependTensorBackward_forward D Sc i n M
  right_inv := prependTensorForward_backward D Sc i n M
  map_add' := map_add _
end OddMath.QuiverHecke
end

end

section

/-!
# Shifted cyclotomic prepend coordinates

The balanced extension (9)–(10) of `PrependCoordinates.md` for the prescribed
shifted coefficient. The equivalence is additive, and right coefficient
compatibility is proved separately using the commuting twisted left action.
Polynomial parity, rather than even polynomial support, is required.
No cancellation, grading on the tensor, or full QP identity is asserted.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))

end OddMath.QuiverHecke
end

end

section

/-!
# Moving-dot square cancellation in prepend coordinates

The degree-two raising and cancellation step of `PrependCoordinates.md`,
used in the repeated-colour QP argument. The square of the existing right
dot is conjugated through the additive balanced coordinates; the finite
support proof permits every right cyclotomic coefficient. No flatness,
monicity, even polynomial support, or coefficient-domain hypothesis is used.
This does not identify an odd linear difference with its square or prove QP.
-/

noncomputable section
open Categorification
namespace OddMath.QuiverHecke

/-- Raising the polynomial exponent by two, with all shuffle indices retained. -/
def prependRaiseTwo {J M : Type*} [AddCommGroup M] :
    (J × ℕ →₀ M) →+ (J × ℕ →₀ M) :=
  Finsupp.embDomain.addMonoidHom
    ⟨fun q => (q.1, q.2 + 2), by intro x y h; cases x; cases y; simp_all⟩

@[simp] theorem prependRaiseTwo_single {J M : Type*} [AddCommGroup M]
    (q : J × ℕ) (y : M) :
    prependRaiseTwo (Finsupp.single q y) = Finsupp.single (q.1, q.2 + 2) y :=
  Finsupp.embDomain_single _ _ _

@[simp] theorem prependRaiseTwo_apply {J M : Type*} [AddCommGroup M]
    (f : J × ℕ →₀ M) (j : J) (m : ℕ) :
    prependRaiseTwo f (j, m + 2) = f (j, m) :=
  Finsupp.embDomain_apply_self _ _ (j, m)

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

variable (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (r : ℕ)
  Hn D Sc (r+1) →ₙ+* Hn D Sc (r+1+1))

end OddMath.QuiverHecke
end

end

section

/-!
# ELV coefficient normalization of prepend PBW coordinates

The affine input PBW basis underlying KKO I, arXiv:1206.5933v2,
Lemma 8.1 (p. 39), extended to the coefficient algebra of
`DeformedGlobalQP.md` §1. The extension to exterior coefficients is not
attributed to KKO. The existing `PrependIdx`, `prependBasis`, and
`ELV.balancedEquiv` are used throughout.

`prependAffineEquiv` is a proved affine coordinate equivalence, without
flatness. `balancedEquiv_prependExpansion` compares its normalized finite
expansion with the old-only quotient. Each coefficient is first twisted by
the moving tail parity, then the entire old morphism is twisted by the
balance parity. Neither twist can be discarded for exterior coefficients.

The expansion is surjective, not asserted injective: its indices still
include old normal forms. Regrouping those indices into old quotient Hom
coefficients, with a proved inverse, remains necessary for moving-dot
cancellation. No moving cyclotomic polynomial is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Affine input PBW coordinates with the full ELV coefficient algebra. -/
def prependAffineEquiv (i : I) (v w : List I) :
    hom D Sc cutoff (i :: v) w ≃ₗ[k]
      (PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _)
    (prependBasis D Sc (i := i) (s := v) (t := w)).repr).trans
      (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem prependAffineEquiv_tmul (i : I) (v w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D w))
    (x : PrependIdx i v w) :
    prependAffineEquiv D Sc cutoff i v w (a ⊗ₜ[k] f) x =
      (prependBasis D Sc).repr f x • a := by
  change TensorProduct.finsuppScalarRight k k _ _
    ((TensorProduct.congr (LinearEquiv.refl k _) (prependBasis D Sc).repr) (a ⊗ₜ[k] f)) x = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.finsuppScalarRight_apply_tmul_apply]

@[simp] theorem prependAffineEquiv_symm_single {i : I} {v w : List I}
    (x : PrependIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (prependAffineEquiv D Sc cutoff i v w).symm (Finsupp.single x a) =
      a ⊗ₜ[k] prependElt D Sc x := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (prependBasis D Sc).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single x a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, prependBasis_apply]

/-- New dots and moving crossings, with no old normal form or coefficient. -/
def prependTail {i : I} {v w : List I} (x : PrependIdx i v w) :
    (pres D Sc).obj (ob D (i :: x.oldTarget)) ⟶ (pres D Sc).obj (ob D w) :=
  cl D Sc _ _ (((List.replicate x.1.1 0).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹))
    (by simpa only [tgt_append, tgt_map_dot, x.moving_target] using
      sChain_pl (i :: x.oldTarget) (((List.replicate x.1.1 0).map PG.dot) ++
        cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹)))

/-- The existing input-side basis has old-first categorical orientation. -/
theorem prependElt_insert_tail {i : I} {v w : List I} (x : PrependIdx i v w) :
    prependElt D Sc x = affineInsert D Sc i v x.oldTarget x.old.nf ≫
      prependTail D Sc x := by
  rw [prependElt_eq_comp, cl_comp]
  rfl

/-- Parity of the new dots and moving crossings, excluding the old block. -/
def prependTailParity {i : I} {v w : List I} (x : PrependIdx i v w) : ZMod 2 :=
  ((pl (i :: x.oldTarget) (((List.replicate x.1.1 0).map PG.dot) ++
    cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹))).map
      fun z => z.2.1.parity D).sum

theorem prependTail_mem {i : I} {v w : List I} (x : PrependIdx i v w) :
    prependTail D Sc x ∈ parity (R := k) _ _ (prependTailParity D x) :=
  Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)

/-- Moving a homogeneous coefficient into the old block retains its Koszul sign. -/
theorem prepend_insert_coefficient {i : I} {v w : List I} (x : PrependIdx i v w)
    {q : ZMod 2} (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q) :
    insert D Sc cutoff i v x.oldTarget (a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) :
        hom D Sc cutoff (i :: x.oldTarget) w) =
      koszulSign q (prependTailParity D x) • (a ⊗ₜ[k] prependElt D Sc x) := by
  rw [insert_tmul]
  change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
    (Y := obj D Sc cutoff (i :: x.oldTarget)) (SuperalgebraCat.ofElem a) _ ≫
    BoxProd.tmulHom (X := obj D Sc cutoff (i :: x.oldTarget))
    (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
  rw [BoxProd.tmulHom_comp_tmulHom ha _ (SuperalgebraCat.ofElem 1)
    (prependTail_mem D Sc x)]
  change koszulSign q (prependTailParity D x) •
    ((1 * a) ⊗ₜ[k] (affineInsert D Sc i v x.oldTarget x.old.nf ≫ prependTail D Sc x)) = _
  rw [one_mul, ← prependElt_insert_tail]

/-- Coefficient parity involution, distinct from total parity on old Homs. -/
def coefficientTwist (r : ZMod 2) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  twist k r (X := SuperalgebraCat.star (SKM.SYM.elvCoefficientParity (k := k) D cutoff))
    (Y := SuperalgebraCat.star (SKM.SYM.elvCoefficientParity (k := k) D cutoff))

/-- Source-order normalization works for arbitrary, not only homogeneous, coefficients. -/
theorem prepend_insert_twisted_coefficient {i : I} {v w : List I}
    (x : PrependIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    insert D Sc cutoff i v x.oldTarget
        (coefficientTwist D cutoff (prependTailParity D x) a ⊗ₜ[k] x.old.nf) ≫
      (((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) :
        hom D Sc cutoff (i :: x.oldTarget) w) = a ⊗ₜ[k] prependElt D Sc x := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (prependTailParity D x) a =
        sign k (prependTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [ht, ← TensorProduct.smul_tmul', map_smul, Linear.smul_comp,
      prepend_insert_coefficient D Sc cutoff x a a.property, koszulSign_smul (R := k),
      mul_comm q, sign_smul_sign_smul]

/-- The full old coefficient, first normalized across the tail and then twisted in total parity. -/
def prependOldCoefficient (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (ideal D Sc cutoff v x.oldTarget).mkQ.comp
    ((twist k p).comp
      (((TensorProduct.mk k _ _).flip x.old.nf).comp
        (coefficientTwist D cutoff (prependTailParity D x))))

/-- One normalized PBW term in the existing signed coend. -/
def prependBalancedTerm (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ.comp
    ((DirectSum.lof k (List I) _ x.oldTarget).comp
      (((TensorProduct.mk k _ _)
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)).comp
          (prependOldCoefficient D Sc cutoff p x)))

/-- Finite normalized PBW expansion into the proved balanced tensor, not a replacement tensor. -/
def prependBalancedExpansion (p : ZMod 2) (i : I) (v w : List I) :
    (PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) →ₗ[k]
      BalancedTensor D Sc cutoff p i v w :=
  Finsupp.lsum k (prependBalancedTerm D Sc cutoff p)

@[simp] theorem prependBalancedExpansion_single (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    prependBalancedExpansion D Sc cutoff p i v w (Finsupp.single x a) =
      prependBalancedTerm D Sc cutoff p x a := Finsupp.lsum_single _ _ _ _

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# ELV old-Hom extraction from prepend PBW coordinates

The extraction step of `ELVPrependCoordinates.md`, needed for the old-only
coordinate comparison in `DeformedGlobalQP.md` §1. Only the old normal-form
component of the existing `PrependIdx` is replaced; the moving exponent and
inverse shuffle remain unchanged. No finite-colour or flatness assumption is used.

`prependExtractOld_insert_comp_tail` extracts arbitrary full-ELV old
composition. `prependExtractOldQuotient_insert_tail_eq_zero_iff` identifies
the old ideal on a prescribed tail. The coefficient-parity normalization
and total old-Hom parity twist are both retained.

These are affine extraction maps with values in old Homs or their quotient.
Descent on all old-relation generators, simultaneous regrouped coordinate
inversion, moving-square shift, and difference injectivity remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace PrependIdx
variable {i : I} {v w : List I}
/-- Replace only the old normal form, keeping the moving exponent and shuffle. -/
def replaceOld (x : PrependIdx i v w) (y : NFIdx v x.oldTarget) : PrependIdx i v w :=
  ⟨(x.1.1, y.1.1, y.1.2, x.1.2.2.2), y.2.1, y.2.2.1, by
    have he := tgt_shift [i] v (cw (Categorification.TypeA.canWord v.length y.1.2))
    simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
    simpa only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
      using x.moving_target⟩

theorem replaceOld_injective (x : PrependIdx i v w) : Function.Injective x.replaceOld := by
  intro y z h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun a : PrependIdx i v w => a.1.2.1) h)
    (congrArg (fun a : PrependIdx i v w => a.1.2.2.1) h)

end PrependIdx
namespace ELV

/-- Full coefficient coordinates on the old affine Hom. -/
def oldAffineEquiv (v t : List I) : hom D Sc cutoff v t ≃ₗ[k]
    (NFIdx v t →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  (TensorProduct.congr (LinearEquiv.refl k _) (basisNF D Sc v t).repr).trans
    (TensorProduct.finsuppScalarRight k k _ _)

@[simp] theorem oldAffineEquiv_symm_single {v t : List I} (y : NFIdx v t)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (oldAffineEquiv D Sc cutoff v t).symm (Finsupp.single y a) = a ⊗ₜ[k] y.nf := by
  change (TensorProduct.congr (LinearEquiv.refl k _) (basisNF D Sc v t).repr).symm
    ((TensorProduct.finsuppScalarRight k k _ _).symm (Finsupp.single y a)) = _
  rw [TensorProduct.finsuppScalarRight_symm_apply_single, TensorProduct.congr_symm_tmul]
  simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_single,
    one_smul, basisNF_apply]

/-- Coefficients of a fixed moving tail, with the mandatory coefficient-parity twist. -/
def prependTailCoefficients {i : I} {v w : List I} (x : PrependIdx i v w) :
    (NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) →ₗ[k]
      (PrependIdx i v w →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
  Finsupp.lsum k fun y => (Finsupp.lsingle (x.replaceOld y)).comp
    (coefficientTwist D cutoff (prependTailParity D x))

/-- Replacing the old index leaves the moving diagram unchanged. -/
theorem prependElt_replaceOld {i : I} {v w : List I} (x : PrependIdx i v w)
    (y : NFIdx v x.oldTarget) :
    prependElt D Sc (x.replaceOld y) =
      affineInsert D Sc i v x.oldTarget y.nf ≫ prependTail D Sc x := by
  change _ = ((pres D Sc).obj (ob D [i]) ◁ y.nf) ≫ _
  rw [whiskerLeft_nf]
  simp only [List.singleton_append]
  unfold prependTail prependElt
  rw [cl_comp]
  apply cl_eq_cl
  simp only [PrependIdx.gens, PrependIdx.replaceOld, List.length_singleton, List.map_append,
    dots_map_shift, cw_map_shift, List.append_assoc]

/-- The tail acts on every exterior coefficient by its coefficient-parity involution. -/
theorem insert_nf_tail {i : I} {v w : List I} (x : PrependIdx i v w)
    (y : NFIdx v x.oldTarget)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    insert D Sc cutoff i v x.oldTarget (a ⊗ₜ[k] y.nf) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w) =
      coefficientTwist D cutoff (prependTailParity D x) a ⊗ₜ[k]
        prependElt D Sc (x.replaceOld y) := by
  induction a using DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff) with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Limits.zero_comp]
  | add a b ha hb =>
    simp only [map_add, TensorProduct.add_tmul, Preadditive.add_comp, ha, hb]
  | @homogeneous q a =>
    have ht : coefficientTwist D cutoff (prependTailParity D x) a =
        sign k (prependTailParity D x * q) • (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :=
      twist_of_mem _ a.property
    rw [insert_tmul]
    change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
      (Y := obj D Sc cutoff (i :: x.oldTarget)) (SuperalgebraCat.ofElem a) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: x.oldTarget))
      (Y := obj D Sc cutoff w) (SuperalgebraCat.ofElem 1) _ = _
    rw [BoxProd.tmulHom_comp_tmulHom a.property _ (SuperalgebraCat.ofElem 1)
      (prependTail_mem D Sc x)]
    change koszulSign q (prependTailParity D x) •
      ((1 * (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ⊗ₜ[k]
        (affineInsert D Sc i v x.oldTarget y.nf ≫ prependTail D Sc x)) = _
    rw [one_mul, ← prependElt_replaceOld, ht, TensorProduct.smul_tmul',
      koszulSign_smul (R := k), mul_comm q]

/-- Extracting an arbitrary old coefficient followed by a prescribed moving tail. -/
theorem prependAffineEquiv_insert_tail {i : I} {v w : List I} (x : PrependIdx i v w)
    (r : hom D Sc cutoff v x.oldTarget) :
    prependAffineEquiv D Sc cutoff i v w
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) =
      prependTailCoefficients D cutoff x (oldAffineEquiv D Sc cutoff v x.oldTarget r) := by
  obtain ⟨f, rfl⟩ := (oldAffineEquiv D Sc cutoff v x.oldTarget).symm.surjective r
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.zero_comp]
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, hf, hg]
  | single y a =>
    rw [oldAffineEquiv_symm_single, insert_nf_tail]
    rw [← prependAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    rw [← oldAffineEquiv_symm_single, LinearEquiv.apply_symm_apply]
    simp only [prependTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]

/-- Restrict the existing PBW coordinates to one moving tail and regroup the old basis.
The normalization includes total old-Hom parity, not merely coefficient parity. -/
def prependExtractOld (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    hom D Sc cutoff (i :: v) w →ₗ[k] hom D Sc cutoff v x.oldTarget :=
  (twist k p).comp ((oldAffineEquiv D Sc cutoff v x.oldTarget).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff (prependTailParity D x))).comp
      ((Finsupp.lcomapDomain x.replaceOld x.replaceOld_injective).comp
        (prependAffineEquiv D Sc cutoff i v w).toLinearMap)))

/-- Actual extraction recovers an arbitrary old Hom coefficient, with its total twist. -/
theorem prependExtractOld_insert_tail (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    prependExtractOld D Sc cutoff p x
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) = twist k p r := by
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [prependAffineEquiv_insert_tail]
  have hc (f : NFIdx v x.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
      Finsupp.mapRange.linearMap (coefficientTwist D cutoff (prependTailParity D x))
        (Finsupp.lcomapDomain (R := k) x.replaceOld x.replaceOld_injective
          (prependTailCoefficients D cutoff x f)) = f := by
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg]
    | single y a =>
      simp only [prependTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
        Finsupp.lsingle_apply, Finsupp.lcomapDomain_apply,
        Finsupp.comapDomain_single,
        Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
      congr 1
      exact twist_twist _ _
  rw [hc, LinearEquiv.symm_apply_apply]

/-- A genuine old-quotient coordinate, obtained from the affine extraction. -/
def prependExtractOldQuotient (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) :
    hom D Sc cutoff (i :: v) w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (ideal D Sc cutoff v x.oldTarget).mkQ.comp (prependExtractOld D Sc cutoff p x)

@[simp] theorem prependExtractOldQuotient_insert_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) =
      (ideal D Sc cutoff v x.oldTarget).mkQ (twist k p r) := by
  exact congrArg (ideal D Sc cutoff v x.oldTarget).mkQ
    (prependExtractOld_insert_tail D Sc cutoff p x r)

/-- On a fixed tail, the vanishing coordinate is exactly the old ideal. -/
theorem prependExtractOldQuotient_insert_tail_eq_zero_iff (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) = 0 ↔
      r ∈ ideal D Sc cutoff v x.oldTarget := by
  rw [prependExtractOldQuotient_insert_tail, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hr
    simpa only [twist_twist] using twist_ideal D Sc cutoff p hr
  · exact twist_ideal D Sc cutoff p

end ELV
end OddMath.QuiverHecke
end

end

section

/-!
# Cross-tail ELV extraction

The off-tail step of `ELVPrependCoordinates.md`, needed for the old-only
coordinate comparison in `DeformedGlobalQP.md` §1. The existing `PrependIdx`
is regrouped by moving exponent and shuffle, with both index inverse laws.
`prependExtractOld_insert_off_tail` proves vanishing on every different tail,
for arbitrary full-ELV old coefficients and total parity. No finite-colour
hypothesis, flatness, or independence assumption is added.

The index equivalence is not yet an old-quotient coordinate equivalence.
Vanishing on all old-only relation generators, simultaneous quotient inversion,
and the moving-square shift and cancellation remain open.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace PrependIdx
variable {i : I} {v w : List I}
/-- The moving exponent and inverse-shuffle index, without the old normal form. -/
def tailKey (x : PrependIdx i v w) : ℕ × PrependShuffle v.length :=
  (x.1.1, x.1.2.2.2)

@[simp] theorem tailKey_replaceOld (x : PrependIdx i v w) (y : NFIdx v x.oldTarget) :
    (x.replaceOld y).tailKey = x.tailKey := rfl

/-- Different moving tails have disjoint sets of old normal-form replacements. -/
theorem replaceOld_ne_of_tailKey_ne (x z : PrependIdx i v w)
    (h : x.tailKey ≠ z.tailKey) (y : NFIdx v x.oldTarget) (b : NFIdx v z.oldTarget) :
    x.replaceOld y ≠ z.replaceOld b := by
  intro he
  exact h (show (x.replaceOld y).tailKey = (z.replaceOld b).tailKey from congrArg tailKey he)

/-- The target word and shuffle recover the intermediate old target uniquely. -/
theorem oldTarget_eq_of_tailKey_eq (x z : PrependIdx i v w)
    (h : x.tailKey = z.tailKey) : x.oldTarget = z.oldTarget := by
  have hd : x.1.2.2.2 = z.1.2.2.2 :=
    congrArg (fun a : ℕ × PrependShuffle v.length => a.2) h
  have he := x.moving_target.trans z.moving_target.symm
  rw [hd] at he
  have hs : (i :: x.oldTarget).length = v.length + 1 := by
    simp [oldTarget]
  have ht : (i :: z.oldTarget).length = v.length + 1 := by
    simp [oldTarget]
  have hh : i :: x.oldTarget = i :: z.oldTarget := by
    refine List.ext_getElem (hs.trans ht.symm) fun a ha hb => ?_
    let q : Fin (v.length + 1) :=
      Categorification.TypeA.wordProd (v.length + 1)
        (Categorification.TypeA.canWord (v.length + 1) z.1.2.2.2.1⁻¹)
        ⟨a, by omega⟩
    have hc := List.getElem_of_eq he (i := q.val) (by simpa only [length_tgt, hs] using q.isLt)
    rw [tgt_cw_getElem (Categorification.TypeA.validWord_canWord _ _) hs q,
      tgt_cw_getElem (Categorification.TypeA.validWord_canWord _ _) ht q] at hc
    simpa [q] using hc
  exact List.cons.inj hh |>.2

/-- Moving tails that occur in the existing prepend basis, forgetting the old index. -/
def Tail (i : I) (v w : List I) : Type :=
  ↥(Set.range (tailKey (i := i) (v := v) (w := w)))

namespace Tail
/-- Choose an existing prepend index over a tail; no new basis is chosen. -/
def representative (q : Tail i v w) : PrependIdx i v w := q.property.choose

@[simp] theorem representative_tailKey (q : Tail i v w) :
    q.representative.tailKey = q.val := q.property.choose_spec
end Tail

end PrependIdx
namespace ELV

/-- Off-tail restriction vanishes before either parity normalization. -/
theorem prependTailCoefficients_comap_off_tail {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (f : NFIdx v z.oldTarget →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    Finsupp.lcomapDomain (R := k) x.replaceOld x.replaceOld_injective
      (prependTailCoefficients D cutoff z f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single y a =>
    simp only [prependTailCoefficients, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    ext b
    simp only [Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Finsupp.zero_apply]
    exact Finsupp.single_eq_of_ne (x.replaceOld_ne_of_tailKey_ne z h b y)

/-- Every old coefficient on a different moving tail extracts to zero. -/
theorem prependExtractOld_insert_off_tail (p : ZMod 2) {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (r : hom D Sc cutoff v z.oldTarget) :
    prependExtractOld D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  unfold prependExtractOld
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [prependAffineEquiv_insert_tail, prependTailCoefficients_comap_off_tail D cutoff x z h]
  simp only [map_zero]

/-- Off-tail extraction also vanishes in the old cyclotomic quotient. -/
theorem prependExtractOldQuotient_insert_off_tail (p : ZMod 2) {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (r : hom D Sc cutoff v z.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  change (ideal D Sc cutoff v x.oldTarget).mkQ
    (prependExtractOld D Sc cutoff p x _) = 0
  rw [prependExtractOld_insert_off_tail D Sc cutoff p x z h, map_zero]
end ELV
end OddMath.QuiverHecke
end

end

section

/-!
# Descent of ELV prepend extraction through all old relations

The old-only coordinate comparison needed by `DeformedGlobalQP.md` §1.
Cross-source rebasing retains the prescribed moving tail. A normal-form index
is selected only from a nonzero old Hom, so empty old Hom spaces are allowed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace PrependIdx
variable {i : I} {v s w : List I}

private theorem shuffle_word_transport {n m : ℕ} (h : n = m) (d : PrependShuffle m) :
    Categorification.TypeA.canWord (n + 1) (↑(h.symm ▸ d : PrependShuffle n))⁻¹ =
      Categorification.TypeA.canWord (m + 1) d.1⁻¹ := by
  subst m
  rfl

/-- Rebase a moving tail to another source using an actual old normal form. -/
def rebase (z : PrependIdx i s w) (y : NFIdx v z.oldTarget) : PrependIdx i v w := by
  have hl : v.length = s.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, oldTarget] using hh
  refine ⟨(z.1.1, y.1.1, y.1.2, hl.symm ▸ z.1.2.2.2), y.2.1, y.2.2.1, ?_⟩
  have he := tgt_shift [i] v (cw (Categorification.TypeA.canWord v.length y.1.2))
  simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
  simp only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw]
  rw [shuffle_word_transport hl z.1.2.2.2]
  exact z.moving_target

 theorem rebase_target (z : PrependIdx i s w) (y : NFIdx v z.oldTarget) :
    (z.rebase y).oldTarget = z.oldTarget := y.tgt_cw

end PrependIdx
namespace ELV

private theorem tail_cl_heq {a b w : List I} {L M : List PG}
    (hab : a = b) (hLM : L = M) (ha : SChain a (pl a L) w)
    (hb : SChain b (pl b M) w) : HEq (cl D Sc a w L ha) (cl D Sc b w M hb) := by
  subst b
  subst M
  rfl

/-- Rebasing changes only the old index, not the positioned moving diagram. -/
theorem prependTail_rebase {i : I} {v s w : List I} (z : PrependIdx i s w)
    (y : NFIdx v z.oldTarget) :
    HEq (prependTail D Sc (z.rebase y)) (prependTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (List.cons i) (z.rebase_target y)
  · dsimp only [PrependIdx.rebase]
    have hl : v.length = s.length := by
      have hh := congrArg List.length y.tgt_cw
      simpa only [length_tgt, PrependIdx.oldTarget] using hh
    rw [PrependIdx.shuffle_word_transport hl z.1.2.2.2]

/-- Equal moving keys give the same positioned tail, including its source. -/
theorem prependTail_heq_of_tailKey_eq {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey = z.tailKey) :
    HEq (prependTail D Sc x) (prependTail D Sc z) := by
  apply tail_cl_heq
  · exact congrArg (List.cons i) (x.oldTarget_eq_of_tailKey_eq z h)
  · have hn := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    change x.1.1 = z.1.1 at hn
    change x.1.2.2.2 = z.1.2.2.2 at hd
    rw [hn, hd]

private theorem insert_tail_transport {i : I} {v t t' w : List I}
    (e : t = t') (r : hom D Sc cutoff v t)
    (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    insert D Sc cutoff i v t r ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f :
        hom D Sc cutoff (i :: t) w) =
    insert D Sc cutoff i v t' (e ▸ r) ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g :
        hom D Sc cutoff (i :: t') w) := by
  subst t'
  cases h
  rfl

/-- Old ideal coefficients vanish at every moving coordinate. -/
theorem prependExtractOldQuotient_insert_ideal_tail (p : ZMod 2)
    {i : I} {v w : List I} (x z : PrependIdx i v w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  by_cases h : x.tailKey = z.tailKey
  · have ht := z.oldTarget_eq_of_tailKey_eq x h.symm
    rw [insert_tail_transport D Sc cutoff ht r _ _
      (prependTail_heq_of_tailKey_eq D Sc z x h.symm)]
    apply (prependExtractOldQuotient_insert_tail_eq_zero_iff D Sc cutoff p x _).mpr
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr
  · exact prependExtractOldQuotient_insert_off_tail D Sc cutoff p x z h r

/-- A nonzero old Hom supplies an actual normal-form index; empty Homs are not assumed inhabited. -/
theorem exists_oldIndex_of_ne_zero {v t : List I} (r : hom D Sc cutoff v t) (hr : r ≠ 0) :
    Nonempty (NFIdx v t) := by
  by_contra hn
  have : IsEmpty (NFIdx v t) := not_nonempty_iff.mp hn
  apply hr
  apply (oldAffineEquiv D Sc cutoff v t).injective
  ext y
  exact isEmptyElim y

/-- Cross-source old ideal coefficients vanish, without an inhabitation assumption on old Homs. -/
theorem prependExtractOldQuotient_insert_ideal_cross_source (p : ZMod 2)
    {i : I} {v s w : List I} (x : PrependIdx i v w) (z : PrependIdx i s w)
    (r : hom D Sc cutoff v z.oldTarget) (hr : r ∈ ideal D Sc cutoff v z.oldTarget) :
    prependExtractOldQuotient D Sc cutoff p x
      (insert D Sc cutoff i v z.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc z : hom D Sc cutoff (i :: z.oldTarget) w)) = 0 := by
  by_cases hz : r = 0
  · simp only [hz, map_zero, Limits.zero_comp]
  · obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hz
    have ht := (z.rebase_target y).symm
    rw [insert_tail_transport D Sc cutoff ht r _ _ (prependTail_rebase D Sc z y).symm]
    apply prependExtractOldQuotient_insert_ideal_tail
    exact (show ∀ {t t' : List I} (e : t = t') (a : hom D Sc cutoff v t),
      a ∈ ideal D Sc cutoff v t → (e ▸ a) ∈ ideal D Sc cutoff v t' from
        by intro t t' e; subst t'; exact fun _ ha => ha) ht r hr

/-- Every old-only generator has zero extracted old quotient coordinate, for arbitrary continuation. -/
theorem prependExtractOldQuotient_old_generator (p : ZMod 2)
    {i : I} {v s w : List I} (x : PrependIdx i v w)
    (r : hom D Sc cutoff v s) (hr : r ∈ ideal D Sc cutoff v s)
    (h : hom D Sc cutoff (i :: s) w) :
    prependExtractOldQuotient D Sc cutoff p x (insert D Sc cutoff i v s r ≫ h) = 0 := by
  obtain ⟨f, rfl⟩ := (prependAffineEquiv D Sc cutoff i s w).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Limits.comp_zero]
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg, add_zero]
  | single z a =>
    rw [prependAffineEquiv_symm_single, ← prepend_insert_twisted_coefficient D Sc cutoff z a,
      ← Category.assoc, ← insert_comp]
    exact prependExtractOldQuotient_insert_ideal_cross_source D Sc cutoff p x z _
      (ideal_comp D Sc cutoff hr _)

/-- Extraction kills the entire old-only relation span, not just prescribed-source tails. -/
theorem prependExtractOldQuotient_relations (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) :
    relations D Sc cutoff i v w ≤ LinearMap.ker (prependExtractOldQuotient D Sc cutoff p x) := by
  apply Submodule.span_le.mpr
  rintro f ⟨s, r, hr, h, rfl⟩
  exact prependExtractOldQuotient_old_generator D Sc cutoff p x r hr h

/-- An actual old quotient coordinate on the old-only target. -/
def prependOldCoordinate (p : ZMod 2) {i : I} {v w : List I} (x : PrependIdx i v w) :
    Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v x.oldTarget :=
  (relations D Sc cutoff i v w).liftQ (prependExtractOldQuotient D Sc cutoff p x)
    (prependExtractOldQuotient_relations D Sc cutoff p x)

@[simp] theorem prependOldCoordinate_projection (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (h : hom D Sc cutoff (i :: v) w) :
    prependOldCoordinate D Sc cutoff p x (projection D Sc cutoff i v w h) =
      prependExtractOldQuotient D Sc cutoff p x h := rfl

/-- Simultaneous old quotient coefficients, with finite support in the existing moving tails. -/
abbrev PrependOldCoordinates (i : I) (v w : List I) :=
  ⨁ (q : PrependIdx.Tail i v w), Old D Sc cutoff v q.representative.oldTarget

/-- Reconstruct the old-only target from all moving-tail old quotient coefficients. -/
def prependOldReconstruct (p : ZMod 2) (i : I) (v w : List I) :
    PrependOldCoordinates D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  DirectSum.toModule k _ _ fun q => pair D Sc cutoff p i
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      prependTail D Sc q.representative)

/-- Reconstruction followed by extraction is the specified direct-sum component. -/
theorem prependOldCoordinate_reconstruct (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p q.representative
      (prependOldReconstruct D Sc cutoff p i v w f) = f q := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply]
  | of t a =>
    change prependOldCoordinate D Sc cutoff p q.representative
      (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t a)) = _
    rw [prependOldReconstruct, DirectSum.toModule_lof]
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t.representative.oldTarget).mkQ_surjective a
    rw [pair_mk, prependOldCoordinate_projection]
    by_cases ht : t = q
    · subst t
      rw [prependExtractOldQuotient_insert_tail, twist_twist, DirectSum.of_eq_same]
    · rw [prependExtractOldQuotient_insert_off_tail]
      · symm
        exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)
      · intro h
        apply ht
        apply Subtype.ext
        exact t.representative_tailKey.symm.trans (h.symm.trans q.representative_tailKey)

/-- Simultaneous old quotient reconstruction is injective. -/
theorem prependOldReconstruct_injective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Injective (prependOldReconstruct D Sc cutoff p i v w) := by
  intro f g h
  apply DFinsupp.ext
  intro q
  rw [← prependOldCoordinate_reconstruct D Sc cutoff p q f,
    ← prependOldCoordinate_reconstruct D Sc cutoff p q g, h]

private theorem prependOldReconstruct_range_tail (p : ZMod 2)
    {i : I} {v w : List I} (x : PrependIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    projection D Sc cutoff i v w
      (insert D Sc cutoff i v x.oldTarget r ≫
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc x : hom D Sc cutoff (i :: x.oldTarget) w)) ∈
      LinearMap.range (prependOldReconstruct D Sc cutoff p i v w) := by
  let q : PrependIdx.Tail i v w := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  refine ⟨DirectSum.lof k _ _ q
    ((ideal D Sc cutoff v q.representative.oldTarget).mkQ (twist k p (ht ▸ r))), ?_⟩
  rw [prependOldReconstruct, DirectSum.toModule_lof, pair_mk, twist_twist]
  exact congrArg (projection D Sc cutoff i v w)
    (insert_tail_transport D Sc cutoff ht r _ _
      (prependTail_heq_of_tailKey_eq D Sc x q.representative hk)).symm

/-- Every old-only class has finite simultaneous old quotient coordinates. -/
theorem prependOldReconstruct_surjective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Surjective (prependOldReconstruct D Sc cutoff p i v w) := by
  intro z
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  obtain ⟨f, rfl⟩ := (prependAffineEquiv D Sc cutoff i v w).symm.surjective h
  change projection D Sc cutoff i v w ((prependAffineEquiv D Sc cutoff i v w).symm f) ∈
    LinearMap.range (prependOldReconstruct D Sc cutoff p i v w)
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => simp only [map_add]; exact Submodule.add_mem _ hf hg
  | single x a =>
    rw [prependAffineEquiv_symm_single, ← prepend_insert_twisted_coefficient D Sc cutoff x a]
    exact prependOldReconstruct_range_tail D Sc cutoff p x _

/-- The full ELV old-only quotient is the direct sum of old quotient Hom coordinates.
No flatness, finite-colour assumption, or moving cyclotomic relation is imposed. -/
def prependOldCoordinateEquiv (p : ZMod 2) (i : I) (v w : List I) :
    Target D Sc cutoff i v w ≃ₗ[k] PrependOldCoordinates D Sc cutoff i v w :=
  (LinearEquiv.ofBijective (prependOldReconstruct D Sc cutoff p i v w)
    ⟨prependOldReconstruct_injective D Sc cutoff p i v w,
      prependOldReconstruct_surjective D Sc cutoff p i v w⟩).symm

@[simp] theorem prependOldCoordinateEquiv_apply (p : ZMod 2) {i : I} {v w : List I}
    (z : Target D Sc cutoff i v w) (q : PrependIdx.Tail i v w) :
    prependOldCoordinateEquiv D Sc cutoff p i v w z q =
      prependOldCoordinate D Sc cutoff p q.representative z := by
  rw [← prependOldCoordinate_reconstruct D Sc cutoff p q]
  exact congrArg (prependOldCoordinate D Sc cutoff p q.representative)
    ((prependOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z)

/-- Reconstruction is the left inverse of simultaneous extraction. -/
@[simp] theorem prependOldReconstruct_coordinateEquiv (p : ZMod 2) (i : I) (v w : List I)
    (z : Target D Sc cutoff i v w) :
    prependOldReconstruct D Sc cutoff p i v w
      (prependOldCoordinateEquiv D Sc cutoff p i v w z) = z :=
  (prependOldCoordinateEquiv D Sc cutoff p i v w).symm_apply_apply z

/-- Reconstruction is the right inverse of simultaneous extraction as well. -/
@[simp] theorem prependOldCoordinateEquiv_reconstruct (p : ZMod 2) (i : I) (v w : List I)
    (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinateEquiv D Sc cutoff p i v w
      (prependOldReconstruct D Sc cutoff p i v w f) = f :=
  (prependOldCoordinateEquiv D Sc cutoff p i v w).apply_symm_apply f

end ELV
end OddMath.QuiverHecke
end

end
