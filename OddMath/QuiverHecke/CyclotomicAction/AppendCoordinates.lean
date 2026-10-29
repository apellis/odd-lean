/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.AppendBasis
import OddMath.QuiverHecke.CyclotomicAction.LastDot
import OddMath.QuiverHecke.MixedRelations

/-!
# Append PBW expansion in the Hom algebra

The expansion terms `c_u x_last^m ψ(b)` of the input-side append decomposition
(the mirror of `PrependCoordinates.lean`, for Kang–Kashiwara–Oh,
arXiv:1206.5933v2, Lemma 8.1), with their right-old-algebra law, corner
membership and matrix entries. `appendPBWTerm_old_nf` identifies a term with a
single old normal form as coefficient with the scalar basis element `appendElt`;
`append_single_expansion` expands every allowed matrix entry. See
`docs/Nondegeneracy/AppendCoordinates.md` §3.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical

/-- Append shuffles for equal block sizes are the same set. -/
def AppendShuffle.cast {n m m' : ℕ} (h : n + 1 = m) (h' : n + 1 = m') :
    AppendShuffle h ≃ AppendShuffle h' := by
  subst h; subst h'; exact Equiv.refl _

theorem AppendShuffle.canWord_cast {n m m' : ℕ} (h : n + 1 = m) (h' : n + 1 = m')
    (u : AppendShuffle h) :
    canWord m' (AppendShuffle.cast h h' u).1⁻¹ = canWord m u.1⁻¹ := by
  subst h; subst h'; rfl

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Moving crossings are indexed independently of the source word. -/
abbrev AppendShuffleAt (n : ℕ) := AppendShuffle (show n + 1 = n + 1 from rfl)

/-- The target word after moving the last strand along an inverse shuffle. -/
def appendShuffleTarget (i : I) {n : ℕ} (u : AppendShuffleAt n) (s : Word I n) :
    Word I (n + 1) :=
  ⟨tgt (s.1 ++ [i]) (cw (canWord (n + 1) u.1⁻¹)), by simp [s.2]⟩

/-- The reduced crossing diagram moving the appended strand. -/
def appendShuffleHom (i : I) {n : ℕ} (u : AppendShuffleAt n) (s : Word I n) :
    wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendShuffleTarget i u s) :=
  cl D Sc (s.1 ++ [i]) _ (cw (canWord (n + 1) u.1⁻¹)) (sChain_pl _ _)

/-- Sum over old words of the moving crossings. -/
def appendShuffleElement (i : I) {n : ℕ} (u : AppendShuffleAt n) : Hn D Sc (n + 1) :=
  ∑ s : Word I n, FiniteHomMatrix.single (appendShuffleTarget i u s) (appendWord i s)
    (appendShuffleHom D Sc i u s)

/-- A coefficient acts first, followed by last-strand dots and the moving crossings. -/
def appendPBWTerm (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b : Hn D Sc n) : Hn D Sc (n + 1) :=
  appendShuffleElement D Sc i u * affineLastDot D Sc i n ^ m * appendAlgebra D Sc i n b

theorem appendPBWTerm_right (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b r : Hn D Sc n) :
    appendPBWTerm D Sc i u m (b * r) =
      appendPBWTerm D Sc i u m b * appendAlgebra D Sc i n r := by
  simp only [appendPBWTerm, map_mul, mul_assoc]

theorem appendPBWTerm_corner (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b : Hn D Sc n) :
    appendPBWTerm D Sc i u m b * appendAlgebra D Sc i n 1 = appendPBWTerm D Sc i u m b := by
  simp only [appendPBWTerm, mul_assoc, ← map_mul, mul_one]

/-- The same term as an element of the append induction corner. -/
def appendPBWCorner (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b : Hn D Sc n) :
    InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  ⟨appendPBWTerm D Sc i u m b, appendPBWTerm_corner D Sc i u m b⟩

theorem appendPBWCorner_right (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b r : Hn D Sc n) :
    appendPBWCorner D Sc i u m (b * r) = MulOpposite.op r • appendPBWCorner D Sc i u m b :=
  Subtype.ext (appendPBWTerm_right D Sc i u m b r)

/-! ## Matrix entries -/

theorem affineLastDot_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    affineLastDot D Sc i n * FiniteHomMatrix.single (appendWord i t) (appendWord i s) f =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s)
        (f ≫ inductionLastDot D Sc i t) := by
  rw [affineLastDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h)) _ _
  · simp

theorem affineLastDot_pow_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) (m : ℕ) :
    affineLastDot D Sc i n ^ m * FiniteHomMatrix.single (appendWord i t) (appendWord i s) f =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s)
        (f ≫ inductionLastDot D Sc i t ^ m) := by
  induction m with
  | zero => simp [End.one_def]
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, affineLastDot_mul_single]
    congr 1
    rw [pow_succ', End.mul_def, Category.assoc]

theorem appendShuffleElement_mul_single (i : I) {n : ℕ} (u : AppendShuffleAt n)
    (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    appendShuffleElement D Sc i u *
        FiniteHomMatrix.single (appendWord i t) (appendWord i s) f =
      FiniteHomMatrix.single (appendShuffleTarget i u t) (appendWord i s)
        (f ≫ appendShuffleHom D Sc i u t) := by
  rw [appendShuffleElement, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h)) _ _
  · simp

/-- The coefficient morphism acts first, then the new dots, then the moving crossing. -/
theorem appendPBWTerm_single (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (s t : Word I n) (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    appendPBWTerm D Sc i u m (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single (appendShuffleTarget i u t) (appendWord i s)
        (appendHom D Sc i s t f ≫ (inductionLastDot D Sc i t ^ m) ≫
          appendShuffleHom D Sc i u t) := by
  unfold appendPBWTerm
  change (_ * _) * appendLinear D Sc i n (FiniteHomMatrix.single t s f) = _
  rw [appendLinear_single, mul_assoc, affineLastDot_pow_mul_single,
    appendShuffleElement_mul_single, Category.assoc]

omit [Fintype I] in
/-- The last dot is the positioned dot at the last strand. -/
theorem inductionLastDot_eq_dotE (i : I) {n : ℕ} (s : Word I n) :
    inductionLastDot D Sc i s = dotE D Sc (s.1 ++ [i]) s.1.length := by
  simp [inductionLastDot, inductionStrandDot, dotE_eq, cl, wordObj,
    Presentation.diag_whiskerLeft, pl, PG.ld, appendWord]
  exact Presentation.diag_eq_of_layers_eq _
    (by simp [Diagram.whiskerL, mkD, layList, Layer.wl, lay, ob])

/-- The intermediate old target as a word of the original height. -/
def AppendIdx.oldWord {i : I} {s t : List I} (x : AppendIdx i s t) : Word I s.length :=
  ⟨x.oldTarget, by simp [AppendIdx.oldTarget]⟩

/-- The target word has one more strand than the old source. -/
def AppendIdx.targetWord {i : I} {s t : List I} (x : AppendIdx i s t) :
    Word I (s.length + 1) :=
  ⟨t, by rw [← x.moving_target]; simp [AppendIdx.oldTarget]⟩

/-- The moving shuffle of an append index, at the height of its source. -/
def AppendIdx.shuffle {i : I} {s t : List I} (x : AppendIdx i s t) :
    AppendShuffleAt s.length :=
  (AppendShuffle.cast _ _).symm x.1.2.2.2

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

omit [Fintype I] in
theorem AppendIdx.canWord_shuffle {i : I} {s t : List I} (x : AppendIdx i s t) :
    canWord (s.length + 1) x.shuffle.1⁻¹ = canWord (s ++ [i]).length x.1.2.2.2.1⁻¹ := by
  rw [← AppendShuffle.canWord_cast _ (appendLen s i) x.shuffle]
  simp [AppendIdx.shuffle]

/-- A scalar append basis element is exactly the corresponding matrix PBW term. -/
theorem appendPBWTerm_old_nf {i : I} {s t : List I} (x : AppendIdx i s t) :
    appendPBWTerm D Sc i x.shuffle x.1.1
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)) =
    FiniteHomMatrix.single x.targetWord (appendWord i ⟨s, rfl⟩) (appendElt D Sc x) := by
  rw [appendPBWTerm_single, inductionLastDot_eq_dotE, dotE_pow]
  apply matrix_single_heq D Sc (Subtype.ext (by
    simpa only [appendShuffleTarget, AppendIdx.oldWord, AppendIdx.targetWord,
      x.canWord_shuffle] using x.moving_target))
  change HEq ((x.old.nf ▷ (pres D Sc).obj (ob D [i])) ≫ _ ≫ _) _
  rw [nf_whiskerRight]
  unfold appendShuffleHom
  dsimp only [AppendIdx.oldWord, AppendIdx.old]
  rw [cl_comp, cl_comp]
  unfold appendElt
  apply cl_target_heq D Sc (by
    simpa only [appendShuffleTarget, AppendIdx.oldWord, AppendIdx.targetWord,
      x.canWord_shuffle] using x.moving_target)
  simp [AppendIdx.gens, AppendIdx.oldTarget, x.canWord_shuffle, List.append_assoc]

/-- Every allowed matrix entry with appended source has a finite expansion by the
prescribed append PBW terms, with coefficients single old normal forms. -/
theorem append_single_expansion (i : I) (s : List I) (t : Word I (s.length + 1))
    (f : wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t (appendWord i ⟨s, rfl⟩) f =
      ((appendBasis D Sc (i := i) (s := s) (t := t.1)).repr f).sum
        (fun x c => c • appendPBWTerm D Sc i x.shuffle x.1.1
          (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩
            (NFIdx.nf (D := D) (Sc := Sc) x.old))) := by
  let L : (wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) →ₗ[k]
      Hn D Sc (s.length + 1) :=
    { toFun := FiniteHomMatrix.single t (appendWord i ⟨s, rfl⟩)
      map_add' := FiniteHomMatrix.single_add _ _
      map_smul' := fun c g => FiniteHomMatrix.single_smul _ _ c g }
  have h := congrArg L ((appendBasis D Sc (i := i) (s := s) (t := t.1)).linearCombination_repr f)
  change L f = _
  rw [← h]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    appendBasis_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (_ • ·)
  exact (appendPBWTerm_old_nf D Sc x).symm

end OddMath.QuiverHecke
