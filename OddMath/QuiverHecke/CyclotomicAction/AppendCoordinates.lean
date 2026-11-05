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

/-! ## Matrix entries -/

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

omit [Fintype I] in

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

end OddMath.QuiverHecke
