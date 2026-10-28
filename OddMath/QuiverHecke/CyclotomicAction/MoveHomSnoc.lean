/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerWords
import OddMath.QuiverHecke.ShuffleBasis

/-!
# Peeling the last letter off the moving-strand map

The QP induction of `docs/Nondegeneracy/DeformedGlobalQP.md`, §3 (the deformed form of
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5) removes the last spectator
letter: `V_n = g_n (V_(n-1) ⊗ 1)`. The map `moveHom` is defined by peeling the first
letter, so this file proves the other recursion.

* `whiskerWordRingHom`: right whiskering by a word as a ring homomorphism of
  endomorphism rings;
* `genE_whiskerRight`, `sameIntertwiner_whiskerRight`, `intertwinerHom_whiskerRight`:
  a positioned generator or intertwiner on a word, whiskered on the right by a word,
  is the same generator on the concatenated word;
* `moveHom_append_singleton`: `moveHom i l (ν ++ [x])` is `moveHom i l ν ⊗ 1_x`
  followed by the intertwiner `g` at the last two positions.

Every statement holds for arbitrary colours, parities and words, including empty ones.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory SignedNilHecke

variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- Right whiskering by the word `s`, as a ring homomorphism of endomorphism rings. -/
def whiskerWordRingHom (w s : List I) :
    End ((pres D Sc).obj (ob D w)) →+* End ((pres D Sc).obj (ob D (w ++ s))) where
  toFun f := f ▷ (pres D Sc).obj (ob D s)
  map_one' := MonoidalSupercategory.id_whiskerRight (R := k) _ _
  map_mul' f g := MonoidalSupercategory.comp_whiskerRight (R := k) g f _
  map_zero' := MonoidalSupercategory.zero_whiskerRight k _
  map_add' f g := MonoidalSupercategory.add_whiskerRight (R := k) f g _

@[simp] theorem whiskerWordRingHom_apply (w s : List I) (f : End ((pres D Sc).obj (ob D w))) :
    whiskerWordRingHom D Sc w s f = f ▷ (pres D Sc).obj (ob D s) := rfl

/-- A positioned generator fixing the word `w` keeps its meaning after right whiskering. -/
theorem genE_whiskerRight (w s : List I) (g : PG) (h : SChain w (pl w [g]) w)
    (hg : g.pos + g.width ≤ w.length) :
    genE D Sc w g ▷ (pres D Sc).obj (ob D s) = genE D Sc (w ++ s) g := by
  have hf : Fits w.length [g] := by
    intro g' hg'
    simp only [List.mem_singleton] at hg'
    subst hg'
    exact hg
  rw [genE_eq D Sc h, cl_whiskerRight D Sc [g] h s hf]
  exact (genE_eq D Sc _).symm

theorem dotE_whiskerRight (w s : List I) (a : ℕ) (ha : a < w.length) :
    dotE D Sc w a ▷ (pres D Sc).obj (ob D s) = dotE D Sc (w ++ s) a :=
  genE_whiskerRight D Sc w s (.dot a) (sChain_dotAny w a) (by simpa [PG.pos, PG.width] using ha)

/-- The same-colour intertwiner keeps its meaning after right whiskering. -/
theorem sameIntertwiner_whiskerRight (l r s : List I) (i : I) :
    sameIntertwiner D Sc (l ++ [i, i] ++ r) l.length i ▷ (pres D Sc).obj (ob D s) =
      sameIntertwiner D Sc (l ++ [i, i] ++ r ++ s) l.length i := by
  have hx : whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s (dotE D Sc (l ++ [i, i] ++ r) l.length) =
      dotE D Sc (l ++ [i, i] ++ r ++ s) l.length :=
    dotE_whiskerRight D Sc (l ++ [i, i] ++ r) s l.length (by simp)
  have hy : whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s
      (dotE D Sc (l ++ [i, i] ++ r) (l.length + 1)) =
      dotE D Sc (l ++ [i, i] ++ r ++ s) (l.length + 1) :=
    dotE_whiskerRight D Sc (l ++ [i, i] ++ r) s (l.length + 1) (by simp)
  have hc : whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s (crossE D Sc (l ++ [i, i] ++ r) l.length) =
      crossE D Sc (l ++ [i, i] ++ r ++ s) l.length :=
    genE_whiskerRight D Sc _ s (.cross l.length) (sChain_cross l r i rfl rfl)
      (by simp [PG.pos, PG.width])
  change whiskerWordRingHom D Sc (l ++ [i, i] ++ r) s
      (sameIntertwiner D Sc (l ++ [i, i] ++ r) l.length i) = _
  unfold sameIntertwiner
  split_ifs
  · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, map_sub,
      map_mul, map_pow, hx, hy, hc]
  · simp only [gEven, phiEven, map_sub, map_mul, map_add, map_one, hx, hy, hc]

/-- Transport of a same-colour intertwiner along an equality of words. -/
theorem sameIntertwiner_congr {w w' : List I} (h : w = w') (a : ℕ) (i : I) :
    sameIntertwiner D Sc w a i =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
        sameIntertwiner D Sc w' a i ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h.symm) := by
  subst h
  simp

/-- Transport of an intertwiner along equalities of its left and right contexts. -/
theorem intertwinerHom_congr {l l' r r' : List I} (hl : l = l') (hr : r = r') (i j : I) :
    intertwinerHom D Sc l r i j =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by rw [hl, hr])) ≫
        intertwinerHom D Sc l' r' i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by rw [hl, hr])) := by
  subst hl hr
  simp

/-- Transporting a class along equalities of its source and target words. -/
theorem cl_eq_eqToHom_comp {t t' u u' : List I} {gs : List PG} (e : t = u) (e' : t' = u')
    (h : SChain t (pl t gs) t') (h' : SChain u (pl u gs) u') :
    cl D Sc t t' gs h =
      eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e) ≫ cl D Sc u u' gs h' ≫
        eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e'.symm) := by
  subst e e'
  simp

/-- Right whiskering of an intertwiner by a word is the intertwiner with the longer
right context. -/
theorem intertwinerHom_whiskerRight (l r s : List I) (i j : I) :
    intertwinerHom D Sc l r i j ▷ (pres D Sc).obj (ob D s) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
          (show l ++ [i, j] ++ r ++ s = l ++ [i, j] ++ (r ++ s) by simp)) ≫
        intertwinerHom D Sc l (r ++ s) i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ [j, i] ++ (r ++ s) = l ++ [j, i] ++ r ++ s by simp)) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, intertwinerHom_self, sameIntertwiner_whiskerRight,
      sameIntertwiner_congr D Sc (show l ++ [i, i] ++ r ++ s = l ++ [i, i] ++ (r ++ s) by simp)]
  · have hf : Fits (l ++ [i, j] ++ r).length [.cross l.length] := by
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      simp [PG.pos, PG.width]
    rw [intertwinerHom_of_ne D Sc _ _ h, intertwinerHom_of_ne D Sc _ _ h,
      cl_whiskerRight D Sc [.cross l.length] _ s hf]
    rw [cl_eq_eqToHom_comp D Sc (show l ++ [i, j] ++ r ++ s = l ++ [i, j] ++ (r ++ s) by simp)
      (show l ++ [j, i] ++ r ++ s = l ++ [j, i] ++ (r ++ s) by simp) _
      (sChain_crossAt l (r ++ s) i j)]

/-- Right whiskering of an identification of words. -/
theorem eqToHom_whiskerRight_word {w w' : List I} (h : w = w') (s : List I) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ▷ (pres D Sc).obj (ob D s) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (congrArg (· ++ s) h)) := by
  subst h
  exact MonoidalSupercategory.id_whiskerRight (R := k) _ _

/-- Right whiskering of an arbitrary identification of objects. -/
theorem eqToHom_whiskerRight_obj {Y Y' : (pres D Sc).Presented} (h : Y = Y')
    (Z : (pres D Sc).Presented) :
    eqToHom h ▷ Z = eqToHom (congrArg (· ⊗ Z) h) := by
  subst h
  exact MonoidalSupercategory.id_whiskerRight (R := k) _ _

/-- KKO's `V_(n+1) = g_(n+1) (V_n ⊗ 1)`: the moving strand first crosses `ν`, then the
final letter `x`. The left context `l` is arbitrary. -/
theorem moveHom_append_singleton (i x : I) : ∀ (ν l : List I),
    moveHom D Sc i l (ν ++ [x]) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
          (show l ++ i :: (ν ++ [x]) = l ++ i :: ν ++ [x] by simp)) ≫
        (moveHom D Sc i l ν ▷ (pres D Sc).obj (ob D [x])) ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ ν ++ [i] ++ [x] = l ++ ν ++ [i, x] ++ [] by simp)) ≫
            intertwinerHom D Sc (l ++ ν) [] i x ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
                (show l ++ ν ++ [x, i] ++ [] = l ++ (ν ++ [x]) ++ [i] by simp))
  | [], l => by
    simp only [List.nil_append, moveHom]
    rw [eqToHom_whiskerRight_word D Sc (show l ++ [i] = l ++ [] ++ [i] by simp)]
    rw [intertwinerHom_congr D Sc (show l ++ [] = l by simp) rfl i x]
    simp
  | j :: ν, l => by
    have ih := moveHom_append_singleton i x ν (l ++ [j])
    simp only [List.cons_append, moveHom]
    rw [ih]
    simp only [MonoidalSupercategory.comp_whiskerRight (R := k), Category.assoc,
      eqToHom_whiskerRight_obj, intertwinerHom_whiskerRight]
    rw [intertwinerHom_congr D Sc (show l ++ [j] ++ ν = l ++ j :: ν by simp) rfl i x]
    simp

end OddMath.QuiverHecke
