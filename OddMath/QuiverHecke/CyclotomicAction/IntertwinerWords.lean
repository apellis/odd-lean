/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.Intertwiner
import OddMath.QuiverHecke.Centre

/-!
# Intertwiners between words and the adjacent dot transport

Ports the word-level use of `Categorification/KLR/Intertwiner.lean` (`KLRAlgebra.gInt` and
`x_mul_gInt`, Kang–Kashiwara arXiv:1102.4677v4, (4.7) and the first identity of Lemma 4.12) to
the quiver Hecke supercategory, following Kang–Kashiwara–Oh, arXiv:1206.5933v2, (8.8) and the
second identity of Lemma 8.3 (8.11) for `b = a, a + 1`. The downstream consumer is the map `Q`
of KKO Proposition 8.4 and the product `QP` of Theorem 8.5, which compose the intertwiners
`g_n ⋯ g_1` on the words `(i, ν)`.

For a word `l ++ [i, j] ++ r`, `intertwinerHom l r i j` is KKO's `g_a e(ν)` at `a = |l|`, as a
morphism to `l ++ [j, i] ++ r`:

* the crossing, if `i ≠ j`;
* `(v - u)(1 + (v - u) T)` on an even colour and `OddNilHecke.Intertwiner.element u v T`
  `= (v² - u²)((v - u) - (v² - u²) T)` on an odd colour, if `i = j`, with `u, v` the dots on the
  two strands and `T` their crossing (`CyclotomicAction.Intertwiner`).

Diagrams compose bottom to top. The dot on the left strand passes through `g` to the right
strand with the sign `(-1)^{|i||j|}`, and the dot on the right strand to the left one with the
same sign (`dot_comp_intertwinerHom`, `dot_succ_comp_intertwinerHom`); this is KKO's sign
`(-1)^{p(ν_a)p(ν_{a+1})p(ν_b)}` for `b = a, a + 1`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
open SKM (zsign)
open scoped Classical

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- KKO's `g_a` on two adjacent strands `a, a + 1` of one colour `i` in the word `w`. -/
def sameIntertwiner (w : List I) (a : ℕ) (i : I) : End ((pres D Sc).obj (ob D w)) :=
  if D.parity i = 1 then
    OddNilHecke.Intertwiner.element (dotE D Sc w a) (dotE D Sc w (a + 1)) (crossE D Sc w a)
  else gEven (dotE D Sc w a) (dotE D Sc w (a + 1)) (crossE D Sc w a)

theorem sChain_crossAt (l r : List I) (i j : I) :
    SChain (l ++ [i, j] ++ r) (pl (l ++ [i, j] ++ r) [.cross l.length]) (l ++ [j, i] ++ r) := by
  have h := sChain_pl (l ++ [i, j] ++ r) [.cross l.length]
  simpa [tgt, PG.act, List.take_append, List.drop_append] using h

theorem sChain_dotAt (l r : List I) (i j : I) (b : ℕ) :
    SChain (l ++ [i, j] ++ r) (pl (l ++ [i, j] ++ r) [.dot b]) (l ++ [i, j] ++ r) := by
  have h := sChain_pl (l ++ [i, j] ++ r) [.dot b]
  simpa [tgt, PG.act] using h

theorem dotE_eq_cl {w : List I} {b : ℕ} (h : SChain w (pl w [.dot b]) w) :
    dotE D Sc w b = cl D Sc w w [.dot b] h :=
  genE_eq D Sc h

/-- KKO's `g_a e(ν)` for `ν = l ++ [i, j] ++ r` and `a = |l|`, as a morphism of words. -/
def intertwinerHom (l r : List I) (i j : I) :
    (pres D Sc).obj (ob D (l ++ [i, j] ++ r)) ⟶ (pres D Sc).obj (ob D (l ++ [j, i] ++ r)) :=
  if h : i = j then
    sameIntertwiner D Sc (l ++ [i, j] ++ r) l.length i ≫ eqToHom (by rw [h])
  else cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j)

theorem intertwinerHom_of_ne (l r : List I) {i j : I} (h : i ≠ j) :
    intertwinerHom D Sc l r i j = cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j) := by
  simp [intertwinerHom, h]

theorem intertwinerHom_self (l r : List I) (i : I) :
    intertwinerHom D Sc l r i i = sameIntertwiner D Sc (l ++ [i, i] ++ r) l.length i := by
  simp [intertwinerHom]

theorem parity_eq_zero_of_ne_one {p : ZMod 2} (h : ¬p = 1) : p = 0 := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  exact (hz p).resolve_right h

/-- KKO (8.11) for `b = a`: the dot on the left strand passes to the right strand. -/
theorem dot_comp_intertwinerHom (l r : List I) (i j : I) :
    dotE D Sc (l ++ [i, j] ++ r) l.length ≫ intertwinerHom D Sc l r i j =
      zsign k (D.parity i * D.parity j) •
        (intertwinerHom D Sc l r i j ≫ dotE D Sc (l ++ [j, i] ++ r) (l.length + 1)) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def]
    by_cases hp : D.parity i = 1
    · simp only [sameIntertwiner, hp, ite_true]
      rw [(oddTwo_block D Sc l r i hp).element_identities.2.1]
      simp [zsign]
    · have hp0 := parity_eq_zero_of_ne_one hp
      simp only [sameIntertwiner, hp, ite_false]
      rw [(evenTwo_block D Sc l r i hp0).x_succ_mul_gEven]
      simp [zsign, hp0]
  · rw [intertwinerHom_of_ne D Sc l r h,
      dotE_eq_cl D Sc (sChain_dotAt l r i j l.length),
      dotE_eq_cl D Sc (sChain_dotAt l r j i (l.length + 1)), cl_comp, cl_comp]
    exact slide_left_ne D Sc l r i j h _ _

/-- KKO (8.11) for `b = a + 1`: the dot on the right strand passes to the left strand. -/
theorem dot_succ_comp_intertwinerHom (l r : List I) (i j : I) :
    dotE D Sc (l ++ [i, j] ++ r) (l.length + 1) ≫ intertwinerHom D Sc l r i j =
      zsign k (D.parity i * D.parity j) •
        (intertwinerHom D Sc l r i j ≫ dotE D Sc (l ++ [j, i] ++ r) l.length) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def]
    by_cases hp : D.parity i = 1
    · simp only [sameIntertwiner, hp, ite_true]
      rw [(oddTwo_block D Sc l r i hp).element_identities.2.2.1]
      simp [zsign]
    · have hp0 := parity_eq_zero_of_ne_one hp
      simp only [sameIntertwiner, hp, ite_false]
      rw [← (evenTwo_block D Sc l r i hp0).x_mul_gEven]
      simp [zsign, hp0]
  · rw [intertwinerHom_of_ne D Sc l r h,
      dotE_eq_cl D Sc (sChain_dotAt l r i j (l.length + 1)),
      dotE_eq_cl D Sc (sChain_dotAt l r j i l.length), cl_comp, cl_comp]
    have hs := slide_right_ne D Sc l r i j h (sChain_append_of (sChain_crossAt l r i j)
      (sChain_dotAt l r j i l.length))
      (sChain_append_of (sChain_dotAt l r i j (l.length + 1)) (sChain_crossAt l r i j))
    have h' := congrArg (zsign k (D.parity i * D.parity j) • ·) hs
    simp only [smul_smul, zsign_mul_self, one_smul] at h'
    exact h'.symm

end OddMath.QuiverHecke
