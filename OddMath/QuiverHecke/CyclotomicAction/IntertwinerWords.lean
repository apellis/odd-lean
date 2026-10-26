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

`moveHom i l ν` is the composite `g_{|l|+|ν|} ⋯ g_{|l|+1}` from `l ++ i :: ν` to
`l ++ ν ++ [i]`, which for `l = []` is the element `g_n ⋯ g_1 e(i, ν)` of KKO's map `Q`
(Proposition 8.4). `dot_comp_moveHom` is the second identity of KKO (8.13):
`x_{n+1} g_n ⋯ g_1 e(i, ν) = (-1)^{p(i)p(ν)} g_n ⋯ g_1 x_1 e(i, ν)`.

Dots away from the pair pass through `g` with the sign `(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}`
(`dot_left_comp_intertwinerHom`, `dot_right_comp_intertwinerHom`: (8.11) for
`b ≠ a, a + 1`). Hence a dot on the strand `ν_b` passes through `g_n ⋯ g_1` from position
`b + 1` to position `b` with the sign `(-1)^{p(ν_b)p(i)p(ν)}` (`dot_mem_comp_moveHom`), which is
the first identity of (8.13) for the dots of `R(β)`; dots to the left of the moving strand pass
unchanged up to the same sign (`dot_left_comp_moveHom`).
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

/-! ### Moving a strand across a word -/

theorem zsign_add_eq (p q : ZMod 2) : zsign k (p + q) = zsign k p * zsign k q := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with rfl | rfl <;> rcases hz q with rfl | rfl <;> simp [zsign]

/-- A dot commutes with the identification of equal words. -/
theorem dotE_comp_eqToHom {w w' : List I} (h : w = w') (b : ℕ) :
    dotE D Sc w b ≫ eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫ dotE D Sc w' b := by
  subst h
  simp

/-- KKO's `g_n ⋯ g_1 e(i, ν)`, moving the strand of colour `i` from position `|l|` across
`ν` to the end: `g_{|l|+|ν|} ⋯ g_{|l|+1}` on `l ++ i :: ν`. -/
def moveHom (i : I) : (l ν : List I) →
    (pres D Sc).obj (ob D (l ++ i :: ν)) ⟶ (pres D Sc).obj (ob D (l ++ ν ++ [i]))
  | l, [] => eqToHom (by simp)
  | l, j :: ν =>
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp)) ≫
        intertwinerHom D Sc l ν i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)) ≫
            moveHom i (l ++ [j]) ν ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp))

/-- The parity `p(ν)` of a word. -/
def wordSumParity (ν : List I) : ZMod 2 := (ν.map D.parity).sum

/-- KKO (8.13), second identity: the dot on the moving strand passes from its first position
to the last, with the sign `(-1)^{p(i) p(ν)}`. -/
theorem dot_comp_moveHom (i : I) (l ν : List I) :
    dotE D Sc (l ++ i :: ν) l.length ≫ moveHom D Sc i l ν =
      zsign k (D.parity i * wordSumParity D ν) •
        (moveHom D Sc i l ν ≫ dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) := by
  induction ν generalizing l with
  | nil =>
    simp only [moveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero, List.length_nil,
      add_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    exact dotE_comp_eqToHom D Sc (by simp) _
  | cons j ν ih =>
    simp only [moveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc (show l ++ i :: j :: ν = l ++ [i, j] ++ ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp),
      Category.assoc, show l.length + 1 = (l ++ [j]).length by simp,
      ← Category.assoc (dotE D Sc _ _), ih, Linear.smul_comp, Category.assoc,
      show (l ++ [j]).length + ν.length = l.length + (j :: ν).length by simp; omega,
      dotE_comp_eqToHom D Sc (show l ++ [j] ++ ν ++ [i] = l ++ j :: ν ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq]

/-! ### Far dots -/

section Ring
variable {B : Type*} [Ring B]

/-- An element commuting with `u`, `v`, `T` commutes with both same-colour variants. -/
theorem comm_variants {u v T Y : B} (hu : u * Y = Y * u) (hv : v * Y = Y * v)
    (ht : T * Y = Y * T) :
    OddNilHecke.Intertwiner.element u v T * Y = Y * OddNilHecke.Intertwiner.element u v T ∧
      gEven u v T * Y = Y * gEven u v T := by
  have hu' : ∀ r, u * (Y * r) = Y * (u * r) := fun r => by rw [← mul_assoc, hu, mul_assoc]
  have hv' : ∀ r, v * (Y * r) = Y * (v * r) := fun r => by rw [← mul_assoc, hv, mul_assoc]
  have ht' : ∀ r, T * (Y * r) = Y * (T * r) := fun r => by rw [← mul_assoc, ht, mul_assoc]
  constructor
  · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, pow_two,
      mul_sub, sub_mul, mul_assoc, hu, hv, ht, hu', hv']
  · simp only [gEven, phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_one,
      hu, hv, ht, hu', hv']

/-- An element anticommuting with `u`, `v`, `T` anticommutes with both same-colour variants. -/
theorem anticomm_variants {u v T Y : B} (hu : u * Y = -(Y * u)) (hv : v * Y = -(Y * v))
    (ht : T * Y = -(Y * T)) :
    OddNilHecke.Intertwiner.element u v T * Y = -(Y * OddNilHecke.Intertwiner.element u v T) ∧
      gEven u v T * Y = -(Y * gEven u v T) := by
  have hu' : ∀ r, u * (Y * r) = -(Y * (u * r)) := fun r => by
    rw [← mul_assoc, hu, neg_mul, mul_assoc]
  have hv' : ∀ r, v * (Y * r) = -(Y * (v * r)) := fun r => by
    rw [← mul_assoc, hv, neg_mul, mul_assoc]
  have ht' : ∀ r, T * (Y * r) = -(Y * (T * r)) := fun r => by
    rw [← mul_assoc, ht, neg_mul, mul_assoc]
  constructor
  · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, pow_two,
      mul_sub, sub_mul, mul_assoc, mul_neg, neg_neg, hu, hv, ht, hu',
      hv']
    noncomm_ring
  · simp only [gEven, phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_one,
      mul_neg, neg_neg, hu, hv, ht, hu', hv']
    noncomm_ring

end Ring

/-- If `u`, `v`, `T` all supercommute with `Y` with the sign of `q`, so does `g`. -/
theorem sameIntertwiner_mul_of {w : List I} {a : ℕ} {i : I} {Y : End ((pres D Sc).obj (ob D w))}
    (q : ZMod 2) (hu : dotE D Sc w a * Y = zsign k q • (Y * dotE D Sc w a))
    (hv : dotE D Sc w (a + 1) * Y = zsign k q • (Y * dotE D Sc w (a + 1)))
    (ht : crossE D Sc w a * Y = zsign k q • (Y * crossE D Sc w a)) :
    sameIntertwiner D Sc w a i * Y = zsign k q • (Y * sameIntertwiner D Sc w a i) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz q with rfl | rfl
  · simp only [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul] at hu hv ht ⊢
    have h := comm_variants hu hv ht
    unfold sameIntertwiner
    split_ifs
    · exact h.1
    · exact h.2
  · simp only [show zsign k (1 : ZMod 2) = -1 by simp [zsign], neg_one_smul] at hu hv ht ⊢
    have h := anticomm_variants hu hv ht
    unfold sameIntertwiner
    split_ifs
    · exact h.1
    · exact h.2

theorem cl_interchange_of_eq {t t' : List I} (l m v : List I) (g h : Shape I)
    (ht : t = l ++ g.dom ++ m ++ h.dom ++ v) (ht' : t' = l ++ g.cod ++ m ++ h.cod ++ v) {p q : ℕ}
    (hp : l.length = p) (hq : (l ++ g.dom ++ m).length = q)
    (h₁ : SChain t (pl t [PG.ofShape g p, PG.ofShape h q]) t')
    (h₂ : SChain t (pl t [PG.ofShape h q, PG.ofShape g p]) t') :
    cl D Sc t t' [PG.ofShape g p, PG.ofShape h q] h₁ =
      zsign k (g.parity D * h.parity D) • cl D Sc t t' [PG.ofShape h q, PG.ofShape g p] h₂ := by
  subst ht ht' hp hq
  exact cl_interchange D Sc l m v g h h₁ h₂

theorem sChain_dotAny (t : List I) (b : ℕ) : SChain t (pl t [.dot b]) t := by
  simpa [tgt, PG.act] using sChain_pl t [.dot b]

/-- KKO (8.11) for `b < a`: a dot to the left of the pair passes through `g` with the sign
`(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}`. -/
theorem dot_left_comp_intertwinerHom (l₁ l₂ r : List I) (x i j : I) :
    dotE D Sc (l₁ ++ [x] ++ l₂ ++ [i, j] ++ r) l₁.length ≫
        intertwinerHom D Sc (l₁ ++ [x] ++ l₂) r i j =
      zsign k (D.parity x * (D.parity i * D.parity j)) •
        (intertwinerHom D Sc (l₁ ++ [x] ++ l₂) r i j ≫
          dotE D Sc (l₁ ++ [x] ++ l₂ ++ [j, i] ++ r) l₁.length) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def, parity_sq]
    refine sameIntertwiner_mul_of D Sc _ ?_ ?_ ?_
    · have := genE_interchange D Sc l₁ l₂ ([i] ++ r) (.dot x) (.dot i) rfl rfl
        (w := l₁ ++ [x] ++ l₂ ++ [i, i] ++ r) (by simp [Shape.dom]) (p := l₁.length)
        (q := (l₁ ++ [x] ++ l₂).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape] using this
    · have := genE_interchange D Sc l₁ (l₂ ++ [i]) r (.dot x) (.dot i) rfl rfl
        (w := l₁ ++ [x] ++ l₂ ++ [i, i] ++ r) (by simp [Shape.dom]) (p := l₁.length)
        (q := (l₁ ++ [x] ++ l₂).length + 1) rfl (by simp [Shape.dom]; omega)
      simpa only [Shape.parity, PG.ofShape] using this
    · have := genE_interchange D Sc l₁ l₂ r (.dot x) (.cross i i) rfl rfl
        (w := l₁ ++ [x] ++ l₂ ++ [i, i] ++ r) (by simp [Shape.dom]) (p := l₁.length)
        (q := (l₁ ++ [x] ++ l₂).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, parity_sq] using this
  · rw [intertwinerHom_of_ne D Sc _ r h, dotE_eq_cl D Sc (sChain_dotAny _ _),
      dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
    exact cl_interchange D Sc l₁ l₂ r (.dot x) (.cross i j) _ _

/-- KKO (8.11) for `b > a + 1`: a dot to the right of the pair passes through `g` with the sign
`(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}`. -/
theorem dot_right_comp_intertwinerHom (l m v : List I) (x i j : I) :
    dotE D Sc (l ++ [i, j] ++ (m ++ [x] ++ v)) (l ++ [i, j] ++ m).length ≫
        intertwinerHom D Sc l (m ++ [x] ++ v) i j =
      zsign k (D.parity x * (D.parity i * D.parity j)) •
        (intertwinerHom D Sc l (m ++ [x] ++ v) i j ≫
          dotE D Sc (l ++ [j, i] ++ (m ++ [x] ++ v)) (l ++ [i, j] ++ m).length) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def, parity_sq]
    have flip : ∀ {f Y : End ((pres D Sc).obj (ob D (l ++ [i, i] ++ (m ++ [x] ++ v))))}
        {q : ZMod 2}, Y * f = zsign k q • (f * Y) → f * Y = zsign k q • (Y * f) := by
      intro f Y q hfy
      rw [hfy, smul_smul, zsign_mul_self, one_smul]
    refine sameIntertwiner_mul_of D Sc _ (flip ?_) (flip ?_) (flip ?_)
    · have := genE_interchange D Sc l ([i] ++ m) v (.dot i) (.dot x) rfl rfl
        (w := l ++ [i, i] ++ (m ++ [x] ++ v)) (by simp [Shape.dom]) (p := l.length)
        (q := (l ++ [i, i] ++ m).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, mul_comm (D.parity i)] using this
    · have := genE_interchange D Sc (l ++ [i]) m v (.dot i) (.dot x) rfl rfl
        (w := l ++ [i, i] ++ (m ++ [x] ++ v)) (by simp [Shape.dom]) (p := l.length + 1)
        (q := (l ++ [i, i] ++ m).length) (by simp) (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, mul_comm (D.parity i)] using this
    · have := genE_interchange D Sc l m v (.cross i i) (.dot x) rfl rfl
        (w := l ++ [i, i] ++ (m ++ [x] ++ v)) (by simp [Shape.dom]) (p := l.length)
        (q := (l ++ [i, i] ++ m).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, parity_sq, mul_comm (D.parity i)] using this
  · rw [intertwinerHom_of_ne D Sc l _ h, dotE_eq_cl D Sc (sChain_dotAny _ _),
      dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
    have hs := cl_interchange_of_eq D Sc l m v (.cross i j) (.dot x)
      (t := l ++ [i, j] ++ (m ++ [x] ++ v)) (t' := l ++ [j, i] ++ (m ++ [x] ++ v))
      (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl
      (sChain_append_of (sChain_crossAt l _ i j) (sChain_dotAny _ _))
      (sChain_append_of (sChain_dotAny _ _) (sChain_crossAt l _ i j))
    have h' := congrArg (zsign k (D.parity x * (D.parity i * D.parity j)) • ·) hs
    simp only [smul_smul, Shape.parity, mul_comm (D.parity i * D.parity j), zsign_mul_self,
      one_smul] at h'
    exact h'.symm

/-! ### Dots through the moving-strand map -/

/-- A dot to the left of the moving strand passes through `g_n ⋯ g_1` with the sign
`(-1)^{p(ν_b) p(i) p(ν)}`. -/
theorem dot_left_comp_moveHom (i x : I) (l₁ : List I) (ν : List I) :
    ∀ (l l₂ : List I), l = l₁ ++ [x] ++ l₂ →
      dotE D Sc (l ++ i :: ν) l₁.length ≫ moveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (moveHom D Sc i l ν ≫ dotE D Sc (l ++ ν ++ [i]) l₁.length) := by
  induction ν with
  | nil =>
    intro l l₂ _
    simp only [moveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    exact dotE_comp_eqToHom D Sc (by simp) _
  | cons j ν ih =>
    intro l l₂ hl
    subst hl
    simp only [moveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l₁ ++ [x] ++ l₂ ++ i :: j :: ν = l₁ ++ [x] ++ l₂ ++ [i, j] ++ ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_left_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show l₁ ++ [x] ++ l₂ ++ [j, i] ++ ν = (l₁ ++ [x] ++ l₂ ++ [j]) ++ i :: ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      ih (l₁ ++ [x] ++ l₂ ++ [j]) (l₂ ++ [j]) (by simp), Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc
        (show l₁ ++ [x] ++ l₂ ++ [j] ++ ν ++ [i] = l₁ ++ [x] ++ l₂ ++ j :: ν ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq]

/-- KKO (8.13), first identity, for dots: the dot on the strand `ν_b` passes through
`g_n ⋯ g_1` from position `b + 1` to position `b`, with the sign `(-1)^{p(ν_b) p(i) p(ν)}`. -/
theorem dot_mem_comp_moveHom (i x : I) (v : List I) (m : List I) :
    ∀ (l ν : List I), ν = m ++ [x] ++ v →
      dotE D Sc (l ++ i :: ν) (l.length + 1 + m.length) ≫ moveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (moveHom D Sc i l ν ≫ dotE D Sc (l ++ ν ++ [i]) (l.length + m.length)) := by
  induction m with
  | nil =>
    intro l ν hν
    obtain rfl : ν = x :: v := by simp [hν]
    simp only [moveHom, List.length_nil, add_zero]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ i :: x :: v = l ++ [i, x] ++ v by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_succ_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc (show l ++ [x, i] ++ v = (l ++ [x]) ++ i :: v by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dot_left_comp_moveHom D Sc i x l v (l ++ [x]) [] (by simp), Linear.smul_comp,
      Category.assoc,
      dotE_comp_eqToHom D Sc (show l ++ [x] ++ v ++ [i] = l ++ x :: v ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, ← zsign_add_eq]
    congr 2
    simp only [wordSumParity, List.map_cons, List.sum_cons]
    linear_combination (-D.parity i) * parity_sq (D.parity x)
  | cons j m ih =>
    intro l ν hν
    obtain rfl : ν = j :: (m ++ [x] ++ v) := by simp [hν]
    simp only [moveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ i :: j :: (m ++ [x] ++ v) = l ++ [i, j] ++ (m ++ [x] ++ v) by simp),
      show l.length + 1 + (j :: m).length = (l ++ [i, j] ++ m).length by simp; omega,
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_right_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show l ++ [j, i] ++ (m ++ [x] ++ v) = (l ++ [j]) ++ i :: (m ++ [x] ++ v) by simp),
      Category.assoc,
      show (l ++ [i, j] ++ m).length = (l ++ [j]).length + 1 + m.length by simp; omega,
      ← Category.assoc (dotE D Sc _ _), ih (l ++ [j]) _ rfl, Linear.smul_comp, Category.assoc,
      show (l ++ [j]).length + m.length = l.length + (j :: m).length by simp; omega,
      dotE_comp_eqToHom D Sc (show l ++ [j] ++ (m ++ [x] ++ v) ++ [i] =
        l ++ j :: (m ++ [x] ++ v) ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq]

end OddMath.QuiverHecke
