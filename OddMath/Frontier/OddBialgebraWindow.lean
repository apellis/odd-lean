import OddMath.Frontier.OddBialgebraKron
import OddMath.Frontier.OddCategorification

/-!
# Graded strand windows in `ONH_{a+b}`

EKL arXiv:1111.1320v1, §6, pp. 46–47: `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}` places a diagram of `ONH_a`
to the left of one of `ONH_b`. Gradings in the paper normalization (a dot of degree `2`, a
crossing of degree `-2`).

* `winPiece n l r d ⊆ ONH_{n+2}`: the `ℤ`-span of words of degree `d` in the generators supported
  on the strands `[l, r)`. Elements of degree `2i` and `2j` in disjoint windows supercommute:
  `y x = (-1)^{ij} x y` (`winPiece_supercomm`); all degrees are even (`onh_even`).
* The graded embeddings of the blocks: `OnhWindow.windowHom` for `ONH_{m+2}` (`windowHom_mem`),
  `dotHom n j : OPol_1 = ONH_1 → ONH_{n+2}`, `x ↦ x_j` (`dotHom_mem`), and `ℤ = ONH_0`.
* `SuperPair.ofWin`, `SuperPair.intLeft`, `SuperPair.intRight`: the resulting super pairs.
-/

noncomputable section

namespace OddMath.Frontier.OddBialgebra
open GradedK0 NilHeckeAction NilHeckeGrading OnhWindow OddCategorification
open OddMath.SkewPolynomial (SkewPolynomial)

variable {n : ℕ}

/-! ### Window pieces -/

/-- A letter supported on the strands `[l, r)`. -/
def InWin (l r : ℕ) : Letter n → Prop
  | Sum.inl j => l ≤ j.val ∧ j.val < r
  | Sum.inr i => l ≤ i.val ∧ i.val + 1 < r

/-- The `ℤ`-span of words of degree `d` in the generators supported on `[l, r)`. -/
def winPiece (n l r : ℕ) (d : ℤ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (wordValue '' {w : List (Letter n) | wordDegree w = d ∧ ∀ g ∈ w, InWin l r g})

theorem word_mem_winPiece {l r : ℕ} (w : List (Letter n)) (hw : ∀ g ∈ w, InWin l r g) :
    wordValue w ∈ winPiece n l r (wordDegree w) :=
  Submodule.subset_span ⟨w, ⟨rfl, hw⟩, rfl⟩

theorem winPiece_le (l r : ℕ) (d : ℤ) : winPiece n l r d ≤ degreePiece n d :=
  Submodule.span_mono (Set.image_subset _ fun _ hw => hw.1)

theorem wordValue_cons (g : Letter n) (w : List (Letter n)) :
    wordValue (g :: w) = letterValue g * wordValue w := by
  simp [wordValue]

theorem wordDegree_cons (g : Letter n) (w : List (Letter n)) :
    wordDegree (g :: w) = letterDegree g + wordDegree w := by
  simp [wordDegree]

theorem homog_wordValue {l r : ℕ} (w : List (Letter n)) (hw : ∀ g ∈ w, InWin l r g) :
    Homog l r w.length (wordValue w) := by
  induction w with
  | nil => exact Homog.one
  | cons g w ih =>
    rw [wordValue_cons, List.length_cons, Nat.add_comm]
    refine Homog.mul (Homog.gen ?_) (ih fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))
    have hg := hw g (List.mem_cons_self ..)
    cases g with
    | inl j => exact IsGen.dot j hg.1 hg.2
    | inr i => exact IsGen.crossing i hg.1 hg.2

theorem wordDegree_eq (w : List (Letter n)) :
    ∃ c : ℤ, wordDegree w = 2 * ((w.length : ℤ) - 2 * c) := by
  induction w with
  | nil => exact ⟨0, by simp [wordDegree]⟩
  | cons g w ih =>
    obtain ⟨c, hc⟩ := ih
    rw [wordDegree_cons, hc, List.length_cons]
    cases g with
    | inl j => exact ⟨c, by simp [letterDegree]; ring⟩
    | inr i => exact ⟨c + 1, by simp [letterDegree]; ring⟩

/-- All degrees of `ONH_{n+2}` are even. -/
theorem onh_even {d : ℤ} {x : Presented n} (hx : x ∈ onhGrading n d) (hx0 : x ≠ 0) : Even d := by
  by_contra hd
  have h : degreePiece n d = ⊥ := by
    refine le_antisymm (Submodule.span_le.2 ?_) bot_le
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨c, hc⟩ := wordDegree_eq w
    exact absurd ⟨(w.length : ℤ) - 2 * c, by rw [← hw.out, hc]; ring⟩ hd
  have hx' : x ∈ degreePiece n d := hx
  rw [h] at hx'
  exact hx0 ((Submodule.mem_bot ℤ).1 hx')

theorem neg_one_pow_eq_negOnePow {R : Type*} [Ring R] (k : ℕ) (i : ℤ)
    (h : Even ((k : ℤ) - i)) : (-1 : R) ^ k = ((i.negOnePow : ℤ) : R) := by
  rw [← Int.cast_negOnePow_natCast, (Int.negOnePow_eq_iff _ _).2 h]

/-- Elements of degrees `2i`, `2j` on disjoint windows supercommute. -/
theorem winPiece_supercomm {l r l' r' : ℕ} {i j : ℤ} {x y : Presented n}
    (hx : x ∈ winPiece n l r (2 * i)) (hy : y ∈ winPiece n l' r' (2 * j)) (hrl : r ≤ l') :
    y * x = (i * j).negOnePow • (x * y) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, ⟨hdu, hu⟩, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, ⟨hdv, hv⟩, rfl⟩ := hy
      have hc := (homog_wordValue u hu).supercomm (homog_wordValue v hv) hrl
      obtain ⟨c, hcu⟩ := wordDegree_eq u
      obtain ⟨c', hcv⟩ := wordDegree_eq v
      have hs : (-1 : Presented n) ^ (u.length * v.length) = (((i * j).negOnePow : ℤ) :
          Presented n) := by
        have hi : i = u.length - 2 * c := by omega
        have hj : j = v.length - 2 * c' := by omega
        refine neg_one_pow_eq_negOnePow _ _ ⟨c * v.length + c' * u.length - 2 * c * c', ?_⟩
        rw [hi, hj]
        push_cast
        ring
      rw [hc, hs, Units.smul_def, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← Int.cast_mul,
        ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
    | zero => simp
    | add y y' _ _ h h' => rw [add_mul, h, h', mul_add, smul_add]
    | smul c y _ h => rw [smul_mul_assoc, h, mul_smul_comm, smul_comm]
  | zero => simp
  | add x x' _ _ h h' => rw [mul_add, h, h', add_mul, smul_add]
  | smul c x _ h => rw [mul_smul_comm, h, smul_mul_assoc, smul_comm]

/-! ### The block embeddings -/

/-- The strand shift of a letter by `p`. -/
def shiftLetter {m p : ℕ} (h : p + (m+2) ≤ n+2) : Letter m → Letter n
  | Sum.inl j => Sum.inl ⟨j.val + p, by have := j.isLt; omega⟩
  | Sum.inr i => Sum.inr (shiftIndex h i)

theorem windowHom_wordValue {m p : ℕ} (h : p + (m+2) ≤ n+2) (w : List (Letter m)) :
    windowHom m n p h (wordValue w) = wordValue (w.map (shiftLetter h)) := by
  induction w with
  | nil => simp [wordValue]
  | cons g w ih =>
    rw [wordValue_cons, map_mul, ih, List.map_cons, wordValue_cons]
    cases g with
    | inl j => simp [letterValue, shiftLetter]
    | inr i => simp [letterValue, shiftLetter]; rfl

theorem wordDegree_map_shiftLetter {m p : ℕ} (h : p + (m+2) ≤ n+2) (w : List (Letter m)) :
    wordDegree (w.map (shiftLetter h)) = wordDegree w := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    rw [List.map_cons, wordDegree_cons, wordDegree_cons, ih]
    cases g <;> rfl

/-- `windowHom` places `ONH_{m+2}` on the strands `[p, p+m+2)`, preserving degrees. -/
theorem windowHom_mem {m p : ℕ} (h : p + (m+2) ≤ n+2) {d : ℤ} {x : Presented m}
    (hx : x ∈ onhGrading m d) : windowHom m n p h x ∈ winPiece n p (p + (m+2)) d := by
  have hx' : x ∈ Submodule.span ℤ (wordValue '' {w : List (Letter m) | wordDegree w = d}) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [windowHom_wordValue, ← hw.out, ← wordDegree_map_shiftLetter h w]
    refine word_mem_winPiece _ fun g hg => ?_
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hg
    cases g with
    | inl j => exact ⟨by simp [shiftLetter], by simp [shiftLetter]; omega⟩
    | inr i =>
      have := i.isLt
      exact ⟨by simp [shiftLetter], by simp [shiftLetter]; omega⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ c hx

/-! ### `ONH_1 = OPol_1` on one strand -/

theorem skewSign_one (a b : Fin 1 → ℕ) : OddMath.skewSign a b = 1 := by
  simp [OddMath.skewSign, OddMath.crossingCount]

/-- `x^k ↦ c x_j^k` on `OPol_1`, additively. -/
def dotAdd (n : ℕ) (j : Fin (n+2)) : SkewPolynomial 1 →+ Presented n :=
  Finsupp.liftAddHom fun a => (zmultiplesHom (Presented n) (dot n j ^ a 0))

theorem dotAdd_single (j : Fin (n+2)) (a : Fin 1 → ℕ) (c : ℤ) :
    dotAdd n j (Finsupp.single a c) = c • dot n j ^ a 0 := by
  simp [dotAdd]

/-- `ONH_1 = OPol_1 → ONH_{n+2}`, `x ↦ x_j`. -/
def dotHom (n : ℕ) (j : Fin (n+2)) : SkewPolynomial 1 →+* Presented n :=
  { dotAdd n j with
    map_one' := by
      show dotAdd n j (Finsupp.single 0 1) = 1
      rw [dotAdd_single, one_smul, Pi.zero_apply, pow_zero]
    map_mul' := fun f g => by
      show dotAdd n j (OddMath.SkewPolynomial.mul f g) = dotAdd n j f * dotAdd n j g
      induction f using Finsupp.induction_linear with
      | zero => rw [OddMath.SkewPolynomial.zero_mul, map_zero, zero_mul]
      | add f f' hf hf' =>
        rw [OddMath.SkewPolynomial.add_mul, map_add, map_add, hf, hf', add_mul]
      | single a r =>
        induction g using Finsupp.induction_linear with
        | zero => rw [OddMath.SkewPolynomial.mul_zero, map_zero, mul_zero]
        | add g g' hg hg' =>
          rw [OddMath.SkewPolynomial.mul_add, map_add, map_add, hg, hg', mul_add]
        | single b t =>
          have hm := OddMath.SkewPolynomial.mul_monomial a b r t
          rw [skewSign_one, mul_one] at hm
          rw [hm, dotAdd_single, dotAdd_single, dotAdd_single, Pi.add_apply, pow_add,
            smul_mul_smul_comm] }

theorem dotHom_single (j : Fin (n+2)) (a : Fin 1 → ℕ) (c : ℤ) :
    dotHom n j (Finsupp.single a c) = c • dot n j ^ a 0 :=
  dotAdd_single j a c

theorem dot_pow_eq (j : Fin (n+2)) (k : ℕ) :
    dot n j ^ k = wordValue (List.replicate k (Sum.inl j)) := by
  induction k with
  | zero => simp [wordValue]
  | succ k ih => rw [List.replicate_succ, wordValue_cons, pow_succ', ih]; rfl

theorem wordDegree_replicate (j : Fin (n+2)) (k : ℕ) :
    wordDegree (List.replicate k (Sum.inl j : Letter n)) = 2 * (k : ℤ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, wordDegree_cons, ih]
    simp [letterDegree]
    ring

theorem dot_pow_mem (j : Fin (n+2)) (k : ℕ) :
    dot n j ^ k ∈ winPiece n j (j + 1) (2 * (k : ℤ)) := by
  rw [dot_pow_eq, ← wordDegree_replicate j k]
  refine word_mem_winPiece _ fun g hg => ?_
  rw [List.eq_of_mem_replicate hg]
  exact ⟨le_rfl, Nat.lt_succ_self _⟩

/-- `x ↦ x_j` places `ONH_1` on the strand `j`, preserving degrees. -/
theorem dotHom_mem (j : Fin (n+2)) {d : ℤ} {f : SkewPolynomial 1} (hf : f ∈ opolGrading d) :
    dotHom n j f ∈ winPiece n j (j + 1) d := by
  rw [← Finsupp.sum_single f, map_finsuppSum]
  refine Submodule.sum_mem _ fun a ha => ?_
  show dotHom n j (Finsupp.single a (f a)) ∈ _
  rw [dotHom_single]
  have hd := NilHeckeGradedEnd.support_degree hf ha
  simp only [NilHeckeGradedEnd.pdegree, Fin.sum_univ_one] at hd
  rw [← hd]
  exact Submodule.smul_mem _ _ (dot_pow_mem j (a 0))

theorem intCast_mem_winPiece (l r : ℕ) (z : ℤ) : (z : Presented n) ∈ winPiece n l r 0 := by
  rw [← zsmul_one]
  exact Submodule.smul_mem _ z (word_mem_winPiece [] fun _ h => absurd h List.not_mem_nil)

/-- All degrees of `OPol_1` are even. -/
theorem opol_even {d : ℤ} {f : SkewPolynomial 1} (hf : f ∈ opolGrading d) (hf0 : f ≠ 0) :
    Even d := by
  by_contra hd
  have hf' : f ∈ NilHeckeGradedEnd.polynomialPiece 1 d := hf
  rw [NilHeckeGradedEnd.polynomial_odd 1 d (by rwa [Int.even_iff] at hd)] at hf'
  exact hf0 ((Submodule.mem_bot ℤ).1 hf')

theorem int_even {d x : ℤ} (hx : x ∈ intGrading d) (hx0 : x ≠ 0) : Even d := by
  rcases (hx : x = 0 ∨ d = 0) with h | h
  · exact absurd h hx0
  · rw [h]; exact Even.zero

/-! ### Super pairs -/

variable {R₁ R₂ S : Type*} [Ring R₁] [Ring R₂] [Ring S] {A₁ : ℤ → AddSubgroup R₁}
  {A₂ : ℤ → AddSubgroup R₂} {B : ℤ → AddSubgroup S}

/-- Graded maps into disjoint windows `[l, r)`, `[l', r')`, `r ≤ l'`, of `ONH_{n+2}`. -/
def SuperPair.ofWin (ι₁ : R₁ →+* Presented n) (ι₂ : R₂ →+* Presented n) {l r l' r' : ℕ}
    (h₁ : ∀ {d x}, x ∈ A₁ d → ι₁ x ∈ winPiece n l r d)
    (h₂ : ∀ {d y}, y ∈ A₂ d → ι₂ y ∈ winPiece n l' r' d) (hrl : r ≤ l')
    (e₁ : ∀ {d : ℤ} {x : R₁}, x ∈ A₁ d → x ≠ 0 → Even d)
    (e₂ : ∀ {d : ℤ} {y : R₂}, y ∈ A₂ d → y ≠ 0 → Even d) :
    SuperPair A₁ A₂ (onhGrading n) where
  ι₁ := ι₁
  ι₂ := ι₂
  map₁ hx := winPiece_le _ _ _ (h₁ hx)
  map₂ hy := winPiece_le _ _ _ (h₂ hy)
  even₁ := e₁
  even₂ := e₂
  comm hx hy := winPiece_supercomm (h₁ hx) (h₂ hy) hrl

/-- `ONH_0 = ℤ` on the left. -/
def SuperPair.intLeft [SetLike.GradedMonoid B] (ι₂ : R₂ →+* S)
    (h₂ : ∀ {d y}, y ∈ A₂ d → ι₂ y ∈ B d) (e₂ : ∀ {d : ℤ} {y : R₂}, y ∈ A₂ d → y ≠ 0 → Even d) :
    SuperPair intGrading A₂ B where
  ι₁ := Int.castRingHom S
  ι₂ := ι₂
  map₁ {d x} hx := by
    rcases (hx : x = 0 ∨ d = 0) with h | h
    · rw [h, map_zero]; exact zero_mem _
    · rw [h]; exact intCast_mem x
  map₂ := h₂
  even₁ := int_even
  even₂ := e₂
  comm {i j x y} hx _ := by
    rcases (hx : x = 0 ∨ 2 * i = 0) with h | h
    · simp [h]
    · obtain rfl : i = 0 := by omega
      simp [(Int.cast_commute x (ι₂ y)).eq]

/-- `ONH_0 = ℤ` on the right. -/
def SuperPair.intRight [SetLike.GradedMonoid B] (ι₁ : R₁ →+* S)
    (h₁ : ∀ {d x}, x ∈ A₁ d → ι₁ x ∈ B d) (e₁ : ∀ {d : ℤ} {x : R₁}, x ∈ A₁ d → x ≠ 0 → Even d) :
    SuperPair A₁ intGrading B where
  ι₁ := ι₁
  ι₂ := Int.castRingHom S
  map₁ := h₁
  map₂ {d y} hy := by
    rcases (hy : y = 0 ∨ d = 0) with h | h
    · rw [h, map_zero]; exact zero_mem _
    · rw [h]; exact intCast_mem y
  even₁ := e₁
  even₂ := int_even
  comm {i j x y} _ hy := by
    rcases (hy : y = 0 ∨ 2 * j = 0) with h | h
    · simp [h]
    · obtain rfl : j = 0 := by omega
      simp [(Int.cast_commute y (ι₁ x)).eq]

end OddMath.Frontier.OddBialgebra
