import OddMath.Frontier.LongestReversal
import OddMath.Frontier.NilCoxeterWords
import OddMath.Frontier.NilHeckeBasis

/-! EKL1111.1320v1 §3.2.4, (3.41)–(3.42), Proposition 3.7 (3.45), pp. 28–29.
Crossings of thick strands in the odd nilHecke algebra, with exact signs.

Conventions: a written product `x * y` is `x` drawn on top of `y`; the rightmost
factor acts first. `down n p k` is the written word `[p+k-1, …, p]` and
`triangle n p k` is the literal (3.11) longest word on the variables `[p, p+k)`.
The crossing (3.41) of `a` strands with `b` strands, placed at offset `p`, is
`crossAt n p a b = down n p a * down n (p+1) a * ⋯ * down n (p+b-1) a`:
its top band carries the first of the `b` strands across all `a` strands.
Out-of-range crossings are zero, so the operator identities need no bounds. -/
namespace OddMath.Frontier.StrandCrossing
open OddMath.SkewPolynomial (SkewPolynomial)
open LongestDivided LongestReversal

/-- Signed commutation `x * y = (-1)^e • (y * x)`. -/
def SignComm {R : Type*} [Ring R] (x y : R) (e : ℕ) : Prop :=
  x * y = (-1 : ℤ)^e • (y * x)

namespace SignComm
variable {R : Type*} [Ring R] {x y z : R} {e f : ℕ}

theorem of_eq (h : SignComm x y e) (he : e = f) : SignComm x y f := he ▸ h

theorem one_right (x : R) : SignComm x 1 0 := by simp [SignComm]

theorem symm (h : SignComm x y e) : SignComm y x e := by
  unfold SignComm at *
  rw [h, smul_smul, ← pow_add, Even.neg_one_pow ⟨e, rfl⟩, one_smul]

theorem mul_right (hy : SignComm x y e) (hz : SignComm x z f) :
    SignComm x (y*z) (e+f) := by
  unfold SignComm at *
  rw [← mul_assoc, hy, smul_mul_assoc, mul_assoc, hz, mul_smul_comm, smul_smul,
    ← pow_add, mul_assoc]

theorem mul_left (hx : SignComm x z e) (hy : SignComm y z f) :
    SignComm (x*y) z (e+f) :=
  (mul_right hx.symm hy.symm).symm

end SignComm

noncomputable section

/-- Operators on the actual skew polynomial ring of rank `n+2`. -/
abbrev Op (n : ℕ) := Module.End ℤ (SkewPolynomial (n+2))

theorem SignComm.apply {n : ℕ} {x y : Op n} {e : ℕ} (h : SignComm x y e)
    (f : SkewPolynomial (n+2)) : x (y f) = (-1 : ℤ)^e • y (x f) := by
  simpa only [Module.End.mul_apply, LinearMap.smul_apply] using LinearMap.congr_fun h f

theorem neg_one_smul_smul {M : Type*} [AddCommGroup M] (e : ℕ) (v : M) :
    (-1 : ℤ)^e • (-1 : ℤ)^e • v = v := by
  rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨e, rfl⟩, one_smul]

variable (n : ℕ)

/-- Crossing positions that share no strand. -/
def Far (i j : ℕ) : Prop := i+1 < j ∨ j+1 < i

theorem cross_zero (j : ℕ) (h : n+1 ≤ j) : cross n j = 0 := by
  unfold cross
  rw [dif_neg (by omega)]

/-- Distant crossings anticommute; no range hypothesis. -/
theorem cross_far {i j : ℕ} (h : Far i j) : SignComm (cross n i) (cross n j) 1 := by
  have key : ∀ p q, p+1 < q → cross n p * cross n q = -(cross n q * cross n p) := by
    intro p q hpq
    by_cases hq : q < n+1
    · exact cross_anti n p q (by omega) hq hpq
    · rw [cross_zero n q (by omega)]
      simp
  unfold SignComm
  rw [pow_one, neg_one_smul]
  rcases h with h | h
  · exact key i j h
  · rw [key j i h, neg_neg]

/-- The braid relation, sign `+`; no range hypothesis. -/
theorem cross_braid_apply (j : ℕ) (f : SkewPolynomial (n+2)) :
    cross n j (cross n (j+1) (cross n j f)) =
      cross n (j+1) (cross n j (cross n (j+1) f)) := by
  by_cases hj : j+1 < n+1
  · exact (LongestKernel.cross_braid n j hj f).symm
  · rw [cross_zero n (j+1) (by omega)]
    simp

/-- The crossing (3.41) of `a` strands with `b` strands, on the window `[p, p+a+b)`. -/
def crossAt (p a : ℕ) : ℕ → Op n
  | 0 => 1
  | b+1 => down n p a * crossAt (p+1) a b

/-- EKL (3.41) in the source position. -/
abbrev crossOp (a b : ℕ) : Op n := crossAt n 0 a b

/-- The descending blocks `down p a * down p (a+1) * ⋯ * down p (a+b-1)`. -/
def stack (p a : ℕ) : ℕ → Op n
  | 0 => 1
  | b+1 => stack p a b * down n p (a+b)

theorem right_down {x : Op n} {e : ℕ} (p k : ℕ)
    (h : ∀ j < k, SignComm x (cross n (p+j)) e) : SignComm x (down n p k) (k*e) := by
  induction k generalizing p with
  | zero =>
      show SignComm x 1 (0*e)
      rw [zero_mul]
      exact SignComm.one_right x
  | succ k ih =>
      show SignComm x (down n (p+1) k * cross n p) ((k+1)*e)
      refine (SignComm.mul_right (ih (p+1) fun j hj => ?_)
        (by simpa using h 0 (by omega))).of_eq (by ring)
      have := h (j+1) (by omega)
      rwa [show p+(j+1) = p+1+j by omega] at this

theorem left_down {y : Op n} {e : ℕ} (p k : ℕ)
    (h : ∀ j < k, SignComm (cross n (p+j)) y e) : SignComm (down n p k) y (k*e) :=
  (right_down n p k fun j hj => (h j hj).symm).symm

theorem right_triangle {x : Op n} {e : ℕ} (p k : ℕ)
    (h : ∀ j, j+1 < k → SignComm x (cross n (p+j)) e) :
    SignComm x (triangle n p k) (k.choose 2 * e) := by
  induction k with
  | zero =>
      show SignComm x 1 (Nat.choose 0 2 * e)
      simpa using SignComm.one_right x
  | succ k ih =>
      show SignComm x (triangle n p k * down n p k) _
      refine (SignComm.mul_right (ih fun j hj => h j (by omega))
        (right_down n p k fun j hj => h j (by omega))).of_eq ?_
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      ring

theorem right_crossAt {x : Op n} {e : ℕ} (p a b : ℕ)
    (h : ∀ i < b, ∀ j < a, SignComm x (cross n (p+i+j)) e) :
    SignComm x (crossAt n p a b) (b*(a*e)) := by
  induction b generalizing p with
  | zero =>
      show SignComm x 1 (0*(a*e))
      rw [zero_mul]
      exact SignComm.one_right x
  | succ b ih =>
      show SignComm x (down n p a * crossAt n (p+1) a b) _
      refine (SignComm.mul_right (right_down n p a fun j hj => by simpa using h 0 (by omega) j hj)
        (ih (p+1) fun i hi j hj => ?_)).of_eq (by ring)
      have := h (i+1) (by omega) j hj
      rwa [show p+(i+1)+j = p+1+i+j by omega] at this

theorem left_crossAt {y : Op n} {e : ℕ} (p a b : ℕ)
    (h : ∀ i < b, ∀ j < a, SignComm (cross n (p+i+j)) y e) :
    SignComm (crossAt n p a b) y (b*(a*e)) :=
  (right_crossAt n p a b fun i hi j hj => (h i hi j hj).symm).symm

/-- Two adjacent crossings of one strand with `a` strands: the case `b = 1` of the slide. -/
theorem down_pair (p a : ℕ) :
    down n p a * down n p (a+1) = cross n (p+a) * down n p a * down n (p+1) a := by
  induction a generalizing p with
  | zero => simp [down]
  | succ a ih =>
      apply LinearMap.ext
      intro f
      have ih' : ∀ g, down n (p+1) a (down n (p+1) (a+1) g) =
          cross n (p+(a+1)) (down n (p+1) a (down n (p+1+1) a g)) := by
        intro g
        have := LinearMap.congr_fun (ih (p+1)) g
        simp only [Module.End.mul_apply] at this
        rwa [show p+1+a = p+(a+1) by omega] at this
      have hs := (right_down n (x := cross n p) (e := 1) (p+1+1) a
        fun j _ => cross_far n (by unfold Far; omega)).apply
      change down n (p+1) a (cross n p (down n (p+1+1) a (cross n (p+1) (cross n p f)))) =
        cross n (p+(a+1)) (down n (p+1) a (cross n p (down n (p+1+1) a (cross n (p+1) f))))
      rw [hs, hs, map_smul, map_smul, map_smul, cross_braid_apply]
      congr 1
      exact ih' _

/-- Sliding a descending block of the lower strands up through a crossing. -/
theorem crossAt_slide (p a b : ℕ) :
    crossAt n p a (b+1) * down n p b = down n (p+a) b * crossAt n p a (b+1) := by
  induction b generalizing p with
  | zero =>
      show crossAt n p a 1 * 1 = 1 * crossAt n p a 1
      rw [mul_one, one_mul]
  | succ b ih =>
      apply LinearMap.ext
      intro f
      have ih' : ∀ g, crossAt n (p+1) a (b+1) (down n (p+1) b g) =
          down n (p+a+1) b (crossAt n (p+1) a (b+1) g) := by
        intro g
        have := LinearMap.congr_fun (ih (p+1)) g
        simp only [Module.End.mul_apply] at this
        rwa [Nat.add_right_comm p 1 a] at this
      have hX := ((right_crossAt n (x := cross n p) (e := 1) (p+1+1) a b
        fun i _ j _ => cross_far n (by unfold Far; omega)).symm.of_eq
          (show b*(a*1) = a*b by ring)).apply
      have hD := ((left_down n (y := down n (p+a+1) b) (e := b*1) p a
        fun i _ => right_down n (p+a+1) b fun j _ => cross_far n (by unfold Far; omega)).of_eq
          (show a*(b*1) = a*b by ring)).apply
      have hB : ∀ g, down n p a (down n p (a+1) g) =
          cross n (p+a) (down n p a (down n (p+1) a g)) := fun g => by
        simpa only [Module.End.mul_apply] using LinearMap.congr_fun (down_pair n p a) g
      change down n p a (crossAt n (p+1) a (b+1) (down n (p+1) b (cross n p f))) =
        down n (p+a+1) b (cross n (p+a) (down n p a (down n (p+1) a
          (crossAt n (p+1+1) a b f))))
      rw [ih']
      change down n p a (down n (p+a+1) b (down n (p+1) a
        (crossAt n (p+1+1) a b (cross n p f)))) = _
      rw [hX, map_smul, map_smul, map_smul]
      change (-1 : ℤ)^(a*b) • down n p a (down n (p+a+1) b (down n p (a+1)
        (crossAt n (p+1+1) a b f))) = _
      rw [hD, hB, neg_one_smul_smul]

theorem crossAt_last (p a b : ℕ) :
    crossAt n p a (b+1) = crossAt n p a b * down n (p+b) a := by
  induction b generalizing p with
  | zero =>
      show down n p a * 1 = 1 * down n p a
      rw [mul_one, one_mul]
  | succ b ih =>
      show down n p a * crossAt n (p+1) a (b+1) =
        (down n p a * crossAt n (p+1) a b) * down n (p+(b+1)) a
      rw [ih, mul_assoc, show p+1+b = p+(b+1) by omega]

theorem down_split (p j k : ℕ) : down n p (j+k) = down n (p+j) k * down n p j := by
  induction k with
  | zero => simp [down]
  | succ k ih =>
      rw [← Nat.add_assoc, down_last, ih, down_last, ← mul_assoc, Nat.add_assoc]

theorem triangle_add (p a b : ℕ) : triangle n p (a+b) = triangle n p a * stack n p a b := by
  induction b with
  | zero => simp [stack]
  | succ b ih =>
      show triangle n p (a+b) * down n p (a+b) = triangle n p a * (stack n p a b * down n p (a+b))
      rw [ih, mul_assoc]

/-- The inductive step for (3.45): a full descending block below the crossing. -/
theorem crossAt_down (p a b : ℕ) :
    crossAt n p a b * down n p (a+b) = down n (p+a) b * crossAt n p a b * down n (p+b) a := by
  rw [Nat.add_comm a b, down_split n p b a, ← mul_assoc, ← crossAt_last, crossAt_slide,
    crossAt_last, mul_assoc]

/-- The descending blocks factor as a triangle on the right window above the crossing. -/
theorem stack_eq (p a b : ℕ) : stack n p a b = triangle n (p+a) b * crossAt n p a b := by
  induction b with
  | zero => simp [stack, triangle, crossAt]
  | succ b ih =>
      show stack n p a b * down n p (a+b) =
        triangle n (p+a) b * down n (p+a) b * crossAt n p a (b+1)
      rw [ih, Nat.add_comm a b, down_split n p b a]
      simp only [mul_assoc]
      rw [← mul_assoc (crossAt n p a b), ← crossAt_last, crossAt_slide]

/-- EKL (3.45), first equality, on the window `[p, p+a+b)`. -/
theorem triangle_crossing (p a b : ℕ) :
    triangle n p (a+b) = triangle n p a * triangle n (p+a) b * crossAt n p a b := by
  rw [triangle_add, stack_eq, mul_assoc]

/-- Triangles on disjoint windows commute up to the product of their lengths. -/
theorem triangle_disjoint (p a b : ℕ) :
    SignComm (triangle n p a) (triangle n (p+a) b) (a.choose 2 * b.choose 2) :=
  (right_triangle n (p+a) b fun j _ =>
    (right_triangle n (x := cross n (p+a+j)) (e := 1) p a fun i _ =>
      cross_far n (by unfold Far; omega)).symm).of_eq (by ring)

/-- EKL (3.45), second equality, on the window `[p, p+a+b)`. -/
theorem triangle_crossing_swap (p a b : ℕ) :
    triangle n p (a+b) = (-1 : ℤ)^(a.choose 2 * b.choose 2) •
      (triangle n (p+a) b * triangle n p a * crossAt n p a b) := by
  rw [triangle_crossing, triangle_disjoint n p a b, smul_mul_assoc]

theorem D_eq_triangle : (D (n+2) : Op n) = triangle n 0 (n+2) :=
  LinearMap.ext fun f => by rw [D_eq_actNat, triangle_source]

/-- EKL Proposition 3.7 for the actual operator `D_{a+b}` of (2.36). -/
theorem D_crossing (a b : ℕ) (hab : a+b = n+2) :
    (D (n+2) : Op n) = triangle n 0 a * triangle n a b * crossOp n a b ∧
    (D (n+2) : Op n) = (-1 : ℤ)^(a.choose 2 * b.choose 2) •
      (triangle n a b * triangle n 0 a * crossOp n a b) := by
  have h1 := triangle_crossing n 0 a b
  have h2 := triangle_crossing_swap n 0 a b
  rw [Nat.zero_add, hab] at h1 h2
  rw [D_eq_triangle]
  exact ⟨h1, h2⟩

/-- EKL (3.42), first identity: `a` strands crossing `b+c` strands. -/
theorem crossAt_add (p a b c : ℕ) :
    crossAt n p a (b+c) = crossAt n p a b * crossAt n (p+b) a c := by
  induction b generalizing p with
  | zero => simp [crossAt]
  | succ b ih =>
      rw [Nat.add_right_comm]
      show down n p a * crossAt n (p+1) a (b+c) =
        (down n p a * crossAt n (p+1) a b) * crossAt n (p+(b+1)) a c
      rw [ih, mul_assoc, show p+1+b = p+(b+1) by omega]

/-- EKL (3.42), second identity: `a+b` strands crossing `c` strands, exact sign. -/
theorem crossAt_split (p a b c : ℕ) :
    crossAt n p (a+b) c = (-1 : ℤ)^(a*b*c.choose 2) •
      (crossAt n (p+a) b c * crossAt n p a c) := by
  induction c with
  | zero => simp [crossAt]
  | succ c ih =>
      have hc : SignComm (crossAt n p a c) (down n (p+a+c) b) (c*a*b) :=
        (left_crossAt n (y := down n (p+a+c) b) (e := b*1) p a c fun i _ j _ =>
          right_down n (p+a+c) b fun k _ => cross_far n (by unfold Far; omega)).of_eq
            (by ring)
      rw [crossAt_last, ih, down_split n (p+c) a b, crossAt_last n (p+a) b c,
        crossAt_last n p a c, show p+c+a = p+a+c by omega]
      rw [smul_mul_assoc]
      simp only [mul_assoc]
      rw [← mul_assoc (crossAt n p a c), hc, smul_mul_assoc, mul_smul_comm, smul_smul,
        ← pow_add]
      simp only [mul_assoc]
      congr 2
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      ring

/-! ### The odd nilHecke algebra -/

open NilHeckeAction NilCoxeterWords

/-- A word of natural-number letters, as a word of the rank-`n+2` algebra. -/
def natWord (l : List ℕ) : Word n :=
  l.filterMap fun j => if h : j < n+1 then some ⟨j,h⟩ else none

theorem natWord_values (l : List ℕ) (hl : ∀ j ∈ l, j < n+1) :
    (natWord n l).map Fin.val = l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      obtain ⟨hj, hl⟩ := List.forall_mem_cons.mp hl
      change (List.filterMap _ (j :: l)).map Fin.val = j :: l
      simp only [List.filterMap_cons, dif_pos hj, List.map_cons]
      exact congrArg (j :: ·) (ih hl)

theorem action_natWord (l : List ℕ) (hl : ∀ j ∈ l, j < n+1) :
    action n (product (natWord n l)) = actNat n l := by
  apply LinearMap.ext
  intro f
  rw [action_product, ← actNat_map_fin, natWord_values n l hl]

/-- Letters of `down n p k`. -/
def downList (p k : ℕ) : List ℕ := (List.range' p k).reverse

/-- Letters of `triangle n p k`: the source word (2.36) shifted by `p`. -/
def triList (p k : ℕ) : List ℕ := (coxeterWord k).map (p + ·)

/-- Letters of `crossAt n p a b`. -/
def crossList (p a : ℕ) : ℕ → List ℕ
  | 0 => []
  | b+1 => downList p a ++ crossList (p+1) a b

theorem mem_downList {p k j : ℕ} (h : j ∈ downList p k) : p ≤ j ∧ j < p+k := by
  simpa [downList, List.mem_range'_1] using h

theorem mem_triList {p k j : ℕ} (h : j ∈ triList p k) : j+1 < p+k := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  have := coxeterWord_bound hi
  omega

theorem mem_crossList {p a b j : ℕ} (h : j ∈ crossList p a b) : j+1 < p+a+b := by
  induction b generalizing p with
  | zero => simp [crossList] at h
  | succ b ih =>
      rcases List.mem_append.mp h with h | h
      · have := mem_downList h
        omega
      · have := ih h
        omega

theorem actNat_downList (p k : ℕ) : actNat n (downList p k) = down n p k :=
  LinearMap.ext fun f => by rw [downList, actNat_reverse_range, down_sweep]

theorem triList_succ (p k : ℕ) : triList p (k+1) = triList p k ++ downList p k := by
  simp [triList, downList, coxeterWord, List.map_reverse, List.range_eq_range',
    List.map_add_range']

theorem actNat_triList (p k : ℕ) : actNat n (triList p k) = triangle n p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      apply LinearMap.ext
      intro f
      rw [triList_succ, actNat_append, ih, actNat_downList]
      rfl

theorem actNat_crossList (p a b : ℕ) : actNat n (crossList p a b) = crossAt n p a b := by
  induction b generalizing p with
  | zero => rfl
  | succ b ih =>
      apply LinearMap.ext
      intro f
      change actNat n (downList p a ++ crossList (p+1) a b) f = _
      rw [actNat_append, ih, actNat_downList]
      rfl

/-- The word of `D_a` on the strands `[p, p+a)`. -/
abbrev triWord (p a : ℕ) : Word n := natWord n (triList p a)

/-- The word of the crossing (3.41) on the strands `[p, p+a+b)`. -/
abbrev crossWord (p a b : ℕ) : Word n := natWord n (crossList p a b)

theorem action_triWord (p a : ℕ) (h : p+a ≤ n+2) :
    action n (product (triWord n p a)) = triangle n p a := by
  rw [action_natWord n _ fun j hj => by have := mem_triList hj; omega, actNat_triList]

theorem action_crossWord (p a b : ℕ) (h : p+a+b ≤ n+2) :
    action n (product (crossWord n p a b)) = crossAt n p a b := by
  rw [action_natWord n _ fun j hj => by have := mem_crossList hj; omega, actNat_crossList]

theorem action_source :
    action n (product (wordIn n (n+2) le_rfl)) = (D (n+2) : Op n) := by
  rw [action_product]
  rfl

/-- EKL Proposition 3.7 (3.45) in the presented odd nilHecke algebra, `a+b = n+2`:
`D_{a+b} = D_a D_b X_{a,b} = (-1)^{C(a,2) C(b,2)} D_b D_a X_{a,b}`, where `D_{a+b}` is the
literal source word (2.36), `D_a` sits on the left `a` strands, `D_b` on the right `b`
strands, and `X_{a,b}` is the crossing (3.41) below them. -/
theorem prop_3_7 (a b : ℕ) (hab : a+b = n+2) :
    product (wordIn n (n+2) le_rfl) =
        product (triWord n 0 a) * product (triWord n a b) * product (crossWord n 0 a b) ∧
    product (wordIn n (n+2) le_rfl) = (-1 : ℤ)^(a.choose 2 * b.choose 2) •
        (product (triWord n a b) * product (triWord n 0 a) * product (crossWord n 0 a b)) := by
  obtain ⟨h1, h2⟩ := D_crossing n a b hab
  constructor
  · apply NilHeckeBasis.action_injective n
    rw [map_mul, map_mul, action_source, action_triWord n 0 a (by omega),
      action_triWord n a b (by omega), action_crossWord n 0 a b (by omega)]
    exact h1
  · apply NilHeckeBasis.action_injective n
    rw [map_zsmul, map_mul, map_mul, action_source, action_triWord n 0 a (by omega),
      action_triWord n a b (by omega), action_crossWord n 0 a b (by omega)]
    exact h2

/-- EKL (3.42) in the presented odd nilHecke algebra, `a+b+c = n+2`. -/
theorem crossing_3_42 (a b c : ℕ) (habc : a+b+c = n+2) :
    product (crossWord n 0 a (b+c)) =
        product (crossWord n 0 a b) * product (crossWord n b a c) ∧
    product (crossWord n 0 (a+b) c) = (-1 : ℤ)^(a*b*c.choose 2) •
        (product (crossWord n a b c) * product (crossWord n 0 a c)) := by
  constructor
  · apply NilHeckeBasis.action_injective n
    rw [map_mul, action_crossWord n 0 a (b+c) (by omega), action_crossWord n 0 a b (by omega),
      action_crossWord n b a c (by omega), crossAt_add, Nat.zero_add]
  · apply NilHeckeBasis.action_injective n
    rw [map_zsmul, map_mul, action_crossWord n 0 (a+b) c (by omega),
      action_crossWord n a b c (by omega), action_crossWord n 0 a c (by omega), crossAt_split,
      Nat.zero_add]

end
end OddMath.Frontier.StrandCrossing
