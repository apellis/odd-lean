import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Matrix.Block
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Graded idempotent matrices and the graded Grothendieck group

`R` is a ring with a `ℤ`-grading `A : ℤ → AddSubgroup R` satisfying `1 ∈ A 0` and
`A d * A e ⊆ A (d + e)` (`SetLike.GradedMonoid A`). No direct sum decomposition is used.

Conventions. A shift vector `s : ι → ℤ` stands for the graded free module
`⊕ᵢ R{s i}`, where `R{k}` is `R` with its generator in degree `k` (`R{k}_d = R_{d-k}`).
A matrix `u : Matrix ι κ R` is a degree-zero map from `(ι, s)` to `(κ, t)` when
`u i j ∈ A (s i - t j)` (`IsHom`); such matrices compose. A graded idempotent
`(n, s, e)` (`GIdem`) is `e : Matrix (Fin n) (Fin n) R` of degree zero from `(Fin n, s)`
to itself with `e * e = e`; it represents the graded projective module `R^n{s} · e`.

Murray–von Neumann equivalence `MvN s e t f`: there are degree-zero `u`, `v` with
`u * v = e`, `v * u = f`, `e * u * f = u`, `f * v * e = v`. It is formulated for arbitrary
finite index types; on graded idempotents it is an equivalence relation.

Block sum (`GIdem.sum`) and the grading shift `P{k}` (`GIdem.shift`, `s ↦ s + k`) descend
to the quotient `GProj A`, a commutative monoid with an additive `ℤ`-action by shifts.
`K0 A` is its Grothendieck group, a module over `ℤ[T;T⁻¹]` with `T k` acting by `{k}`;
in particular `q = T 1` acts by `{1}`, and `[R{k}] = T k • [R]`. If the grading of `R`
uses a different unit (for instance all degrees even), rescale `A` first.

The Grothendieck group of a commutative monoid `M` is realised as the quotient of the free
abelian group on `M` by the relations `[a + b] - [a] - [b]`; it has the universal property
of the group completion (`GrothendieckGroup.lift`, `GrothendieckGroup.hom_ext`).
-/

noncomputable section
open Matrix

namespace OddMath.Frontier.GradedK0

variable {R : Type*} [Ring R] (A : ℤ → AddSubgroup R)

section Hom

variable {ι κ μ ι' κ' : Type*}

/-- `u` is homogeneous of degree zero from `(ι, s)` to `(κ, t)`: `u i j ∈ A (s i - t j)`. -/
def IsHom (s : ι → ℤ) (t : κ → ℤ) (u : Matrix ι κ R) : Prop :=
  ∀ i j, u i j ∈ A (s i - t j)

variable {A}

theorem mem_of_deg_eq {a b : ℤ} {x : R} (h : x ∈ A a) (hab : a = b) : x ∈ A b := hab ▸ h

namespace IsHom

variable {s : ι → ℤ} {t : κ → ℤ} {r : μ → ℤ}

theorem zero : IsHom A s t 0 := fun _ _ => zero_mem _

theorem add {u u' : Matrix ι κ R} (hu : IsHom A s t u) (hu' : IsHom A s t u') :
    IsHom A s t (u + u') := fun i j => add_mem (hu i j) (hu' i j)

theorem neg {u : Matrix ι κ R} (hu : IsHom A s t u) : IsHom A s t (-u) :=
  fun i j => neg_mem (hu i j)

theorem sub {u u' : Matrix ι κ R} (hu : IsHom A s t u) (hu' : IsHom A s t u') :
    IsHom A s t (u - u') := fun i j => sub_mem (hu i j) (hu' i j)

theorem mul [SetLike.GradedMonoid A] [Fintype κ] {u : Matrix ι κ R} {v : Matrix κ μ R}
    (hu : IsHom A s t u) (hv : IsHom A t r v) : IsHom A s r (u * v) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mem_of_deg_eq (SetLike.GradedMul.mul_mem (hu i k) (hv k j)) (by ring)

theorem one [SetLike.GradedMonoid A] [DecidableEq ι] : IsHom A s s (1 : Matrix ι ι R) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [sub_self]
    exact SetLike.GradedOne.one_mem
  · exact zero_mem _

theorem shift (k : ℤ) {u : Matrix ι κ R} (hu : IsHom A s t u) :
    IsHom A (fun i => s i + k) (fun j => t j + k) u :=
  fun i j => mem_of_deg_eq (hu i j) (by ring)

theorem unshift (k : ℤ) {u : Matrix ι κ R}
    (hu : IsHom A (fun i => s i + k) (fun j => t j + k) u) :
    IsHom A s t u :=
  fun i j => mem_of_deg_eq (hu i j) (by ring)

theorem fromBlocks {s' : ι' → ℤ} {t' : κ' → ℤ} {a : Matrix ι κ R} {b : Matrix ι κ' R}
    {c : Matrix ι' κ R} {d : Matrix ι' κ' R} (ha : IsHom A s t a) (hb : IsHom A s t' b)
    (hc : IsHom A s' t c) (hd : IsHom A s' t' d) :
    IsHom A (Sum.elim s s') (Sum.elim t t') (Matrix.fromBlocks a b c d) := by
  rintro (i | i) (j | j)
  exacts [ha i j, hb i j, hc i j, hd i j]

end IsHom

variable (A) in
/-- Degree-zero endomorphisms of `(ι, s)` form a subring. -/
def homSubring [SetLike.GradedMonoid A] [Fintype ι] [DecidableEq ι] (s : ι → ℤ) :
    Subring (Matrix ι ι R) where
  carrier := {x | IsHom A s s x}
  mul_mem' := IsHom.mul
  one_mem' := IsHom.one
  add_mem' := IsHom.add
  zero_mem' := IsHom.zero
  neg_mem' := IsHom.neg

theorem mem_homSubring [SetLike.GradedMonoid A] [Fintype ι] [DecidableEq ι] {s : ι → ℤ}
    {x : Matrix ι ι R} : x ∈ homSubring A s ↔ IsHom A s s x := Iff.rfl

end Hom

section MvN

variable {ι κ μ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ι']
  [Fintype κ']

/-- Murray–von Neumann equivalence of `e` on `(ι, s)` and `f` on `(κ, t)` through
degree-zero matrices. -/
def MvN (s : ι → ℤ) (e : Matrix ι ι R) (t : κ → ℤ) (f : Matrix κ κ R) : Prop :=
  ∃ (u : Matrix ι κ R) (v : Matrix κ ι R), IsHom A s t u ∧ IsHom A t s v ∧
    u * v = e ∧ v * u = f ∧ e * u * f = u ∧ f * v * e = v

variable {A}

namespace MvN

variable {s : ι → ℤ} {t : κ → ℤ} {r : μ → ℤ} {e : Matrix ι ι R}
  {f : Matrix κ κ R} {g : Matrix μ μ R}

theorem refl (he : IsHom A s s e) (hee : e * e = e) : MvN A s e s e :=
  ⟨e, e, he, he, hee, hee, by rw [hee, hee], by rw [hee, hee]⟩

theorem symm (h : MvN A s e t f) : MvN A t f s e := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  exact ⟨v, u, hv, hu, h2, h1, h4, h3⟩

theorem trans [SetLike.GradedMonoid A] (hee : e * e = e) (hff : f * f = f) (hgg : g * g = g)
    (h : MvN A s e t f) (h' : MvN A t f r g) : MvN A s e r g := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  obtain ⟨u', v', hu', hv', h1', h2', h3', h4'⟩ := h'
  have eu : e * u = u := by
    conv_lhs => rw [← h3]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hee, h3]
  have uf : u * f = u := by
    conv_lhs => rw [← h3]
    rw [Matrix.mul_assoc, hff, h3]
  have ve : v * e = v := by
    conv_lhs => rw [← h4]
    rw [Matrix.mul_assoc, hee, h4]
  have ug : u' * g = u' := by
    conv_lhs => rw [← h3']
    rw [Matrix.mul_assoc, hgg, h3']
  have gv : g * v' = v' := by
    conv_lhs => rw [← h4']
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg, h4']
  have vf : v' * f = v' := by
    conv_lhs => rw [← h4']
    rw [Matrix.mul_assoc, hff, h4']
  refine ⟨u * u', v' * v, hu.mul hu', hv'.mul hv, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc u' v', h1', ← Matrix.mul_assoc, uf, h1]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc v u, h2, ← Matrix.mul_assoc, vf, h2']
  · rw [← Matrix.mul_assoc, eu, Matrix.mul_assoc, ug]
  · rw [← Matrix.mul_assoc, gv, Matrix.mul_assoc, ve]

/-- Relabelling the index set along an equivalence. -/
theorem of_equiv [SetLike.GradedMonoid A] (σ : ι ≃ κ) (he : IsHom A s s e) (hee : e * e = e)
    (hs : ∀ i, t (σ i) = s i) (hf : ∀ i j, f (σ i) (σ j) = e i j) : MvN A s e t f := by
  have hf' : f = e.submatrix σ.symm σ.symm := by
    ext k l
    rw [submatrix_apply, ← hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have ht : ∀ k, t k = s (σ.symm k) := fun k => by rw [← hs, Equiv.apply_symm_apply]
  subst hf'
  have k1 : e.submatrix id σ.symm * e.submatrix σ.symm id = e := by
    rw [← submatrix_mul _ _ _ _ _ σ.symm.bijective, hee, submatrix_id_id]
  have k2 : e.submatrix σ.symm id * e.submatrix id σ.symm = e.submatrix σ.symm σ.symm := by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hee]
  have k3 : e * e.submatrix id σ.symm = e.submatrix id σ.symm := by
    have h := submatrix_mul e e id id σ.symm Function.bijective_id
    rw [submatrix_id_id, hee] at h
    exact h.symm
  have k4 : e.submatrix id σ.symm * e.submatrix σ.symm σ.symm = e.submatrix id σ.symm := by
    rw [← submatrix_mul _ _ _ _ _ σ.symm.bijective, hee]
  have k5 : e.submatrix σ.symm σ.symm * e.submatrix σ.symm id = e.submatrix σ.symm id := by
    rw [← submatrix_mul _ _ _ _ _ σ.symm.bijective, hee]
  have k6 : e.submatrix σ.symm id * e = e.submatrix σ.symm id := by
    have h := submatrix_mul e e σ.symm id id Function.bijective_id
    rw [submatrix_id_id, hee] at h
    exact h.symm
  refine ⟨e.submatrix id σ.symm, e.submatrix σ.symm id, ?_, ?_, k1, k2, ?_, ?_⟩
  · intro i k
    rw [ht]
    exact he _ _
  · intro k i
    rw [ht]
    exact he _ _
  · rw [k3, k4]
  · rw [k5, k6]

theorem shift (k : ℤ) (h : MvN A s e t f) :
    MvN A (fun i => s i + k) e (fun j => t j + k) f := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  exact ⟨u, v, hu.shift k, hv.shift k, h1, h2, h3, h4⟩

theorem sum {s' : ι' → ℤ} {t' : κ' → ℤ} {e' : Matrix ι' ι' R} {f' : Matrix κ' κ' R}
    (h : MvN A s e t f) (h' : MvN A s' e' t' f') :
    MvN A (Sum.elim s s') (fromBlocks e 0 0 e') (Sum.elim t t') (fromBlocks f 0 0 f') := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  obtain ⟨u', v', hu', hv', h1', h2', h3', h4'⟩ := h'
  refine ⟨fromBlocks u 0 0 u', fromBlocks v 0 0 v', hu.fromBlocks IsHom.zero IsHom.zero hu',
    hv.fromBlocks IsHom.zero IsHom.zero hv', ?_, ?_, ?_, ?_⟩ <;>
  simp [fromBlocks_multiply, *]

end MvN

theorem fromBlocks_idem {e : Matrix ι ι R} {e' : Matrix ι' ι' R} (h : e * e = e)
    (h' : e' * e' = e') : fromBlocks e 0 0 e' * fromBlocks e 0 0 e' = fromBlocks e 0 0 e' := by
  simp [fromBlocks_multiply, h, h']

end MvN

/-! ### Graded idempotents -/

/-- A graded idempotent `(n, s, e)`: the graded projective module `R^n{s} · e`. -/
structure GIdem where
  /-- Rank of the ambient free module. -/
  n : ℕ
  /-- Shifts: the `i`-th generator sits in degree `s i`. -/
  s : Fin n → ℤ
  /-- The idempotent matrix. -/
  e : Matrix (Fin n) (Fin n) R
  hom : IsHom A s s e
  idem : e * e = e

variable {A}

namespace GIdem

variable [SetLike.GradedMonoid A]

instance setoid : Setoid (GIdem A) where
  r P Q := MvN A P.s P.e Q.s Q.e
  iseqv :=
    { refl := fun P => MvN.refl P.hom P.idem
      symm := MvN.symm
      trans := fun {P Q S} h h' => MvN.trans P.idem Q.idem S.idem h h' }

theorem equiv_def {P Q : GIdem A} : P ≈ Q ↔ MvN A P.s P.e Q.s Q.e := Iff.rfl

/-- Transport of a graded idempotent on a finite index set to `Fin n`. -/
def ofEquiv {ι : Type*} [Fintype ι] (s : ι → ℤ) (e : Matrix ι ι R) (hom : IsHom A s s e)
    (idem : e * e = e) {n : ℕ} (σ : ι ≃ Fin n) : GIdem A where
  n := n
  s := s ∘ σ.symm
  e := e.submatrix σ.symm σ.symm
  hom := fun _ _ => hom _ _
  idem := by rw [← submatrix_mul _ _ _ _ _ σ.symm.bijective, idem]

theorem mvn_ofEquiv {ι : Type*} [Fintype ι] (s : ι → ℤ) (e : Matrix ι ι R)
    (hom : IsHom A s s e) (idem : e * e = e) {n : ℕ} (σ : ι ≃ Fin n) :
    MvN A s e (ofEquiv s e hom idem σ).s (ofEquiv s e hom idem σ).e :=
  MvN.of_equiv σ hom idem (fun i => by simp [ofEquiv]) (fun i j => by simp [ofEquiv])

/-- The graded free module `R^m{t}`. -/
def free {m : ℕ} (t : Fin m → ℤ) : GIdem A := ⟨m, t, 1, IsHom.one, mul_one 1⟩

/-- The graded free module `R{k}` of rank one. -/
def single (k : ℤ) : GIdem A := free fun _ : Fin 1 => k

/-- The zero module. -/
def zero : GIdem A := ⟨0, Fin.elim0, 0, fun i => i.elim0, mul_zero 0⟩

/-- Block sum `P ⊕ Q`. -/
def sum (P Q : GIdem A) : GIdem A :=
  ofEquiv (Sum.elim P.s Q.s) (fromBlocks P.e 0 0 Q.e)
    (P.hom.fromBlocks IsHom.zero IsHom.zero Q.hom) (fromBlocks_idem P.idem Q.idem) finSumFinEquiv

theorem mvn_sum (P Q : GIdem A) :
    MvN A (Sum.elim P.s Q.s) (fromBlocks P.e 0 0 Q.e) (P.sum Q).s (P.sum Q).e :=
  mvn_ofEquiv _ _ _ _ _

/-- Grading shift `P{k}`: all generators move up by `k`. -/
def shift (k : ℤ) (P : GIdem A) : GIdem A :=
  ⟨P.n, fun i => P.s i + k, P.e, P.hom.shift k, P.idem⟩

theorem sum_congr {P P' Q Q' : GIdem A} (h : P ≈ P') (h' : Q ≈ Q') : P.sum Q ≈ P'.sum Q' :=
  MvN.trans (P.sum Q).idem (fromBlocks_idem P'.idem Q'.idem) (P'.sum Q').idem
    (MvN.trans (P.sum Q).idem (fromBlocks_idem P.idem Q.idem) (fromBlocks_idem P'.idem Q'.idem)
      (mvn_sum P Q).symm (MvN.sum h h')) (mvn_sum P' Q')

theorem sum_comm (P Q : GIdem A) : P.sum Q ≈ Q.sum P := by
  refine MvN.trans (P.sum Q).idem (fromBlocks_idem P.idem Q.idem) (Q.sum P).idem
    (mvn_sum P Q).symm (MvN.trans (fromBlocks_idem P.idem Q.idem)
      (fromBlocks_idem Q.idem P.idem) (Q.sum P).idem ?_ (mvn_sum Q P))
  refine MvN.of_equiv (Equiv.sumComm _ _) (P.hom.fromBlocks IsHom.zero IsHom.zero Q.hom)
    (fromBlocks_idem P.idem Q.idem) ?_ ?_
  · rintro (i | i) <;> rfl
  · rintro (i | i) (j | j) <;> rfl

theorem sum_assoc (P Q S : GIdem A) : (P.sum Q).sum S ≈ P.sum (Q.sum S) := by
  have i1 := fromBlocks_idem (P.sum Q).idem S.idem
  have i2 := fromBlocks_idem (fromBlocks_idem P.idem Q.idem) S.idem
  have i3 := fromBlocks_idem P.idem (fromBlocks_idem Q.idem S.idem)
  have i4 := fromBlocks_idem P.idem (Q.sum S).idem
  have h1 : MvN A _ _ _ _ := (mvn_sum (P.sum Q) S).symm
  have h2 : MvN A _ _ _ _ := MvN.sum (mvn_sum P Q).symm (MvN.refl S.hom S.idem)
  have h3 : MvN A (Sum.elim (Sum.elim P.s Q.s) S.s) (fromBlocks (fromBlocks P.e 0 0 Q.e) 0 0 S.e)
      (Sum.elim P.s (Sum.elim Q.s S.s)) (fromBlocks P.e 0 0 (fromBlocks Q.e 0 0 S.e)) := by
    refine MvN.of_equiv (Equiv.sumAssoc _ _ _)
      ((P.hom.fromBlocks IsHom.zero IsHom.zero Q.hom).fromBlocks IsHom.zero IsHom.zero S.hom)
      i2 ?_ ?_
    · rintro ((i | i) | i) <;> rfl
    · rintro ((i | i) | i) ((j | j) | j) <;> rfl
  have h4 : MvN A _ _ _ _ := MvN.sum (MvN.refl P.hom P.idem) (mvn_sum Q S)
  have h5 : MvN A _ _ _ _ := mvn_sum P (Q.sum S)
  exact MvN.trans (P.sum Q |>.sum S).idem i1 (P.sum (Q.sum S)).idem h1 <|
    MvN.trans i1 i2 (P.sum (Q.sum S)).idem h2 <| MvN.trans i2 i3 (P.sum (Q.sum S)).idem h3 <|
    MvN.trans i3 i4 (P.sum (Q.sum S)).idem h4 h5

theorem zero_sum (P : GIdem A) : zero.sum P ≈ P := by
  have i1 := fromBlocks_idem (zero (A := A)).idem P.idem
  refine MvN.trans (zero.sum P).idem i1 P.idem (mvn_sum zero P).symm ?_
  refine MvN.of_equiv (Equiv.emptySum (Fin 0) (Fin P.n))
    ((zero (A := A)).hom.fromBlocks IsHom.zero IsHom.zero P.hom) i1 ?_ ?_
  · rintro (i | i)
    exacts [i.elim0, rfl]
  · rintro (i | i) (j | j)
    exacts [i.elim0, i.elim0, j.elim0, rfl]

theorem shift_congr (k : ℤ) {P Q : GIdem A} (h : P ≈ Q) : P.shift k ≈ Q.shift k :=
  MvN.shift k h

theorem shift_sum (k : ℤ) (P Q : GIdem A) :
    (P.sum Q).shift k ≈ (P.shift k).sum (Q.shift k) := by
  refine MvN.of_equiv (Equiv.refl _) ((P.sum Q).shift k).hom (P.sum Q).idem ?_ (fun _ _ => rfl)
  intro i
  show Sum.elim (fun i => P.s i + k) (fun i => Q.s i + k) (finSumFinEquiv.symm i) =
    Sum.elim P.s Q.s (finSumFinEquiv.symm i) + k
  generalize finSumFinEquiv.symm i = x
  cases x <;> rfl

theorem shift_zero' (P : GIdem A) : P.shift 0 ≈ P :=
  MvN.of_equiv (Equiv.refl _) (P.shift 0).hom P.idem (fun i => (add_zero (P.s i)).symm)
    (fun _ _ => rfl)

theorem shift_shift (a b : ℤ) (P : GIdem A) : (P.shift b).shift a ≈ P.shift (a + b) :=
  MvN.of_equiv (Equiv.refl _) ((P.shift b).shift a).hom P.idem
    (fun i => by simp only [shift, Equiv.refl_apply]; ring) (fun _ _ => rfl)

theorem shift_zero_module (k : ℤ) : (zero (A := A)).shift k ≈ zero :=
  MvN.of_equiv (Equiv.refl _) ((zero (A := A)).shift k).hom (zero (A := A)).idem
    (fun i => i.elim0) (fun i => i.elim0)

end GIdem

/-! ### The monoid of graded projectives -/

variable (A) in
/-- Isomorphism classes of graded projectives `R^n{s} · e`: graded idempotents up to
Murray–von Neumann equivalence. -/
def GProj [SetLike.GradedMonoid A] : Type _ := Quotient (GIdem.setoid (A := A))

namespace GProj

variable [SetLike.GradedMonoid A]

/-- The class of a graded idempotent. -/
def mk (P : GIdem A) : GProj A := Quotient.mk _ P

theorem mk_eq_mk {P Q : GIdem A} : mk P = mk Q ↔ P ≈ Q := Quotient.eq

@[elab_as_elim]
theorem ind {motive : GProj A → Prop} (h : ∀ P, motive (mk P)) (x : GProj A) : motive x :=
  Quotient.ind h x

instance : Zero (GProj A) := ⟨mk GIdem.zero⟩

instance : Add (GProj A) :=
  ⟨Quotient.map₂ GIdem.sum fun _ _ h _ _ h' => GIdem.sum_congr h h'⟩

theorem mk_add (P Q : GIdem A) : mk P + mk Q = mk (P.sum Q) := rfl

theorem zero_def : (0 : GProj A) = mk GIdem.zero := rfl

instance : AddCommMonoid (GProj A) where
  add_assoc := by
    refine ind fun P => ind fun Q => ind fun S => ?_
    simp only [mk_add, mk_eq_mk]
    exact GIdem.sum_assoc P Q S
  zero_add := by
    refine ind fun P => ?_
    simp only [zero_def, mk_add, mk_eq_mk]
    exact GIdem.zero_sum P
  add_zero := by
    refine ind fun P => ?_
    simp only [zero_def, mk_add, mk_eq_mk]
    exact Setoid.trans (GIdem.sum_comm P _) (GIdem.zero_sum P)
  add_comm := by
    refine ind fun P => ind fun Q => ?_
    simp only [mk_add, mk_eq_mk]
    exact GIdem.sum_comm P Q
  nsmul := nsmulRec

/-- The shift `{k}` as an additive endomorphism. -/
def shift (k : ℤ) : GProj A →+ GProj A where
  toFun := Quotient.map (GIdem.shift k) fun _ _ h => GIdem.shift_congr k h
  map_zero' := mk_eq_mk.2 (GIdem.shift_zero_module k)
  map_add' := by
    refine ind fun P => ind fun Q => ?_
    exact mk_eq_mk.2 (GIdem.shift_sum k P Q)

theorem shift_mk (k : ℤ) (P : GIdem A) : shift k (mk P) = mk (P.shift k) := rfl

theorem shift_zero (x : GProj A) : shift 0 x = x := by
  induction x using ind with
  | h P => exact mk_eq_mk.2 (GIdem.shift_zero' P)

theorem shift_shift (a b : ℤ) (x : GProj A) : shift a (shift b x) = shift (a + b) x := by
  induction x using ind with
  | h P => exact mk_eq_mk.2 (GIdem.shift_shift a b P)

end GProj

/-! ### Grothendieck group of a commutative monoid -/

section Grothendieck

variable (M : Type*) [AddCommMonoid M]

/-- Additivity relations `[a + b] - [a] - [b]` in the free abelian group on `M`. -/
def additivityRelations : AddSubgroup (FreeAbelianGroup M) :=
  AddSubgroup.closure {x | ∃ a b : M, x =
    FreeAbelianGroup.of (a + b) - FreeAbelianGroup.of a - FreeAbelianGroup.of b}

/-- The Grothendieck group (group completion) of a commutative monoid. -/
def GrothendieckGroup : Type _ := FreeAbelianGroup M ⧸ additivityRelations M

instance : AddCommGroup (GrothendieckGroup M) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup M ⧸ additivityRelations M))

namespace GrothendieckGroup

variable {M}

/-- The canonical map to the Grothendieck group. -/
def of : M →+ GrothendieckGroup M :=
  AddMonoidHom.mk' (fun a => (QuotientAddGroup.mk (FreeAbelianGroup.of a) :
    FreeAbelianGroup M ⧸ additivityRelations M)) fun a b => by
    have h : (QuotientAddGroup.mk (FreeAbelianGroup.of (a + b) - FreeAbelianGroup.of a -
        FreeAbelianGroup.of b) : FreeAbelianGroup M ⧸ additivityRelations M) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.subset_closure ⟨a, b, rfl⟩)
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, sub_sub, sub_eq_zero] at h
    exact h

variable {G : Type*} [AddCommGroup G]

/-- Universal property: additive maps from `M` to an abelian group factor uniquely. -/
def lift (f : M →+ G) : GrothendieckGroup M →+ G :=
  QuotientAddGroup.lift (additivityRelations M) (FreeAbelianGroup.lift f) <| by
    rw [additivityRelations, AddSubgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    simp [AddMonoidHom.mem_ker]

@[simp] theorem lift_of (f : M →+ G) (a : M) : lift f (of a) = f a := by
  show QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk _) = _
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift.of]

theorem hom_ext {f g : GrothendieckGroup M →+ G} (h : ∀ a, f (of a) = g (of a)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ (FreeAbelianGroup.lift.ext _ _ h)

variable {N : Type*} [AddCommMonoid N]

/-- Functoriality. -/
def map (g : M →+ N) : GrothendieckGroup M →+ GrothendieckGroup N := lift (of.comp g)

@[simp] theorem map_of (g : M →+ N) (a : M) : map g (of a) = of (g a) := lift_of _ _

/-- Functoriality for isomorphisms. -/
def mapEquiv (g : M ≃+ N) : GrothendieckGroup M ≃+ GrothendieckGroup N where
  toFun := map g.toAddMonoidHom
  invFun := map g.symm.toAddMonoidHom
  left_inv x := by
    have : (map g.symm.toAddMonoidHom).comp (map g.toAddMonoidHom) = AddMonoidHom.id _ :=
      hom_ext fun a => by simp
    exact DFunLike.congr_fun this x
  right_inv x := by
    have : (map g.toAddMonoidHom).comp (map g.symm.toAddMonoidHom) = AddMonoidHom.id _ :=
      hom_ext fun a => by simp
    exact DFunLike.congr_fun this x
  map_add' := map_add _

@[simp] theorem mapEquiv_of (g : M ≃+ N) (a : M) : mapEquiv g (of a) = of (g a) := map_of _ _

end GrothendieckGroup

end Grothendieck

/-! ### The graded Grothendieck group -/

variable (A) in
/-- `K₀` of graded projectives: the Grothendieck group of `GProj A`. -/
def K0 [SetLike.GradedMonoid A] : Type _ := GrothendieckGroup (GProj A)

namespace K0

variable [SetLike.GradedMonoid A]

instance : AddCommGroup (K0 A) := inferInstanceAs (AddCommGroup (GrothendieckGroup _))

/-- The class `[P]` of a graded idempotent. -/
def of (P : GIdem A) : K0 A := GrothendieckGroup.of (GProj.mk P)

theorem of_sum (P Q : GIdem A) : of (P.sum Q) = of P + of Q := by
  simp only [of, ← GProj.mk_add, map_add]

theorem of_eq {P Q : GIdem A} (h : P ≈ Q) : of P = of Q := by
  simp only [of, GProj.mk_eq_mk.2 h]

theorem hom_ext {G : Type*} [AddCommGroup G] {f g : K0 A →+ G} (h : ∀ P, f (of P) = g (of P)) :
    f = g :=
  GrothendieckGroup.hom_ext fun x => GProj.ind (fun P => h P) x

/-- The shift `{k}` on `K₀`. -/
def shift (k : ℤ) : K0 A →+ K0 A := GrothendieckGroup.map (GProj.shift k)

theorem shift_of (k : ℤ) (P : GIdem A) : shift k (of P) = of (P.shift k) :=
  GrothendieckGroup.map_of _ _

theorem shift_zero (x : K0 A) : shift 0 x = x := by
  have : shift (A := A) 0 = AddMonoidHom.id _ := hom_ext fun P => by
    rw [shift_of, AddMonoidHom.id_apply]
    exact congrArg GrothendieckGroup.of (GProj.shift_zero (GProj.mk P))
  rw [this, AddMonoidHom.id_apply]

theorem shift_shift (a b : ℤ) (x : K0 A) : shift a (shift b x) = shift (a + b) x := by
  have : (shift (A := A) a).comp (shift b) = shift (a + b) := hom_ext fun P => by
    rw [AddMonoidHom.comp_apply, shift_of, shift_of, shift_of]
    exact congrArg GrothendieckGroup.of (GProj.shift_shift a b (GProj.mk P))
  exact DFunLike.congr_fun this x

/-- The shift action as a representation of `ℤ`. -/
def shiftRep : Multiplicative ℤ →* Module.End ℤ (K0 A) where
  toFun k := (shift (Multiplicative.toAdd k)).toIntLinearMap
  map_one' := LinearMap.ext shift_zero
  map_mul' _ _ := LinearMap.ext fun x => (shift_shift _ _ x).symm

/-- `K₀` is a `ℤ[T;T⁻¹]`-module, `T k` acting by the shift `{k}`. -/
instance : Module (LaurentPolynomial ℤ) (K0 A) :=
  Module.compHom (K0 A) (AddMonoidAlgebra.lift ℤ ℤ (Module.End ℤ (K0 A)) shiftRep).toRingHom

theorem smul_def (p : LaurentPolynomial ℤ) (x : K0 A) :
    p • x = AddMonoidAlgebra.lift ℤ ℤ (Module.End ℤ (K0 A)) shiftRep p x := rfl

theorem T_smul (k : ℤ) (x : K0 A) : (LaurentPolynomial.T k : LaurentPolynomial ℤ) • x =
    shift k x := by
  rw [smul_def, LaurentPolynomial.T, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem C_smul (a : ℤ) (x : K0 A) :
    (LaurentPolynomial.C a : LaurentPolynomial ℤ) • x = a • x := by
  rw [smul_def, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.lift_single, ofAdd_zero,
    map_one]
  rfl

theorem T_smul_of (k : ℤ) (P : GIdem A) :
    (LaurentPolynomial.T k : LaurentPolynomial ℤ) • of P = of (P.shift k) := by
  rw [T_smul, shift_of]

theorem of_zero : of (GIdem.zero : GIdem A) = 0 := map_zero (GrothendieckGroup.of (M := GProj A))

theorem T_smul_single (k : ℤ) :
    (LaurentPolynomial.T k : LaurentPolynomial ℤ) • of (GIdem.single 0 : GIdem A) =
      of (GIdem.single k) := by
  rw [T_smul_of]
  exact of_eq (MvN.of_equiv (Equiv.refl _) ((GIdem.single 0).shift k).hom
    (GIdem.single (A := A) 0).idem (fun _ => (zero_add k).symm) (fun _ _ => rfl))

/-- `[R^m{t}] = ∑ₐ [R{t a}]`. -/
theorem of_free : ∀ {m : ℕ} (t : Fin m → ℤ),
    of (GIdem.free t : GIdem A) = ∑ a, of (GIdem.single (t a))
  | 0, t => by
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← of_zero]
    exact of_eq (MvN.of_equiv (Equiv.refl _) IsHom.one (mul_one 1) (fun i => i.elim0)
      (fun i => i.elim0))
  | m + 1, t => by
    have h : MvN A (Sum.elim (fun i => t (Fin.castSucc i)) fun _ : Fin 1 => t (Fin.last m))
        (fromBlocks 1 0 0 1) t 1 := by
      refine MvN.of_equiv finSumFinEquiv (IsHom.one.fromBlocks IsHom.zero IsHom.zero IsHom.one)
        (fromBlocks_idem (mul_one 1) (mul_one 1)) ?_ ?_
      · rintro (i | i)
        · rfl
        · obtain rfl : i = 0 := Subsingleton.elim _ _
          rfl
      · intro x y
        simp only [fromBlocks_one, one_apply, EmbeddingLike.apply_eq_iff_eq]
    have h' : GIdem.free t ≈ (GIdem.free fun i => t (Fin.castSucc i)).sum
        (GIdem.single (A := A) (t (Fin.last m))) :=
      MvN.trans (mul_one 1) (fromBlocks_idem (mul_one 1) (mul_one 1)) (GIdem.sum _ _).idem h.symm
        (GIdem.mvn_sum (GIdem.free fun i => t (Fin.castSucc i)) (GIdem.single (t (Fin.last m))))
    rw [of_eq h', of_sum, of_free, Fin.sum_univ_castSucc]

/-- An additive map out of `K₀` commuting with all shifts is `ℤ[T;T⁻¹]`-linear. -/
theorem map_smul_of_shift {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial ℤ) M]
    (φ : K0 A →+ M)
    (h : ∀ k x, φ (shift k x) = (LaurentPolynomial.T k : LaurentPolynomial ℤ) • φ x)
    (p : LaurentPolynomial ℤ) (x : K0 A) : φ (p • x) = p • φ x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [add_smul, map_add, hp, hq, add_smul]
  | C_mul_T n a =>
    rw [MulAction.mul_smul, C_smul, T_smul, map_zsmul, h, MulAction.mul_smul,
      ← mul_one (LaurentPolynomial.C a), ← LaurentPolynomial.smul_eq_C_mul, smul_assoc,
      one_smul]

end K0

end OddMath.Frontier.GradedK0
