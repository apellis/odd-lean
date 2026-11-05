import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Tactic

/-! # Division by a degree-shift triangular module row

Finite coefficient elimination for the polynomial row step of
DeformedBoundaryDivision (5). Coefficients form an arbitrary module; each
pivot is a specified linear equivalence. No coefficient multiplication,
field, dimension or finiteness premise is used.
-/
noncomputable section
namespace OddMath.Algebra.DegreeShiftRow
open scoped Classical
variable {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
  (A : (ℕ →₀ M) →ₗ[k] (ℕ →₀ M)) (L : ℕ → M ≃ₗ[k] M) (S Q : ℕ)
  (habove : ∀ d n b, d + Q < n + S → A (Finsupp.single d b) n = 0)
  (htop : ∀ d n b, n + S = d + Q → A (Finsupp.single d b) n = L n b)

include habove htop

omit htop in
theorem above (f : ℕ →₀ M) (n : ℕ)
    (hf : ∀ d ∈ f.support, d + Q < n + S) : A f n = 0 := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  exact habove d n (f d) (hf d hd)

theorem top (f : ℕ →₀ M) (d n : ℕ)
    (hf : ∀ e ∈ f.support, e ≤ d) (hn : n + S = d + Q) :
    A f n = L n (f d) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single d]
  · rw [htop d n _ hn]
  · intro e he hne
    exact habove e n (f e) (by have := hf e he; omega)
  · intro hd
    rw [Finsupp.notMem_support_iff.mp hd, Finsupp.single_zero, map_zero, Finsupp.zero_apply]

theorem eq_zero_iff (f : ℕ →₀ M) :
    A f = 0 ↔ ∀ d ∈ f.support, d + Q < S := by
  constructor
  · intro hz d hd
    by_contra h
    obtain ⟨e, he, hmax⟩ := f.support.exists_max_image id ⟨d, hd⟩
    have hde : d ≤ e := hmax d hd
    have hn : e + Q - S +
        S = e + Q := by omega
    have ht := top A L S Q habove htop f e _ hmax hn
    rw [hz, Finsupp.zero_apply] at ht
    have hc : f e = 0 := (L _).injective
      (ht.symm.trans (map_zero _).symm)
    exact Finsupp.mem_support_iff.mp he hc
  · intro hf
    ext n
    exact above A S Q habove f n (fun d hd => by have := hf d hd; omega)

theorem division (f : ℕ →₀ M) :
    ∃ q r : ℕ →₀ M, A q + r = f ∧
      (∀ d ∈ q.support, S ≤ d + Q) ∧
      (∀ n ∈ r.support, n + S < Q) := by
  suffices hb : ∀ N (g : ℕ →₀ M), (∀ n, N ≤ n → g n = 0) →
      ∃ q r : ℕ →₀ M,
        A q + r = g ∧
        (∀ d ∈ q.support, S ≤ d + Q) ∧
        (∀ n ∈ r.support, n + S < Q) by
    apply hb (f.support.sup id + 1) f
    intro n hn
    apply Finsupp.notMem_support_iff.mp
    intro hh
    have hh' : n ≤ f.support.sup id := Finset.le_sup (f := id) hh
    omega
  intro N
  induction N with
  | zero =>
    intro g hg
    have hz : g = 0 := by ext n; exact hg n (Nat.zero_le n)
    exact ⟨0, 0, by rw [map_zero, add_zero, hz], by simp, by simp⟩
  | succ N ih =>
    intro g hg
    by_cases hN : N + S < Q
    · refine ⟨0, g, by rw [map_zero, zero_add], by simp, ?_⟩
      intro n hn
      have hnN : n ≤ N := by
        by_contra h
        exact (Finsupp.mem_support_iff.mp hn) (hg n (by omega))
      omega
    · let d := N + S - Q
      have hd : N + S = d + Q := by
        dsimp [d]; omega
      let c := (L N).symm (g N)
      let s := Finsupp.single d c
      have ht : A s N = g N := by
        rw [htop d N c hd]
        exact LinearEquiv.apply_symm_apply _ _
      have hlow : ∀ n, N ≤ n → (g - A s) n = 0 := by
        intro n hn
        by_cases he : n = N
        · subst n; simp only [Finsupp.sub_apply, ht, sub_self]
        · rw [Finsupp.sub_apply, hg n (by omega),
            habove d n c (by omega), sub_self]
      obtain ⟨q, r, hqr, hq, hr⟩ := ih _ hlow
      refine ⟨q + s, r, ?_, ?_, hr⟩
      · rw [map_add]
        calc
          _ = (A q + r) +
              A s := by abel
          _ = g := by rw [hqr]; abel
      · intro e he
        rcases Finset.mem_union.mp (Finsupp.support_add he) with he | he
        · exact hq e he
        · have heq : e = d := by
            by_contra hh
            exact (Finsupp.mem_support_iff.mp he) (Finsupp.single_eq_of_ne hh)
          omega

theorem separation (q r : ℕ →₀ M)
    (hq : ∀ d ∈ q.support, S ≤ d + Q)
    (hr : ∀ n ∈ r.support, n + S < Q)
    (h : A q + r = 0) : q = 0 ∧ r = 0 := by
  have hq0 : q = 0 := by
    by_contra hq0
    obtain ⟨d, hd, hmax⟩ := q.support.exists_max_image id (Finsupp.support_nonempty_iff.mpr hq0)
    have hd' := hq d hd
    let n := d + Q - S
    have hn : n + S = d + Q := by
      dsimp [n]; omega
    have hr0 : r n = 0 := by
      by_contra hh
      have := hr n (Finsupp.mem_support_iff.mpr hh)
      omega
    have hh := congrArg (fun f : ℕ →₀ M => f n) h
    rw [Finsupp.add_apply, hr0, add_zero, Finsupp.zero_apply,
      top A L S Q habove htop q d n hmax hn] at hh
    have hc : q d = 0 := (L n).injective
      (hh.trans (map_zero _).symm)
    exact Finsupp.mem_support_iff.mp hd hc
  refine ⟨hq0, ?_⟩
  simpa only [hq0, map_zero, zero_add] using h

/-- A nonnegative degree shift has no low kernel. -/
theorem injective (h : S ≤ Q) : Function.Injective A := by
  intro f g hfg
  have hz : A (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hb := (eq_zero_iff A L S Q habove htop (f - g)).mp hz
  apply sub_eq_zero.mp
  ext d
  by_contra hd
  have := hb d (Finsupp.mem_support_iff.mpr hd)
  omega

/-- A nonpositive degree shift has no low output remainder. -/
theorem surjective (h : Q ≤ S) : Function.Surjective A := by
  intro f
  obtain ⟨q, r, he, _, hr⟩ := division A L S Q habove htop f
  have hr0 : r = 0 := by
    ext n
    by_contra hh
    have := hr n (Finsupp.mem_support_iff.mpr hh)
    omega
  exact ⟨q, by simpa only [hr0, add_zero] using he⟩

def high : Submodule k (ℕ →₀ M) :=
  Finsupp.supported M k {d | S ≤ d + Q}

def window : Submodule k (ℕ →₀ M) :=
  Finsupp.supported M k {n | n + S < Q}

def assembly : (high (k := k) (M := M) S Q × window (k := k) (M := M) S Q) →ₗ[k] (ℕ →₀ M) :=
  (A.comp (high (k := k) (M := M) S Q).subtype).coprod
    (window (k := k) (M := M) S Q).subtype

theorem assembly_bijective :
    Function.Bijective (assembly A S Q) := by
  constructor
  · intro x y hxy
    have hz : assembly A S Q (x - y) = 0 := by
      rw [(assembly A S Q).map_sub x y, hxy, sub_self]
    have hh := separation A L S Q habove htop (x - y).1 (x - y).2
      (fun d hd => (x - y).1.property hd) (fun n hn => (x - y).2.property hn) hz
    apply sub_eq_zero.mp
    apply Prod.ext <;> apply Subtype.ext
    · exact hh.1
    · exact hh.2
  · intro f
    obtain ⟨q, r, he, hq, hr⟩ := division A L S Q habove htop f
    exact ⟨(⟨q, fun _ hd => hq _ hd⟩, ⟨r, fun _ hn => hr _ hn⟩), he⟩

def divisionEquiv :
    (high (k := k) (M := M) S Q × window (k := k) (M := M) S Q) ≃ₗ[k] (ℕ →₀ M) :=
  LinearEquiv.ofBijective (assembly A S Q) (assembly_bijective A L S Q habove htop)

end OddMath.Algebra.DegreeShiftRow
