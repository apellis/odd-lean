import OddMath.SKM.K0Relations
import OddMath.CoveringQuantum.Integers

/-!
# Laurent coefficients of shifted SKM classes

The coefficient convention of BE2 Lemma 11.6: `q` shifts degree by one,
and `π` shifts parity by one.
-/

noncomputable section
namespace OddMath.SKM.K0Relations
open CategoryTheory StringDiagrams LaurentPolynomial GradedSupercategory
open CategoryTheory.Idempotents

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- A weight block before additive idempotent completion. -/
abbrev base (μ ν : X) :=
  GUnderlying k (QPiEnvelope k
    ((show UGr D Sc sy hc from ⟨μ⟩) ⟶ (show UGr D Sc sy hc from ⟨ν⟩)))

/-- A completed weight block with its entrywise shift functors. -/
abbrev block (μ ν : X) :=
  GSKar k ((show UGr D Sc sy hc from ⟨μ⟩) ⟶ (show UGr D Sc sy hc from ⟨ν⟩))

local instance homModule (μ ν : X) :
    Module (LaurentPolynomial Zπ) (K₀ (block Sc sy hc μ ν)) :=
  K₀.moduleLaurent k (block Sc sy hc μ ν)

/-- Classes in a single weight block. -/
def blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) : K₀ (block Sc sy hc μ ν) :=
  K₀.mk (C := block Sc sy hc μ ν) (completed Sc sy hc μ ν s hs n a)

theorem pi_blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) :
    (C Zπ.π : LaurentPolynomial Zπ) • blockClass Sc sy hc μ ν s hs n a =
      blockClass Sc sy hc μ ν s hs n (a + 1) := by
  rw [blockClass, K₀.C_π_smul_mk]
  apply K₀.mk_eq_mk_of_iso
  exact eqToIso (by
    refine Karoubi.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      change (PiCategory.pi (R := k) (C := Mat_ (base Sc sy hc μ ν))).map (𝟙 (completed Sc sy hc μ ν s hs n a).X) = _
      exact CategoryTheory.Functor.map_id _ _)

theorem q_blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) :
    (T 1 : LaurentPolynomial Zπ) • blockClass Sc sy hc μ ν s hs n a =
      blockClass Sc sy hc μ ν s hs (n + 1) a := by
  rw [blockClass, K₀.T_smul_mk]
  apply K₀.mk_eq_mk_of_iso
  exact eqToIso (by
    refine Karoubi.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      change (QPiCategory.Q (R := k) (C := Mat_ (base Sc sy hc μ ν))).map (𝟙 (completed Sc sy hc μ ν s hs n a).X) = _
      exact CategoryTheory.Functor.map_id _ _)

theorem qinv_blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) :
    (T (-1) : LaurentPolynomial Zπ) • blockClass Sc sy hc μ ν s hs n a =
      blockClass Sc sy hc μ ν s hs (n - 1) a := by
  rw [blockClass, K₀.T_neg_one_smul_mk]
  apply K₀.mk_eq_mk_of_iso
  exact eqToIso (by
    refine Karoubi.ext ?_ ?_
    · rfl
    · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      change (QPiCategory.Qinv (R := k) (C := Mat_ (base Sc sy hc μ ν))).map
        (𝟙 (completed Sc sy hc μ ν s hs n a).X) = _
      exact CategoryTheory.Functor.map_id _ _)

/-- Arbitrary integral degree shifts act by Laurent monomials. -/
theorem T_blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (m n : ℤ) (a : ZMod 2) :
    (T n : LaurentPolynomial Zπ) • blockClass Sc sy hc μ ν s hs m a =
      blockClass Sc sy hc μ ν s hs (m + n) a := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by omega, T_add, mul_smul, ih, q_blockClass]
    congr 1; omega
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega, T_add, mul_smul, ih, qinv_blockClass]
    congr 1; omega

/-- Iterated parity shift; the integer exponent is read modulo two. -/
theorem pi_pow_blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (m : ℤ) (a : ZMod 2) (r : ℕ) :
    (C Zπ.π : LaurentPolynomial Zπ) ^ r • blockClass Sc sy hc μ ν s hs m a =
      blockClass Sc sy hc μ ν s hs m (a + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ' (C Zπ.π : LaurentPolynomial Zπ) r, mul_smul, ih, pi_blockClass]
    congr 1
    push_cast
    ring

/-- The Laurent unit `q^d`. -/
def qUnit (d : ℤ) : (LaurentPolynomial Zπ)ˣ where
  val := T d
  inv := T (-d)
  val_inv := by rw [← T_add, add_neg_cancel, T_zero]
  inv_val := by rw [← T_add, neg_add_cancel, T_zero]

/-- The covering parameter attached to a parity. -/
def piCoeff (p : ZMod 2) : LaurentPolynomial Zπ := (C Zπ.π) ^ p.val

theorem piCoeff_sq (p : ZMod 2) : piCoeff p ^ 2 = 1 := by
  rw [piCoeff, ← pow_mul, mul_comm, pow_mul, ← map_pow, Zπ.π_pow_two, map_one, one_pow]

/-- Laurent-module calculation for a degree/parity shift family. -/
theorem qpNat_action {A : Type*} [AddCommGroup A] [Module (LaurentPolynomial Zπ) A]
    (f : ℤ → ZMod 2 → A)
    (hT : ∀ m n a, (T n : LaurentPolynomial Zπ) • f m a = f (m + n) a)
    (hpi : ∀ (m : ℤ) (a : ZMod 2) (r : ℕ), (C Zπ.π : LaurentPolynomial Zπ) ^ r • f m a = f m (a + r))
    (d : ℤ) (p : ZMod 2) (m : ℕ) :
    CoveringQuantum.qpNat (qUnit d) (piCoeff p) m • f 0 0 =
      ∑ n ∈ Finset.range m, f (d * ((m : ℤ) - 1 - 2 * n)) (n * p) := by
  rw [CoveringQuantum.qpNat, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro n hn
  change (((C Zπ.π) ^ p.val) ^ n * (T d : LaurentPolynomial Zπ) ^ (m - 1 - n) *
    T (-d) ^ n) • f 0 0 = f (d * ((m : ℤ) - 1 - 2 * n)) (n * p)
  rw [← pow_mul (C Zπ.π : LaurentPolynomial Zπ), T_pow, T_pow, mul_smul, mul_smul, hT, hT,
    hpi]
  congr 1
  · have hn := Finset.mem_range.mp hn
    rw [Nat.cast_sub (by omega : n ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  · simp [mul_comm]


/-- A positive quantum integer is the class of its explicit shifted summands. -/
theorem qpNat_blockClass (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (d : ℤ) (p : ZMod 2) (m : ℕ) :
    CoveringQuantum.qpNat (qUnit d) (piCoeff p) m • blockClass Sc sy hc μ ν s hs 0 0 =
      ∑ n ∈ Finset.range m, blockClass Sc sy hc μ ν s hs
        (d * ((m : ℤ) - 1 - 2 * n)) (n * p) :=
  qpNat_action (blockClass Sc sy hc μ ν s hs) (T_blockClass Sc sy hc μ ν s hs)
    (pi_pow_blockClass Sc sy hc μ ν s hs) d p m

end OddMath.SKM.K0Relations
