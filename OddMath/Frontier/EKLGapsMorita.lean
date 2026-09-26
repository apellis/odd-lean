import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Data.Matrix.Basis
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Module.BigOperators
import Mathlib.RingTheory.Morita.Basic
import OddMath.Frontier.OnhStructure
import OddMath.Frontier.SmallRankONH

/-! # EKL: Morita equivalences as equivalences of module categories

EKL = Ellis–Khovanov–Lauda, *The odd nilHecke algebra and its diagrammatics*,
arXiv:1111.1320v1, abstract and §1.1–1.2, pp. 1–2: "idempotents which give a Morita equivalence
between odd nilHecke algebras and the rings of odd symmetric functions in finitely many
variables. Cyclotomic quotients of odd nilHecke algebras are Morita equivalent to rings which
are odd analogues of the cohomology rings of Grassmannians." The claims are ungraded.

* For any ring `R` and finite nonempty `ι`, `Mod(Mat_ι(R)) ≌ Mod(R)` (`matrixModuleEquiv`):
  `M ↦ E_{i₀i₀} M` (`cornerFunctor`, `corner`) with inverse `N ↦ N^ι` (`colFunctor`, `Col`);
  it is `ℤ`-linear, i.e. a Morita equivalence in the sense of `MoritaEquivalence`
  (`matrixMorita`).
* `ONH_a ∼ OΛ_a` (`onhMorita`, `onh_isMoritaEquivalent`), from the thick-calculus isomorphism
  `ONH_a ≅ Mat_{a!}(OΛ_a)` (`OnhStructure.matrixEquiv`, Thm 4.15 and p. 42), for every
  `a = n+2`; and for `a ≤ 1` (`onhMorita_small`).
* `ONH_a^N ∼ OH_{a,N}` (`onhCycMorita`, `onhCyc_isMoritaEquivalent`), from Proposition 5.2
  (`Cyclotomic.prop_5_2`), for every `a = n+2` and `N`.
-/

namespace OddMath.Frontier.EKLGaps
open CategoryTheory Matrix
noncomputable section

universe u v

section MatrixMorita
variable {R : Type u} [Ring R] {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)

local notation "E" => Matrix.stdBasisMatrix

omit [Fintype ι] in
theorem E_apply (i j : ι) (r : R) (a b : ι) : E i j r a b = if i = a ∧ j = b then r else 0 := rfl

theorem E_mul_E (i j k : ι) (r s : R) : E i j r * E j k s = E i k (r * s) :=
  StdBasisMatrix.mul_same (c := r) i j k s

theorem E_mul_E_of_ne {i j j' k : ι} (h : j ≠ j') (r s : R) : E i j r * E j' k s = 0 :=
  StdBasisMatrix.mul_of_ne (c := r) i j j' h s

theorem sum_E_diag : ∑ j : ι, E j j (1 : R) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, stdBasisMatrix, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun j _ => if_neg fun e => h (e.1.symm.trans e.2)

theorem E_row_mul (j : ι) (A : Matrix ι ι R) : E i₀ j 1 * A = ∑ k, E i₀ k (A j k) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply, stdBasisMatrix, Matrix.of_apply]
  by_cases ha : i₀ = a
  · subst ha
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [ha]

/-! #### The corner functor `M ↦ E₀₀ M` -/

section Corner
variable (R) (M : Type v) [AddCommGroup M] [Module (Matrix ι ι R) M]

/-- The corner `E_{i₀i₀} M` of a module over `Mat_ι(R)`. -/
def corner : AddSubgroup M where
  carrier := {m | (E i₀ i₀ (1 : R)) • m = m}
  add_mem' {x y} hx hy := by
    change E i₀ i₀ (1 : R) • (x + y) = x + y
    rw [smul_add, hx, hy]
  zero_mem' := smul_zero _
  neg_mem' {x} hx := by
    change E i₀ i₀ (1 : R) • (-x) = -x
    rw [smul_neg, hx]

variable {R}

theorem E_smul_mem (r : R) (m : M) : E i₀ i₀ r • m ∈ corner R i₀ M := by
  change E i₀ i₀ (1 : R) • (E i₀ i₀ r • m) = E i₀ i₀ r • m
  rw [← MulAction.mul_smul, E_mul_E, one_mul]

instance cornerModule : Module R (corner R i₀ M) where
  smul r m := ⟨E i₀ i₀ r • (m : M), E_smul_mem i₀ M r m⟩
  one_smul m := Subtype.ext m.2
  mul_smul r s m := Subtype.ext (by
    change E i₀ i₀ (r * s) • (m : M) = E i₀ i₀ r • E i₀ i₀ s • (m : M)
    rw [← MulAction.mul_smul, E_mul_E])
  smul_zero r := Subtype.ext (smul_zero _)
  smul_add r m m' := Subtype.ext (smul_add _ _ _)
  add_smul r s m := Subtype.ext (by
    change E i₀ i₀ (r + s) • (m : M) = E i₀ i₀ r • (m : M) + E i₀ i₀ s • (m : M)
    rw [← add_smul, stdBasisMatrix_add])
  zero_smul m := Subtype.ext (by
    change E i₀ i₀ (0 : R) • (m : M) = 0
    rw [stdBasisMatrix_zero, zero_smul])

theorem corner_smul_val (r : R) (m : corner R i₀ M) : ((r • m : corner R i₀ M) : M) = E i₀ i₀ r • (m : M) :=
  rfl

end Corner

/-! #### Column vectors -/

/-- Column vectors `ι → N` over an `R`-module `N`, as a module over `Mat_ι(R)`. -/
def Col (ι : Type) (N : Type v) : Type v := ι → N

instance (N : Type v) [AddCommGroup N] : AddCommGroup (Col ι N) := Pi.addCommGroup

instance colModule (N : Type v) [AddCommGroup N] [Module R N] : Module (Matrix ι ι R) (Col ι N) where
  smul A v := fun i => ∑ j, A i j • (v : ι → N) j
  one_smul v := funext fun i => by
    change ∑ j, (1 : Matrix ι ι R) i j • (v : ι → N) j = v i
    simp [Matrix.one_apply]
  mul_smul A B v := funext fun i => by
    change ∑ j, (A * B) i j • (v : ι → N) j = ∑ k, A i k • ∑ j, B k j • (v : ι → N) j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, MulAction.mul_smul]
    exact Finset.sum_comm
  smul_zero A := funext fun i => by
    change ∑ j, A i j • (0 : N) = 0
    simp
  smul_add A v w := funext fun i => by
    change ∑ j, A i j • ((v : ι → N) j + (w : ι → N) j) =
      ∑ j, A i j • (v : ι → N) j + ∑ j, A i j • (w : ι → N) j
    simp [smul_add, Finset.sum_add_distrib]
  add_smul A B v := funext fun i => by
    change ∑ j, (A + B) i j • (v : ι → N) j =
      ∑ j, A i j • (v : ι → N) j + ∑ j, B i j • (v : ι → N) j
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul v := funext fun i => by
    change ∑ j, (0 : Matrix ι ι R) i j • (v : ι → N) j = 0
    simp

theorem col_smul_apply (N : Type v) [AddCommGroup N] [Module R N] (A : Matrix ι ι R) (v : Col ι N)
    (i : ι) : (A • v : Col ι N) i = ∑ j, A i j • v j := rfl

variable (R ι) in
/-- `M ↦ E_{i₀i₀} M`, from `Mat_ι(R)`-modules to `R`-modules. -/
def cornerFunctor : ModuleCat.{v} (Matrix ι ι R) ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (corner R i₀ M)
  map {M N} f := ModuleCat.ofHom
    { toFun := fun m => ⟨f m.1, by
        change E i₀ i₀ (1 : R) • f.hom m.1 = f.hom m.1
        rw [← f.hom.map_smul, m.2]⟩
      map_add' := fun m m' => Subtype.ext (f.hom.map_add _ _)
      map_smul' := fun r m => Subtype.ext (f.hom.map_smul _ _) }
  map_id M := rfl
  map_comp f g := rfl

variable (R ι) in
/-- `N ↦ N^ι` (column vectors), from `R`-modules to `Mat_ι(R)`-modules. -/
def colFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} (Matrix ι ι R) where
  obj N := ModuleCat.of (Matrix ι ι R) (Col ι N)
  map {N N'} g := ModuleCat.ofHom
    { toFun := fun v i => g ((v : ι → N) i)
      map_add' := fun v w => funext fun i => g.hom.map_add _ _
      map_smul' := fun A v => funext fun i => by
        change g.hom (∑ j, A i j • (v : ι → N) j) = ∑ j, A i j • g.hom ((v : ι → N) j)
        simp }
  map_id N := rfl
  map_comp f g := rfl

section Unit
variable (M : Type v) [AddCommGroup M] [Module (Matrix ι ι R) M]

/-- `M ≅ (E_{i₀i₀} M)^ι`, `m ↦ (E_{i₀j} m)_j`. -/
def unitEquiv : M ≃ₗ[Matrix ι ι R] Col ι (corner R i₀ M) where
  toFun m := fun j => ⟨E i₀ j (1 : R) • m, by
    change E i₀ i₀ (1 : R) • E i₀ j (1 : R) • m = E i₀ j (1 : R) • m
    rw [← MulAction.mul_smul, E_mul_E, one_mul]⟩
  map_add' m m' := funext fun j => Subtype.ext (smul_add _ _ _)
  map_smul' A m := funext fun j => Subtype.ext (by
    change E i₀ j (1 : R) • A • m = ((∑ k, A j k • _ : corner R i₀ M) : M)
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [corner_smul_val, ← MulAction.mul_smul, E_mul_E, one_mul, mul_one, RingHom.id_apply]
    rw [← Finset.sum_smul, ← E_row_mul])
  invFun v := ∑ j, E j i₀ (1 : R) • ((v : ι → corner R i₀ M) j : M)
  left_inv m := by
    change ∑ j, E j i₀ (1 : R) • E i₀ j (1 : R) • m = m
    simp only [← MulAction.mul_smul, E_mul_E, one_mul]
    rw [← Finset.sum_smul, sum_E_diag, one_smul]
  right_inv v := funext fun k => Subtype.ext (by
    change E i₀ k (1 : R) • ∑ j, E j i₀ (1 : R) • ((v : ι → corner R i₀ M) j : M) =
      ((v : ι → corner R i₀ M) k : M)
    rw [Finset.smul_sum, Finset.sum_eq_single k]
    · rw [← MulAction.mul_smul, E_mul_E, one_mul]
      exact ((v : ι → corner R i₀ M) k).2
    · intro j _ hj
      rw [← MulAction.mul_smul, E_mul_E_of_ne (Ne.symm hj), zero_smul]
    · simp)

end Unit

section Counit
variable (N : Type v) [AddCommGroup N] [Module R N]

/-- `E_{i₀i₀} (N^ι) ≅ N`, `v ↦ v_{i₀}`. -/
def counitEquiv : corner R i₀ (Col ι N) ≃ₗ[R] N where
  toFun v := (v.1 : ι → N) i₀
  map_add' v w := rfl
  map_smul' r v := by
    change (∑ j, E i₀ i₀ r i₀ j • (v.1 : ι → N) j) = r • (v.1 : ι → N) i₀
    rw [Finset.sum_eq_single i₀]
    · rw [StdBasisMatrix.apply_same]
    · intro j _ hj
      rw [E_apply, if_neg (fun e : i₀ = i₀ ∧ i₀ = j => hj e.2.symm), zero_smul]
    · simp
  invFun n := ⟨(Pi.single i₀ n : ι → N), by
    change (fun i => ∑ j, E i₀ i₀ (1 : R) i j • (Pi.single i₀ n : ι → N) j) = Pi.single i₀ n
    funext i
    rw [Finset.sum_eq_single i₀]
    · by_cases hi : i = i₀
      · subst hi; simp
      · rw [E_apply, if_neg (fun e : i₀ = i ∧ i₀ = i₀ => hi e.1.symm), zero_smul,
          Pi.single_eq_of_ne hi]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, smul_zero]
    · simp⟩
  left_inv v := Subtype.ext (by
    have hv := v.2
    change (fun i => ∑ j, E i₀ i₀ (1 : R) i j • (v.1 : ι → N) j) = (v.1 : ι → N) at hv
    change (Pi.single i₀ ((v.1 : ι → N) i₀) : ι → N) = v.1
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi, ← congrFun hv i]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [E_apply, if_neg (fun e : i₀ = i ∧ i₀ = j => hi e.1.symm), zero_smul])
  right_inv n := by simp

end Counit

variable (R ι) in
/-- **Morita equivalence for matrix rings**: `Mod(Mat_ι(R)) ≌ Mod(R)`, `M ↦ E_{i₀i₀} M`, with
inverse `N ↦ N^ι`. -/
def matrixModuleEquiv : ModuleCat.{v} (Matrix ι ι R) ≌ ModuleCat.{v} R :=
  CategoryTheory.Equivalence.mk (cornerFunctor R ι i₀) (colFunctor R ι)
    (NatIso.ofComponents (fun M => (unitEquiv i₀ M).toModuleIso) fun f => by
      ext m
      funext j
      apply Subtype.ext
      change E i₀ j (1 : R) • f.hom m = f.hom (E i₀ j (1 : R) • m)
      rw [f.hom.map_smul])
    (NatIso.ofComponents (fun N => (counitEquiv i₀ N).toModuleIso) fun g => rfl)

variable (R ι) in
/-- `Mat_ι(R)` and `R` are Morita equivalent (as `ℤ`-algebras). -/
def matrixMorita : MoritaEquivalence ℤ (Matrix ι ι R) R where
  eqv := matrixModuleEquiv R ι i₀
  linear := @Functor.Linear.mk ℤ _ _ _ _ _ _ _ ModuleCat.Algebra.instLinear
    ModuleCat.Algebra.instLinear _ fun f r => by
      ext m
      apply Subtype.ext
      change (algebraMap ℤ (Matrix ι ι R) r) • f.hom m.1 = E i₀ i₀ (algebraMap ℤ R r) • f.hom m.1
      have hm : E i₀ i₀ (1 : R) • f.hom m.1 = f.hom m.1 := by
        rw [← f.hom.map_smul]; exact congrArg f.hom m.2
      conv_lhs => rw [← hm]
      rw [← MulAction.mul_smul]
      congr 1
      rw [Matrix.algebraMap_eq_diagonal]
      ext a b
      rw [Matrix.diagonal_mul, E_apply, E_apply, Pi.algebraMap_apply, mul_ite, mul_one, mul_zero]

end MatrixMorita

/-! ### `ONH_a ∼ OΛ_a` and `ONH_a^N ∼ OH_{a,N}` -/

/-- A ring isomorphism as an isomorphism of `ℤ`-algebras. -/
def ringEquivToIntAlgEquiv {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B) : A ≃ₐ[ℤ] B :=
  AlgEquiv.ofRingEquiv (f := e) fun x => by
    rw [algebraMap_int_eq, eq_intCast, eq_intCast, map_intCast]

theorem idx_nonempty (n : ℕ) : Nonempty (OnhStructure.Idx n) :=
  Fintype.card_pos_iff.mp (by rw [OnhStructure.card_Idx]; exact Nat.factorial_pos _)

/-- **EKL, abstract and §1.2: `ONH_a` is Morita equivalent to `OΛ_a`**, `a = n+2`: an equivalence
of categories `Mod(ONH_a) ≌ Mod(OΛ_a)`, `ℤ`-linear, obtained from the thick-calculus matrix
isomorphism `ONH_a ≅ Mat_{a!}(OΛ_a)` of p. 42 (`OnhStructure.matrixEquiv`). -/
def onhMorita (n : ℕ) : MoritaEquivalence ℤ (NilHeckeAction.Presented n) (OnhStructure.K n) :=
  (MoritaEquivalence.ofAlgEquiv (ringEquivToIntAlgEquiv (OnhStructure.matrixEquiv n).symm)).trans ℤ
    (matrixMorita (OnhStructure.K n) (OnhStructure.Idx n) (Classical.choice (idx_nonempty n)))

theorem onh_isMoritaEquivalent (n : ℕ) :
    IsMoritaEquivalent ℤ (NilHeckeAction.Presented n) (OnhStructure.K n) := ⟨⟨onhMorita n⟩⟩

/-- **EKL, abstract and §1.1: `ONH_a^N` is Morita equivalent to `OH_{a,N}`**, from Proposition 5.2
(`Cyclotomic.prop_5_2`), for every `a = n+2` and `N`. -/
def onhCycMorita (n N : ℕ) : MoritaEquivalence ℤ (Cyclotomic.ONH n N) (Cyclotomic.OH n N) :=
  (MoritaEquivalence.ofAlgEquiv (ringEquivToIntAlgEquiv (Cyclotomic.prop_5_2 n N))).trans ℤ
    (matrixMorita (Cyclotomic.OH n N) (NilCoxeterWords.Perm n) 1)

theorem onhCyc_isMoritaEquivalent (n N : ℕ) :
    IsMoritaEquivalent ℤ (Cyclotomic.ONH n N) (Cyclotomic.OH n N) := ⟨⟨onhCycMorita n N⟩⟩

/-- `ONH_a ∼ OΛ_a` for `a ≤ 1` (`ONH_a = OΛ_a`, `a! = 1`). -/
def onhMorita_small {a : ℕ} (ha : a ≤ 1) : MoritaEquivalence ℤ (SmallRank.ONH a) (SmallRank.OLam a) :=
  (MoritaEquivalence.ofAlgEquiv (ringEquivToIntAlgEquiv (SmallRank.matrixEquiv_small ha).symm)).trans ℤ
    (matrixMorita (SmallRank.OLam a) (Fin 1) 0)

end
end OddMath.Frontier.EKLGaps
