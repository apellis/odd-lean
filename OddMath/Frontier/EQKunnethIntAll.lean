import OddMath.Frontier.EQKunnethInt
import DG.HalfGraded.Vanishing

/-!
# The Künneth isomorphism (3.39) over `ℤ` in all bidegrees

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6, the Künneth property (3.39).

`ONHAll N` is the integral dg odd nilHecke ring `ONH_N` for every `N`: `ONH_0 = OPol_0`,
`ONH_1 = OPol_1`, and `ONH_{n+2} = EQOnhDG.ONH n`. `ONHTensor m n` is `ONH_m ⊗ ONH_n`, dg-lean's
graded tensor product over `ℤ`; `ONHT m n` is the same type, written as `EQK0.OPolT m n` for
`m, n ≤ 1` (`ONHT_eq : ONHT m n = ONHTensor m n`), so that the results of `EQThm318Int` and
`EQKunnethInt` apply to it directly.

* For `m ≥ 2` (or `n ≥ 2`) the dg ring `ONH_m ⊗ ONH_n` is acyclic: `d (∂₁ ⊗ 1) = 1`
  (or `d (1 ⊗ ∂₁) = 1`; `d_del_tmul_one`, `d_one_tmul_del`), so its half-graded derived category
  vanishes and its compact super Grothendieck group is zero (dg-lean's
  `DG.HalfGradedDGRing.superK0c_subsingleton`);
  `K₀(D(ONH_m)) = 0` likewise (Proposition 3.16 (2)).
* For `m, n ≤ 1` the Künneth isomorphism is built, as `EQK0.kunnethInt` (`m + n ≤ 1`) and
  `kunnethOneOneInt` (`m = n = 1`) are, from `K₀ ≅ ℤ[√−1]` on the regular classes
  (`gaEquiv`, `taEquiv`).

**The Künneth isomorphism (3.39) over `ℤ`** (`kunnethIntAll`): for all `m, n`,
`K₀(D(ONH_m)) ⊗_{ℤ[√−1]} K₀(D(ONH_n)) ≅ K₀(D(ONH_m ⊗ ONH_n))`, with
`[ONH_m] ⊗ [ONH_n] ↦ [ONH_m ⊗ ONH_n]` (`kunnethIntAll_reg`).
-/

noncomputable section

open CategoryTheory TensorProduct

namespace OddMath.Frontier.EQK0Int

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQK0
open OddMath.Frontier.EQSkewDifferential (OPol)
open OddMath.Frontier.EQOnhDG (ONH)

/-! ### `ONH_N` for every `N` -/

/-- The integral dg odd nilHecke ring `ONH_N`: `OPol_0`, `OPol_1`, and `EQOnhDG.ONH n` for
`N = n + 2`. -/
def ONHAll : ℕ → Type
  | 0 => OPol 0
  | 1 => OPol 1
  | n + 2 => ONH n

instance instRingONHAll (N : ℕ) : Ring (ONHAll N) :=
  match N with
  | 0 => inferInstanceAs (Ring (OPol 0))
  | 1 => inferInstanceAs (Ring (OPol 1))
  | n + 2 => inferInstanceAs (Ring (ONH n))

instance instDGAddCommGroupONHAll (N : ℕ) : DGAddCommGroup (ONHAll N) :=
  match N with
  | 0 => inferInstanceAs (DGAddCommGroup (OPol 0))
  | 1 => inferInstanceAs (DGAddCommGroup (OPol 1))
  | n + 2 => inferInstanceAs (DGAddCommGroup (ONH n))

instance instDGRingONHAll (N : ℕ) : DGRing (ONHAll N) :=
  match N with
  | 0 => inferInstanceAs (DGRing (OPol 0))
  | 1 => inferInstanceAs (DGRing (OPol 1))
  | n + 2 => inferInstanceAs (DGRing (ONH n))

/-- `ONH_m ⊗ ONH_n`, dg-lean's graded tensor product over `ℤ`. -/
abbrev ONHTensor (m n : ℕ) : Type :=
  DGAlgebra.gradingSubmodule ℤ (ONHAll m) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (ONHAll n)

/-- `ONH_m ⊗ ONH_n`: the graded tensor product `ONHTensor m n`, written as `EQK0.OPolT m n`
(`= OPol_m ⊗ OPol_n`, the same graded tensor product) for `m, n ≤ 1`. -/
def ONHT : ℕ → ℕ → Type
  | 0, 0 => OPolT 0 0
  | 0, 1 => OPolT 0 1
  | 1, 0 => OPolT 1 0
  | 1, 1 => OPolT 1 1
  | m + 2, n => ONHTensor (m + 2) n
  | 0, n + 2 => ONHTensor 0 (n + 2)
  | 1, n + 2 => ONHTensor 1 (n + 2)

/-- `ONHT m n` is the graded tensor product `ONH_m ⊗ ONH_n` in every bidegree. -/
theorem ONHT_eq : ∀ m n, ONHT m n = ONHTensor m n
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | _ + 2, _ | 0, _ + 2 | 1, _ + 2 => rfl

instance instONHTRing (m n : ℕ) : Ring (ONHT m n) :=
  match m, n with
  | 0, 0 => inferInstanceAs (Ring (OPolT 0 0))
  | 0, 1 => inferInstanceAs (Ring (OPolT 0 1))
  | 1, 0 => inferInstanceAs (Ring (OPolT 1 0))
  | 1, 1 => inferInstanceAs (Ring (OPolT 1 1))
  | m + 2, n => inferInstanceAs (Ring (ONHTensor (m + 2) n))
  | 0, n + 2 => inferInstanceAs (Ring (ONHTensor 0 (n + 2)))
  | 1, n + 2 => inferInstanceAs (Ring (ONHTensor 1 (n + 2)))

instance instONHTDGAddCommGroup (m n : ℕ) : DGAddCommGroup (ONHT m n) :=
  match m, n with
  | 0, 0 => inferInstanceAs (DGAddCommGroup (OPolT 0 0))
  | 0, 1 => inferInstanceAs (DGAddCommGroup (OPolT 0 1))
  | 1, 0 => inferInstanceAs (DGAddCommGroup (OPolT 1 0))
  | 1, 1 => inferInstanceAs (DGAddCommGroup (OPolT 1 1))
  | m + 2, n => inferInstanceAs (DGAddCommGroup (ONHTensor (m + 2) n))
  | 0, n + 2 => inferInstanceAs (DGAddCommGroup (ONHTensor 0 (n + 2)))
  | 1, n + 2 => inferInstanceAs (DGAddCommGroup (ONHTensor 1 (n + 2)))

instance instONHTDGRing (m n : ℕ) : DGRing (ONHT m n) :=
  match m, n with
  | 0, 0 => inferInstanceAs (DGRing (OPolT 0 0))
  | 0, 1 => inferInstanceAs (DGRing (OPolT 0 1))
  | 1, 0 => inferInstanceAs (DGRing (OPolT 1 0))
  | 1, 1 => inferInstanceAs (DGRing (OPolT 1 1))
  | m + 2, n => inferInstanceAs (DGRing (ONHTensor (m + 2) n))
  | 0, n + 2 => inferInstanceAs (DGRing (ONHTensor 0 (n + 2)))
  | 1, n + 2 => inferInstanceAs (DGRing (ONHTensor 1 (n + 2)))

/-! ### Acyclicity in ranks `≥ 2` -/

/-- The crossing `∂₁ ∈ ONH_{n+2}`. -/
def delAll (n : ℕ) : ONHAll (n + 2) := (ONH.del 0 : ONH n)

theorem d_delAll (n : ℕ) : DG.d (delAll n) = 1 := ONH.d_del (n := n) 0

theorem one_tmul_one (m n : ℕ) : ((1 : ONHAll m) ᵍ⊗ₜ[ℤ] (1 : ONHAll n) : ONHTensor m n) = 1 := rfl

/-- `d (∂₁ ⊗ 1) = 1` in `ONH_{m+2} ⊗ ONH_n`. -/
theorem d_del_tmul_one (m n : ℕ) :
    DG.d ((delAll m ᵍ⊗ₜ[ℤ] (1 : ONHAll n)) : ONHTensor (m + 2) n) = 1 := by
  rw [ConnectedTensor.d_tmul_one, d_delAll, one_tmul_one]

/-- `d (1 ⊗ ∂₁) = 1` in `ONH_m ⊗ ONH_{n+2}`. -/
theorem d_one_tmul_del (m n : ℕ) :
    DG.d (((1 : ONHAll m) ᵍ⊗ₜ[ℤ] delAll n) : ONHTensor m (n + 2)) = 1 := by
  rw [ConnectedTensor.d_one_tmul, d_delAll, one_tmul_one]

theorem subsingleton_tensor_left {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton M] : Subsingleton (M ⊗[R] N) := by
  refine subsingleton_of_forall_eq 0 fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem subsingleton_tensor_right {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] : Subsingleton (M ⊗[R] N) := by
  refine subsingleton_of_forall_eq 0 fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-! ### Grothendieck groups -/

variable [∀ N, DG.HasDerivedCategory.{0, 0} (ONHAll N)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHAll N)).Regraded)]
  [∀ m n, DG.HasDerivedCategory.{0, 0} (ONHT m n)]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHT m n)).Regraded)]

/-- `K₀(D(ONH_N))` over `ℤ` (half-graded, compact, super). -/
abbrev GA (N : ℕ) : Type 1 :=
  SuperK0c.{0, 0} (ofDGRing (ONHAll N))

/-- The regular class `[ONH_N]`. -/
abbrev regGA (N : ℕ) : GA N :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (ONHAll N) (DGRing.K0.self (ONHAll N)))

/-- `K₀(D(ONH_m ⊗ ONH_n))` over `ℤ`. -/
abbrev TA (m n : ℕ) : Type 1 :=
  SuperK0c.{0, 0} (ofDGRing (ONHT m n))

/-- The regular class `[ONH_m ⊗ ONH_n]`. -/
abbrev regTA (m n : ℕ) : TA m n :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (ONHT m n) (DGRing.K0.self (ONHT m n)))

omit [∀ N, DG.HasDerivedCategory.{0, 0} (ONHAll N)] [∀ m n, DG.HasDerivedCategory.{0, 0} (ONHT m n)]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHT m n)).Regraded)] in
/-- `K₀(D(ONH_{n+2})) = 0` over `ℤ` (Proposition 3.16 (2)). -/
theorem subsingleton_GA (n : ℕ) : Subsingleton (GA (n + 2)) :=
  superK0c_subsingleton (ofDGRing (ONHAll (n + 2))) (x := delAll n) (d_delAll n)

omit [∀ N, DG.HasDerivedCategory.{0, 0} (ONHAll N)] [∀ m n, DG.HasDerivedCategory.{0, 0} (ONHT m n)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHAll N)).Regraded)] in
/-- `K₀(D(ONH_{m+2} ⊗ ONH_n)) = 0` over `ℤ`: the dg ring is acyclic. -/
theorem subsingleton_TA_left (m n : ℕ) : Subsingleton (TA (m + 2) n) :=
  superK0c_subsingleton (ofDGRing (ONHT (m + 2) n)) (d_del_tmul_one m n)

omit [∀ N, DG.HasDerivedCategory.{0, 0} (ONHAll N)] [∀ m n, DG.HasDerivedCategory.{0, 0} (ONHT m n)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHAll N)).Regraded)] in
/-- `K₀(D(ONH_m ⊗ ONH_{n+2})) = 0` over `ℤ`: the dg ring is acyclic. -/
theorem subsingleton_TA_right : ∀ m n, Subsingleton (TA m (n + 2))
  | 0, n => superK0c_subsingleton (ofDGRing (ONHT 0 (n + 2))) (d_one_tmul_del 0 n)
  | 1, n => superK0c_subsingleton (ofDGRing (ONHT 1 (n + 2))) (d_one_tmul_del 1 n)
  | m + 2, n => subsingleton_TA_left m (n + 2)

/-! ### Instances on `OPol_N`, `OPol_m ⊗ OPol_n` from those on `ONH_N`, `ONH_m ⊗ ONH_n` -/

/-- The derived-category data on `OPol_N` (`N ≤ 1`) given by that on `ONH_N = OPol_N` (unused for
`N ≥ 2`). -/
@[instance_reducible]
def opolDG : ∀ N, DG.HasDerivedCategory.{0, 0} (OPol N)
  | 0 => (inferInstance : DG.HasDerivedCategory.{0, 0} (ONHAll 0))
  | 1 => (inferInstance : DG.HasDerivedCategory.{0, 0} (ONHAll 1))
  | _ + 2 => DG.HasDerivedCategory.small _

@[instance_reducible]
def opolCat : ∀ N, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (ofDGRing (OPol N)).Regraded)
  | 0 => (inferInstance : CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ONHAll 0)).Regraded))
  | 1 => (inferInstance : CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ONHAll 1)).Regraded))
  | _ + 2 => CatModule.HasDerivedCategory.small _

@[instance_reducible]
def opolTDG : ∀ m n, DG.HasDerivedCategory.{0, 0} (OPolT m n)
  | 0, 0 => (inferInstance : DG.HasDerivedCategory.{0, 0} (ONHT 0 0))
  | 0, 1 => (inferInstance : DG.HasDerivedCategory.{0, 0} (ONHT 0 1))
  | 1, 0 => (inferInstance : DG.HasDerivedCategory.{0, 0} (ONHT 1 0))
  | 1, 1 => (inferInstance : DG.HasDerivedCategory.{0, 0} (ONHT 1 1))
  | _, _ => DG.HasDerivedCategory.small _

@[instance_reducible]
def opolTCat : ∀ m n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (ofDGRing (OPolT m n)).Regraded)
  | 0, 0 => (inferInstance : CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ONHT 0 0)).Regraded))
  | 0, 1 => (inferInstance : CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ONHT 0 1)).Regraded))
  | 1, 0 => (inferInstance : CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ONHT 1 0)).Regraded))
  | 1, 1 => (inferInstance : CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ONHT 1 1)).Regraded))
  | _, _ => CatModule.HasDerivedCategory.small _

/-! ### Ranks `≤ 1` -/

/-- `K₀(D(ONH_N)) ≅ ℤ[√−1]` over `ℤ`, `N ≤ 1`, on the regular class (`EQK0.superK0OPolIntEquiv`). -/
def gaEquiv : ∀ N, N ≤ 1 → GA N ≃ₗ[GaussianInt] GaussianInt
  | 0, _ => letI := opolDG; letI := opolCat; superK0OPolIntEquiv (N := 0) (by omega)
  | 1, _ => letI := opolDG; letI := opolCat; superK0OPolIntEquiv (N := 1) le_rfl
  | _ + 2, h => absurd h (by omega)

omit [∀ m n, DG.HasDerivedCategory.{0, 0} (ONHT m n)]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHT m n)).Regraded)] in
theorem gaEquiv_reg : ∀ N (hN : N ≤ 1), gaEquiv N hN (regGA N) = 1
  | 0, _ => letI := opolDG; letI := opolCat; superK0OPolIntEquiv_self (N := 0) _
  | 1, _ => letI := opolDG; letI := opolCat; superK0OPolIntEquiv_self (N := 1) _
  | _ + 2, h => absurd h (by omega)

/-- `K₀(D(ONH_m ⊗ ONH_n)) ≅ ℤ[√−1]` over `ℤ`, `m, n ≤ 1`, on the regular class
(`EQK0.superK0OPolTIntEquiv`, `superK0OPolTOneOneIntEquiv`). -/
def taEquiv : ∀ m n, m ≤ 1 → n ≤ 1 → TA m n ≃ₗ[GaussianInt] GaussianInt
  | 0, 0, _, _ => letI := opolDG; letI := opolCat; letI := opolTDG; letI := opolTCat
      superK0OPolTIntEquiv (m := 0) (n := 0) (by omega)
  | 0, 1, _, _ => letI := opolDG; letI := opolCat; letI := opolTDG; letI := opolTCat
      superK0OPolTIntEquiv (m := 0) (n := 1) (by omega)
  | 1, 0, _, _ => letI := opolDG; letI := opolCat; letI := opolTDG; letI := opolTCat
      superK0OPolTIntEquiv (m := 1) (n := 0) (by omega)
  | 1, 1, _, _ => letI := opolDG; letI := opolCat; letI := opolTDG; letI := opolTCat
      superK0OPolTOneOneIntEquiv
  | _ + 2, _, h, _ => absurd h (by omega)
  | _, _ + 2, _, h => absurd h (by omega)

omit [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHAll N)).Regraded)] in
theorem taEquiv_reg : ∀ m n (hm : m ≤ 1) (hn : n ≤ 1), taEquiv m n hm hn (regTA m n) = 1
  | 0, 0, _, _ => letI := opolDG; letI := opolTDG; letI := opolTCat
      superK0OPolTIntEquiv_self (m := 0) (n := 0) (by omega)
  | 0, 1, _, _ => letI := opolDG; letI := opolTDG; letI := opolTCat
      superK0OPolTIntEquiv_self (m := 0) (n := 1) (by omega)
  | 1, 0, _, _ => letI := opolDG; letI := opolTDG; letI := opolTCat
      superK0OPolTIntEquiv_self (m := 1) (n := 0) (by omega)
  | 1, 1, _, _ => letI := opolDG; letI := opolTDG; letI := opolTCat
      superK0OPolTOneOneIntEquiv_self
  | _ + 2, _, h, _ => absurd h (by omega)
  | _, _ + 2, _, h => absurd h (by omega)

/-! ### The Künneth isomorphism -/

/-- **The Künneth isomorphism (3.39) over `ℤ`, all bidegrees**:
`K₀(D(ONH_m)) ⊗_{ℤ[√−1]} K₀(D(ONH_n)) ≅ K₀(D(ONH_m ⊗ ONH_n))`, `[ONH_m] ⊗ [ONH_n] ↦ [ONH_m ⊗ ONH_n]`
(`kunnethIntAll_reg`). For `m, n ≤ 1` it is built from the trivializations on the regular classes,
as `EQK0.kunnethInt` and `kunnethOneOneInt` are; otherwise both sides vanish. -/
def kunnethIntAll : ∀ m n, GA m ⊗[GaussianInt] GA n ≃ₗ[GaussianInt] TA m n
  | 0, 0 => tensorEquivOfGaussian (gaEquiv 0 (by omega)) (gaEquiv 0 (by omega))
      (taEquiv 0 0 (by omega) (by omega))
  | 0, 1 => tensorEquivOfGaussian (gaEquiv 0 (by omega)) (gaEquiv 1 (by omega))
      (taEquiv 0 1 (by omega) (by omega))
  | 1, 0 => tensorEquivOfGaussian (gaEquiv 1 (by omega)) (gaEquiv 0 (by omega))
      (taEquiv 1 0 (by omega) (by omega))
  | 1, 1 => tensorEquivOfGaussian (gaEquiv 1 (by omega)) (gaEquiv 1 (by omega))
      (taEquiv 1 1 (by omega) (by omega))
  | m + 2, n =>
      haveI := subsingleton_GA m
      haveI := subsingleton_TA_left m n
      haveI : Subsingleton (GA (m + 2) ⊗[GaussianInt] GA n) := subsingleton_tensor_left
      LinearEquiv.ofSubsingleton _ _
  | 0, n + 2 =>
      haveI := subsingleton_GA n
      haveI := subsingleton_TA_right 0 n
      haveI : Subsingleton (GA 0 ⊗[GaussianInt] GA (n + 2)) := subsingleton_tensor_right
      LinearEquiv.ofSubsingleton _ _
  | 1, n + 2 =>
      haveI := subsingleton_GA n
      haveI := subsingleton_TA_right 1 n
      haveI : Subsingleton (GA 1 ⊗[GaussianInt] GA (n + 2)) := subsingleton_tensor_right
      LinearEquiv.ofSubsingleton _ _

/-- The Künneth isomorphism (3.39) over `ℤ` sends `[ONH_m] ⊗ [ONH_n]` to `[ONH_m ⊗ ONH_n]`. -/
theorem kunnethIntAll_reg : ∀ m n, kunnethIntAll m n (regGA m ⊗ₜ regGA n) = regTA m n
  | 0, 0 => tensorEquivOfGaussian_tmul _ _ _ (gaEquiv_reg 0 _) (gaEquiv_reg 0 _)
      (taEquiv_reg 0 0 _ _)
  | 0, 1 => tensorEquivOfGaussian_tmul _ _ _ (gaEquiv_reg 0 _) (gaEquiv_reg 1 _)
      (taEquiv_reg 0 1 _ _)
  | 1, 0 => tensorEquivOfGaussian_tmul _ _ _ (gaEquiv_reg 1 _) (gaEquiv_reg 0 _)
      (taEquiv_reg 1 0 _ _)
  | 1, 1 => tensorEquivOfGaussian_tmul _ _ _ (gaEquiv_reg 1 _) (gaEquiv_reg 1 _)
      (taEquiv_reg 1 1 _ _)
  | m + 2, n => (subsingleton_TA_left m n).elim _ _
  | 0, n + 2 => (subsingleton_TA_right 0 n).elim _ _
  | 1, n + 2 => (subsingleton_TA_right 1 n).elim _ _

end OddMath.Frontier.EQK0Int
