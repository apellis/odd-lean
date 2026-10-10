import OddMath.Frontier.EQOnhDGCompare
import OddMath.Frontier.OddBialgebraWindow
import DG.Algebra.TensorProduct

/-!
# `ι_{a,b} : ONH_a ⊗ ONH_b → ONH_{a+b}` as a morphism of dg rings

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6, the inclusion `ι_{m,n} : ONH_m ⊗ ONH_n ↪ ONH_{m+n}` defining `Ind_{m,n}` and `Res_{m,n}`
((3.39)–(3.41)); ranks `a = a' + 2`, `b = b' + 2`.

* `ONH.windowDG m n p h : ONH_{m+2} → ONH_{n+2}`: the strand window (`OnhWindow.windowHom`, placing a
  diagram on the strands `[p, p + m + 2)`) as a morphism of dg rings: it preserves the grading
  (`EQOnhDGCompare`) and the differential (`d x = x²`, `d ∂ = 1` on generators,
  `ONH.map_d_of_generators`).
* `ONH.iota a' b' : ONH_{a'+2} ⊗ ONH_{b'+2} → ONH_{a'+b'+4}` (the target is indexed as
  `ONH (a' + 2 + b')`, of rank `(a' + 2) + (b' + 2)`), `g ⊗ h ↦ g h` with `g` on the first
  `a' + 2` strands and `h` on the last `b' + 2`, a morphism of dg rings out of dg-lean's graded tensor
  product (Koszul sign rule), well defined since diagrams on disjoint windows supercommute
  (`OddBialgebra.winPiece_supercomm`).
-/

noncomputable section

open DG
open scoped TensorProduct

namespace OddMath.Frontier.EQOnhDG

open NilHeckeAction NilHeckeGrading OddBialgebra

namespace ONH

/-! ### Morphisms out of `ONH` commuting with the differential on generators -/

theorem freeAlgebra_ind {n : ℕ} {P : ONH n → Prop} (h1 : P 1) (hadd : ∀ x y, P x → P y → P (x + y))
    (hneg : ∀ x, P x → P (-x))
    (hdot : ∀ j v, P v → P (x j * v)) (hcross : ∀ i v, P v → P (del i * v)) (y : ONH n) : P y := by
  -- `S = {u | ∀ v, P v → P (u * v)}` contains the generators and is a subring.
  let S : Subring (ONH n) :=
    { carrier := {u | ∀ v, P v → P (u * v)}
      mul_mem' := fun {u u'} hu hu' v hv => by rw [mul_assoc]; exact hu _ (hu' v hv)
      one_mem' := fun v hv => by rwa [one_mul]
      add_mem' := fun {u u'} hu hu' v hv => by rw [add_mul]; exact hadd _ _ (hu v hv) (hu' v hv)
      zero_mem' := fun v hv => by
        rw [zero_mul]
        have h := hadd _ _ h1 (hneg _ h1)
        rwa [add_neg_cancel] at h
      neg_mem' := fun {u} hu v hv => by rw [neg_mul]; exact hneg _ (hu v hv) }
  have hS : ∀ u : ONH n, u ∈ S := by
    intro u
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (I := relIdeal n) u
    induction w using FreeAlgebra.induction with
    | grade1 g =>
      cases g with
      | inl j => exact fun v hv => hdot j v hv
      | inr i => exact fun v hv => hcross i v hv
    | grade0 r =>
      rw [Ideal.Quotient.mk_algebraMap, Algebra.algebraMap_eq_smul_one]
      exact Subring.zsmul_mem _ S.one_mem r
    | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
    | mul a b ha hb => rw [map_mul]; exact S.mul_mem ha hb
  have := hS y 1 h1
  rwa [mul_one] at this

/-- A ring morphism `ONH_{m+2} → B` into a dg ring which preserves the grading commutes with the
differentials as soon as it does on the generators `x_j`, `∂_i`. -/
theorem map_d_of_generators {m : ℕ} {B : Type*} [Ring B] [DGAddCommGroup B] [DGRing B]
    (f : ONH m →+* B) (hmem : ∀ {k : ℤ} {y : ONH m}, y ∈ DG.grading k → f y ∈ DG.grading k)
    (hx : ∀ j, d (f (x j)) = f (d (x j))) (hdel : ∀ i, d (f (del i)) = f (d (del i)))
    (y : ONH m) : d (f y) = f (d y) := by
  refine freeAlgebra_ind (P := fun y => d (f y) = f (d y)) ?_ ?_ ?_ ?_ ?_ y
  · rw [map_one, d_one, d_one, map_zero]
  · intro u v hu hv; rw [map_add, d_add, hu, hv, d_add, map_add]
  · intro u hu; rw [map_neg, d_neg, hu, d_neg, map_neg]
  · intro j u hu
    rw [map_mul, d_mul (hmem (x_mem_grading j)), d_mul (x_mem_grading j), hx, hu, map_add, map_mul,
      Units.smul_def, Units.smul_def, map_zsmul, map_mul]
  · intro i u hu
    rw [map_mul, d_mul (hmem (del_mem_grading i)), d_mul (del_mem_grading i), hdel, hu, map_add,
      map_mul, Units.smul_def, Units.smul_def, map_zsmul, map_mul]

/-! ### Windows -/

theorem mem_grading_iff_degreePiece {n : ℕ} {k : ℤ} {y : ONH n} :
    y ∈ DG.grading k ↔ (equiv n).symm y ∈ degreePiece n (2 * k) := by
  rw [mem_grading_iff, grading_eq_degreePiece]; rfl


/-- The strand window `[p, p + m + 2)` as a ring morphism `ONH_{m+2} → ONH_{n+2}`. -/
def windowRing (m n p : ℕ) (h : p + (m + 2) ≤ n + 2) : ONH m →+* ONH n :=
  ((equiv n).toRingHom.comp (OnhWindow.windowHom m n p h)).comp (equiv m).symm.toRingHom

theorem windowRing_x (m n p : ℕ) (h : p + (m + 2) ≤ n + 2) (j : Fin (m + 2)) :
    windowRing m n p h (x j) = x ⟨j.val + p, by have := j.isLt; omega⟩ :=
  OnhWindow.windowHom_dot j

theorem windowRing_del (m n p : ℕ) (h : p + (m + 2) ≤ n + 2) (i : Fin (m + 1)) :
    windowRing m n p h (del i) = del ⟨i.val + p, by have := i.isLt; omega⟩ :=
  OnhWindow.windowHom_crossing i

theorem windowRing_mem_winPiece (m n p : ℕ) (h : p + (m + 2) ≤ n + 2) {k : ℤ} {y : ONH m} (hy : y ∈ DG.grading k) :
    (equiv n).symm (windowRing m n p h y) ∈ winPiece n p (p + (m + 2)) (2 * k) :=
  windowHom_mem h ((mem_grading_iff_degreePiece).mp hy)

theorem windowRing_mem (m n p : ℕ) (h : p + (m + 2) ≤ n + 2) {k : ℤ} {y : ONH m} (hy : y ∈ DG.grading k) :
    windowRing m n p h y ∈ DG.grading k :=
  (mem_grading_iff_degreePiece).mpr (winPiece_le _ _ _ (windowRing_mem_winPiece m n p h hy))

/-- **The strand window as a morphism of dg rings** `ONH_{m+2} → ONH_{n+2}`. -/
def windowDG (m n p : ℕ) (h : p + (m + 2) ≤ n + 2) : ONH m →ᵈᵍ+* ONH n where
  toRingHom := windowRing m n p h
  map_mem' hy := windowRing_mem m n p h hy
  map_d' y := (map_d_of_generators (windowRing m n p h) (windowRing_mem m n p h)
    (fun j => by rw [d_x, map_mul, windowRing_x m n p h, d_x])
    (fun i => by rw [d_del, map_one, windowRing_del m n p h, d_del]) y).symm

theorem windowDG_apply (m n p : ℕ) (h : p + (m + 2) ≤ n + 2) (y : ONH m) : windowDG m n p h y = windowRing m n p h y := rfl

/-! ### `ι_{a,b}` -/

variable (a b : ℕ)

local notation "𝒜" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "ℬ" => DGAlgebra.gradingSubmodule ℤ (ONH b)

theorem le_left : 0 + (a + 2) ≤ (a + 2 + b) + 2 := by omega
theorem le_right : (a + 2) + (b + 2) ≤ (a + 2 + b) + 2 := by omega

/-- The left block `ONH_{a+2} → ONH_{a+b+4}` (strands `[0, a + 2)`). -/
abbrev iotaL : ONH a →ᵈᵍ+* ONH (a + 2 + b) := windowDG a (a + 2 + b) 0 (le_left a b)

/-- The right block `ONH_{b+2} → ONH_{a+b+4}` (strands `[a + 2, a + b + 4)`). -/
abbrev iotaR : ONH b →ᵈᵍ+* ONH (a + 2 + b) := windowDG b (a + 2 + b) (a + 2) (le_right a b)

theorem iotaL_mul_iotaR {i j : ℤ} (f : 𝒜 i) (g : ℬ j) :
    (iotaL a b).toIntAlgHom (f : ONH a) * (iotaR a b).toIntAlgHom (g : ONH b) =
      (-1 : ℤˣ) ^ (j * i) •
        ((iotaR a b).toIntAlgHom (g : ONH b) * (iotaL a b).toIntAlgHom (f : ONH a)) := by
  have hx := windowRing_mem_winPiece a (a + 2 + b) 0 (le_left a b) f.2
  have hy := windowRing_mem_winPiece b (a + 2 + b) (a + 2) (le_right a b) g.2
  have hc : windowRing b (a + 2 + b) (a + 2) (le_right a b) g *
      windowRing a (a + 2 + b) 0 (le_left a b) f = (i * j).negOnePow •
        (windowRing a (a + 2 + b) 0 (le_left a b) f *
          windowRing b (a + 2 + b) (a + 2) (le_right a b) g) :=
    winPiece_supercomm hx hy (by omega)
  change windowRing a (a + 2 + b) 0 (le_left a b) f * windowRing b (a + 2 + b) (a + 2) (le_right a b) g =
    koszulSign (j * i) • (windowRing b (a + 2 + b) (a + 2) (le_right a b) g *
      windowRing a (a + 2 + b) 0 (le_left a b) f)
  rw [hc, smul_smul, mul_comm j i, Int.units_mul_self, one_smul]

/-- `g ⊗ h ↦ g h`, `ONH_{a+2} ⊗ ONH_{b+2} → ONH_{a+b+4}` (an algebra morphism over `ℤ`). -/
def iotaAlgHom : (𝒜 ᵍ⊗[ℤ] ℬ) →ₐ[ℤ] ONH (a + 2 + b) :=
  GradedTensorProduct.lift _ _ (iotaL a b).toIntAlgHom (iotaR a b).toIntAlgHom
    fun _ _ f g => iotaL_mul_iotaR a b f g

theorem iotaAlgHom_tmul (f : ONH a) (g : ONH b) :
    iotaAlgHom a b (f ᵍ⊗ₜ[ℤ] g) = iotaL a b f * iotaR a b g :=
  GradedTensorProduct.lift_tmul _ _ _ _ _ f g

theorem iotaAlgHom_mem_grading {k : ℤ} {t : 𝒜 ᵍ⊗[ℤ] ℬ} (ht : t ∈ DG.grading k) :
    iotaAlgHom a b t ∈ DG.grading (M := ONH (a + 2 + b)) k := by
  refine GradedTensorProduct.grading_induction _ _ ht
    (motive := fun t => iotaAlgHom a b t ∈ DG.grading (M := ONH (a + 2 + b)) k)
    (by rw [map_zero]; exact zero_mem _) ?_ ?_
  · rintro i j f g rfl
    rw [iotaAlgHom_tmul]
    exact DG.mul_mem_grading ((iotaL a b).map_mem f.2) ((iotaR a b).map_mem g.2)
  · intro x y hx hy
    rw [map_add]; exact add_mem hx hy

theorem iotaAlgHom_d (t : 𝒜 ᵍ⊗[ℤ] ℬ) : iotaAlgHom a b (DG.d t) = DG.d (iotaAlgHom a b t) := by
  induction t using GradedTensorProduct.induction_on_tmul with
  | zero => rw [d_zero, map_zero, d_zero]
  | @tmul i j f hf g hg =>
    rw [GradedTensorProduct.d_tmul hf, map_add, Units.smul_def, map_zsmul, iotaAlgHom_tmul,
      iotaAlgHom_tmul, (iotaL a b).map_d, (iotaR a b).map_d, iotaAlgHom_tmul,
      DG.d_mul ((iotaL a b).map_mem hf), Units.smul_def]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

/-- **`ι_{a,b} : ONH_a ⊗ ONH_b → ONH_{a+b}`** (`a, b ≥ 2`) as a morphism of dg rings. -/
def iota : (𝒜 ᵍ⊗[ℤ] ℬ) →ᵈᵍ+* ONH (a + 2 + b) where
  __ := (iotaAlgHom a b).toRingHom
  map_mem' ht := iotaAlgHom_mem_grading a b ht
  map_d' t := iotaAlgHom_d a b t

theorem iota_tmul (f : ONH a) (g : ONH b) :
    iota a b (f ᵍ⊗ₜ[ℤ] g) = iotaL a b f * iotaR a b g := iotaAlgHom_tmul a b f g

end ONH

end OddMath.Frontier.EQOnhDG
