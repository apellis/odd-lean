/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HalfTurn.Composite
import OddMath.QuiverHecke.SwappedVacuum.TransformedIdeal

/-!
# The half-turn on coefficient-extended Hom spaces and the transformed ideal

`docs/Nondegeneracy/SwappedVacuumCoordinates.md` §§4–5. The half-turn `U` (`halfTurnFunctor`)
gives linear maps `htPres` on the Hom spaces of the quiver Hecke supercategory, reversing words
and the direction of morphisms, and `htCoef` on the coefficient-extended Hom spaces, by
`U(a ⊗ f) = a ⊗ U(f)`, with no coefficient sign.

## Main declarations

* `htPres`, `htPres_diag_mkD`: the half-turn on Hom spaces and its value on a normal-form
  diagram.
* `htPres_diag_comp`: the signed reversal of composition, `U(f ≫ g) = (-1)^{|f||g|} U(g) ≫ U(f)`,
  for normal-form diagrams.
* `htCoef`, `htCoef_sourceCoefficientHom`: the half-turn on coefficient-extended Hom spaces.
* `htCoef_sandwich`: `U(α ⊗ A ≫ γ ⊗ B ≫ β ⊗ C) = ± α ⊗ U(C) ≫ γ ⊗ U(B) ≫ β ⊗ U(A)` for
  homogeneous `α`, `γ`, with an explicit sign; the coefficients keep their places, so no
  supercommutativity of the coefficient ring is used.
* `htPres_lastDotPower`: `U(y_last^j) = (-1)^{p(i) C(j,2)} y_first^j`.
* `elvCoefficientIdeal_le_homogeneousSpan`: `J_N` is spanned by its homogeneous elements.
* `htCoef_transformedIdeal_le`: **`U(K_N) ⊆ I_N`** (§5), for the transformed ideal with no
  extra coefficients (`T = ∅`): the half-turn maps the transformed ideal into the ELV relation
  span of the twisted parameters. The transformed polynomial (4) of colour `i` goes to `±` the
  first-strand cyclotomic polynomial of colour `i`, with a sign independent of the power.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-! ## Combinatorics of the reflected layers -/

theorem halfTurnL_append (A B : List (LayerData I)) :
    halfTurnL (A ++ B) = halfTurnL B ++ halfTurnL A := by
  simp [halfTurnL]

theorem halfTurnLD_halfTurnLD (x : LayerData I) : halfTurnLD (halfTurnLD x) = x := by
  obtain ⟨u, g, v⟩ := x
  simp [halfTurnLD]

theorem halfTurnL_halfTurnL (ls : List (LayerData I)) : halfTurnL (halfTurnL ls) = ls := by
  simp [halfTurnL, List.map_reverse, Function.comp_def, halfTurnLD_halfTurnLD]

theorem psum_halfTurnL (ls : List (LayerData I)) : psum D (halfTurnL ls) = psum D ls := by
  induction ls with
  | nil => rfl
  | cons x ls ih =>
    simp only [halfTurnL] at ih ⊢
    rw [List.map_cons, List.reverse_cons, psum_append, ih, psum_cons, add_comm]
    simp [psum, halfTurnLD]

theorem halfTurnC_append (A B : List (LayerData I)) :
    halfTurnC (k := k) D (A ++ B) =
      zsign k (psum D A * psum D B) * halfTurnC D A * halfTurnC D B := by
  induction A with
  | nil => simp [SKM.zsign]
  | cons x A ih =>
    simp only [List.cons_append, halfTurnC_cons, ih, psum_append, psum_cons, mul_add, add_mul,
      SKM.zsign_add]
    ring

theorem halfTurnWeight_mul_self (g : Shape I) : halfTurnWeight (k := k) g * halfTurnWeight g = 1 := by
  cases g with
  | dot i => simp [halfTurnWeight]
  | cross i j => by_cases h : i = j <;> simp [halfTurnWeight, h]

theorem halfTurnC_mul_self (ls : List (LayerData I)) :
    halfTurnC (k := k) D ls * halfTurnC D ls = 1 := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
    rw [halfTurnC_cons]
    calc _ = (zsign k (x.2.1.parity D * psum D ls) * zsign k (x.2.1.parity D * psum D ls)) *
          (halfTurnWeight x.2.1 * halfTurnWeight x.2.1) * (halfTurnC D ls * halfTurnC D ls) := by
          ring
      _ = 1 := by rw [zsign_mul_self, halfTurnWeight_mul_self, ih, one_mul, one_mul]

/-! ## The half-turn on Hom spaces -/

instance halfTurnFunctor_additive : (halfTurnFunctor D Sc).Additive := by
  unfold halfTurnFunctor mirrorFunctor flipFunctor; infer_instance

instance halfTurnFunctor_linear : (halfTurnFunctor D Sc).Linear k := by
  unfold halfTurnFunctor mirrorFunctor flipFunctor; infer_instance

/-- The half-turn on Hom spaces, `Hom(s, t) → Hom(t^rev, s^rev)`. -/
def htPres (s t : List I) :
    ((pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) →ₗ[k]
      ((pres D (parameterTwist D Sc)).obj (ob D t.reverse) ⟶
        (pres D (parameterTwist D Sc)).obj (ob D s.reverse)) :=
  ((pres D (parameterTwist D Sc)).castLinearEquiv (halfTurn_obj D t)
      (halfTurn_obj D s)).toLinearMap ∘ₗ
    SOp.unsopₗ _ _ ∘ₗ (halfTurnFunctor D Sc).mapLinearMap k

theorem htPres_apply {s t : List I} (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    htPres D Sc s t f = (pres D (parameterTwist D Sc)).castLinearEquiv (halfTurn_obj D t)
      (halfTurn_obj D s) (SOp.unsop ((halfTurnFunctor D Sc).map f)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The half-turn of a normal-form diagram: the reflected layers in reverse order, times
`halfTurnC`. -/
theorem htPres_diag_mkD {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    htPres D Sc s t ((pres D Sc).diag (mkD D ls h)) =
      halfTurnC (k := k) D ls •
        (pres D (parameterTwist D Sc)).diag (mkD D (halfTurnL ls) (sChain_halfTurnL h)) := by
  rw [htPres_apply, halfTurn_mkD, map_smul, Presentation.castLinearEquiv_apply,
    Presentation.castHom_diag, Diagram.cast_cast]
  refine congrArg (halfTurnC (k := k) D ls • ·) ?_
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_cast]

theorem diag_mkD_mem_parity {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    (pres D Sc).diag (mkD D ls h) ∈ Supercategory.parity (R := k) _ _ (psum D ls) :=
  Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)

theorem htPres_diag_mkD_mem_parity {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    htPres D Sc s t ((pres D Sc).diag (mkD D ls h)) ∈
      Supercategory.parity (R := k) _ _ (psum D ls) := by
  rw [htPres_diag_mkD, ← psum_halfTurnL D ls]
  exact Submodule.smul_mem _ _ (diag_mkD_mem_parity D _ _ _)

/-- **The signed reversal of composition** for normal-form diagrams:
`U(f ≫ g) = (-1)^{|f||g|} U(g) ≫ U(f)`. -/
theorem htPres_diag_comp {s t r : List I} (A B : List (LayerData I)) (hA : SChain s A t)
    (hB : SChain t B r) :
    htPres D Sc s r ((pres D Sc).diag (mkD D A hA) ≫ (pres D Sc).diag (mkD D B hB)) =
      zsign k (psum D A * psum D B) •
        (htPres D Sc t r ((pres D Sc).diag (mkD D B hB)) ≫
          htPres D Sc s t ((pres D Sc).diag (mkD D A hA))) := by
  rw [← diag_mkD_append D Sc A B (hA.append hB) hA hB, htPres_diag_mkD, htPres_diag_mkD,
    htPres_diag_mkD, Linear.smul_comp, Linear.comp_smul, ← diag_mkD_append D (parameterTwist D Sc)
      (halfTurnL B) (halfTurnL A) ((sChain_halfTurnL hB).append (sChain_halfTurnL hA)),
    smul_smul, smul_smul, halfTurnC_append]
  have e : (pres D (parameterTwist D Sc)).diag (mkD D (halfTurnL (A ++ B))
      (sChain_halfTurnL (hA.append hB))) = (pres D (parameterTwist D Sc)).diag
      (mkD D (halfTurnL B ++ halfTurnL A)
        ((sChain_halfTurnL hB).append (sChain_halfTurnL hA))) :=
    Presentation.diag_eq_of_layers_eq _ (by simp only [layers_mkD, halfTurnL_append])
  rw [e]
  congr 1
  ring

theorem htPres_id (t : List I) :
    htPres D Sc t t (𝟙 _) = 𝟙 _ := by
  have e : (𝟙 ((pres D Sc).obj (ob D t))) = (pres D Sc).diag (mkD D [] (t := t) (t' := t) rfl) := by
    rw [← Presentation.diag_id]; rfl
  rw [e, htPres_diag_mkD, halfTurnC_nil, one_smul, ← Presentation.diag_id]
  rfl

/-! ## The half-turn on coefficient-extended Hom spaces -/

/-- The half-turn on coefficient-extended Hom spaces: `a ⊗ f ↦ a ⊗ U(f)`. -/
def htCoef (s t : List I) :
    (coefficientObj D Sc s ⟶ coefficientObj D Sc t) →ₗ[k]
      (coefficientObj D (parameterTwist D Sc) t.reverse ⟶
        coefficientObj D (parameterTwist D Sc) s.reverse) :=
  (sourceTensorEquiv D (parameterTwist D Sc) t.reverse s.reverse).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (htPres D Sc s t) ∘ₗ
      (sourceTensorEquiv D Sc s t).symm.toLinearMap

/-- `U(a ⊗ f) = a ⊗ U(f)`, with no coefficient sign (§4). -/
@[simp] theorem htCoef_sourceCoefficientHom {s t : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    htCoef D Sc s t (sourceCoefficientHom D Sc a f) =
      sourceCoefficientHom D (parameterTwist D Sc) a (htPres D Sc s t f) := by
  rw [show sourceCoefficientHom D Sc a f = sourceTensorEquiv D Sc s t (a ⊗ₜ[k] f) from rfl]
  rw [htCoef, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rfl

/-- Composition of three pure coefficient tensors. -/
theorem sourceCoefficientHom_comp_comp {s v w t : List I} {p q r₁ r₂ : ZMod 2}
    {α γ : SKM.SYM D k} (β : SKM.SYM D k)
    (hα : SKM.SYM.polynomialExteriorEquiv D k α ∈ SKM.SYM.polynomialExteriorParity D k p)
    (hγ : SKM.SYM.polynomialExteriorEquiv D k γ ∈ SKM.SYM.polynomialExteriorParity D k q)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D v))
    {g : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    {h : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D t)}
    (hg : g ∈ Supercategory.parity (R := k) _ _ r₁)
    (hh : h ∈ Supercategory.parity (R := k) _ _ r₂) :
    sourceCoefficientHom D Sc α f ≫ sourceCoefficientHom D Sc γ g ≫ sourceCoefficientHom D Sc β h =
      ((koszulSign q r₂ * koszulSign p (r₁ + r₂) : ℤ) : k) •
        sourceCoefficientHom D Sc (β * γ * α) (f ≫ g ≫ h) := by
  rw [sourceCoefficientHom_comp D Sc hγ _ _ hh, Preadditive.comp_zsmul,
    sourceCoefficientHom_comp D Sc hα _ _ (Supercategory.comp_mem hg hh), smul_smul,
    ← Int.cast_smul_eq_zsmul k, Int.cast_mul, mul_comm (koszulSign q r₂ : k)]

/-! ## Signs -/

theorem koszulSign_cast (p q : ZMod 2) : ((Supercategory.koszulSign p q : ℤ) : k) = zsign k (p * q) := by
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz p with rfl | rfl <;> rcases hz q with rfl | rfl <;>
    simp [Supercategory.koszulSign, SKM.zsign]

/-! ## Homogeneous coefficients -/

/-- A coefficient of parity `p`. -/
def CoefParity (p : ZMod 2) (a : SKM.SYM D k) : Prop :=
  SKM.SYM.polynomialExteriorEquiv D k a ∈ SKM.SYM.polynomialExteriorParity D k p

theorem coefParity_one : CoefParity D 0 (1 : SKM.SYM D k) := by
  unfold CoefParity; rw [map_one]; exact SetLike.GradedOne.one_mem

theorem CoefParity.mul {p q : ZMod 2} {a b : SKM.SYM D k} (ha : CoefParity D p a)
    (hb : CoefParity D q b) : CoefParity D (p + q) (a * b) := by
  unfold CoefParity at *; rw [map_mul]; exact SetLike.GradedMul.mul_mem ha hb

theorem CoefParity.smul {p : ZMod 2} {a : SKM.SYM D k} (c : k) (ha : CoefParity D p a) :
    CoefParity D p (c • a) := by
  unfold CoefParity at *; rw [map_smul]; exact Submodule.smul_mem _ _ ha

theorem coefParity_e (i : I) (n : ℕ) : CoefParity D 0 (SKM.SYM.e D k i n) :=
  SKM.SYM.polynomialExterior_e_mem_even D k i n

theorem coefParity_delta (i : {i : I // D.parity i = 1}) :
    CoefParity D 1 (SKM.SYM.delta D k i) :=
  SKM.SYM.polynomialExterior_delta_mem_odd D k i

theorem coefParity_elvChi (i : {i : I // D.parity i = 1}) (r : ℕ) :
    CoefParity D 0 (SKM.SYM.elvChi D k i r) := by
  cases r with
  | zero => exact coefParity_one D
  | succ r => exact coefParity_e D i.1 r

theorem coefParity_elvCoefficient (i : {i : I // D.parity i = 1}) (n : ℕ) :
    CoefParity D (n : ZMod 2) (SKM.SYM.elvCoefficient D k i n) := by
  unfold SKM.SYM.elvCoefficient
  split_ifs with h
  · have : (n : ZMod 2) = 0 := by rw [← ZMod.natCast_mod, h]; rfl
    rw [this]; exact coefParity_elvChi D i _
  · have h1 : n % 2 = 1 := by omega
    have : (n : ZMod 2) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
    rw [this]
    have hm := CoefParity.mul D (coefParity_delta (k := k) D i) (coefParity_elvChi (k := k) D i (n / 2))
    rwa [add_zero] at hm

theorem coefParity_factorCoefficient (i : I) (N : ℕ) (j : Fin (N + 1)) :
    CoefParity D (((N : ZMod 2) + (j.val : ZMod 2)) * D.parity i)
      (factorCoefficient (k := k) D i N j) := by
  unfold factorCoefficient
  split_ifs with h
  · rw [h, mul_one]
    unfold SKM.SYM.elvMonicCoefficient
    have he : (((N - j.val : ℕ)) : ZMod 2) = (N : ZMod 2) + (j.val : ZMod 2) := by
      rw [Nat.cast_sub (Nat.lt_succ_iff.mp j.isLt), sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    rw [← he]
    exact (coefParity_elvCoefficient D _ _).smul D _
  · have h0 : D.parity i = 0 := by
      have : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
      exact this _ h
    rw [h0, mul_zero]
    unfold SKM.SYM.evenMonicCoefficient
    apply CoefParity.smul
    cases N - j.val with
    | zero => exact coefParity_one D
    | succ r => exact coefParity_e D i r

theorem coefParity_transformedCoefficient (i : I) (N : ℕ) (j : Fin (N + 1)) :
    CoefParity D (((N : ZMod 2) + (j.val : ZMod 2)) * D.parity i)
      (transformedCoefficient (k := k) D i N j) :=
  (coefParity_factorCoefficient D i N j).smul D _

/-! ## The half-turn of a sandwich of pure coefficient tensors -/

/-- The sign identity behind `htCoef_sandwich`. -/
theorem sandwich_sign_identity (p q A B C : ZMod 2) :
    q * C + p * (B + C) + (A * (B + C) + B * C) =
      q * C + p * (B + C) + A * (B + C) + B * C + q * A + p * (B + A) + (q * A + p * (B + A)) := by
  revert p q A B C; decide

/-- **The half-turn of a sandwich**: `U(α ⊗ A ≫ γ ⊗ B ≫ β ⊗ C) = ± α ⊗ U(C) ≫ γ ⊗ U(B) ≫ β ⊗ U(A)`
for homogeneous `α`, `γ`; the coefficients keep their places. -/
theorem htCoef_sandwich {s v w t : List I} {p q : ZMod 2} {α γ : SKM.SYM D k}
    (hα : CoefParity D p α) (hγ : CoefParity D q γ) (β : SKM.SYM D k)
    (A B C : List (LayerData I)) (hA : SChain s A v) (hB : SChain v B w) (hC : SChain w C t) :
    htCoef D Sc s t (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D A hA)) ≫
        sourceCoefficientHom D Sc γ ((pres D Sc).diag (mkD D B hB)) ≫
        sourceCoefficientHom D Sc β ((pres D Sc).diag (mkD D C hC))) =
      zsign k (q * psum D C + p * (psum D B + psum D C) + psum D A * (psum D B + psum D C) +
          psum D B * psum D C + q * psum D A + p * (psum D B + psum D A)) •
        (sourceCoefficientHom D (parameterTwist D Sc) α
            (htPres D Sc w t ((pres D Sc).diag (mkD D C hC))) ≫
          sourceCoefficientHom D (parameterTwist D Sc) γ
            (htPres D Sc v w ((pres D Sc).diag (mkD D B hB))) ≫
          sourceCoefficientHom D (parameterTwist D Sc) β
            (htPres D Sc s v ((pres D Sc).diag (mkD D A hA)))) := by
  rw [sourceCoefficientHom_comp_comp D Sc β hα hγ _ (diag_mkD_mem_parity D Sc B hB)
      (diag_mkD_mem_parity D Sc C hC),
    sourceCoefficientHom_comp_comp D (parameterTwist D Sc) β hα hγ _
      (htPres_diag_mkD_mem_parity D Sc B hB) (htPres_diag_mkD_mem_parity D Sc A hA),
    map_smul, htCoef_sourceCoefficientHom,
    ← diag_mkD_append D Sc B C (hB.append hC) hB hC,
    htPres_diag_comp D Sc A (B ++ C) hA (hB.append hC), sourceCoefficientHom_smul_right,
    diag_mkD_append D Sc B C (hB.append hC) hB hC, htPres_diag_comp D Sc B C hB hC,
    Linear.smul_comp, sourceCoefficientHom_smul_right, Category.assoc]
  simp only [smul_smul]
  congr 1
  simp only [Int.cast_mul, koszulSign_cast, psum_append, ← SKM.zsign_add]
  congr 1
  linear_combination sandwich_sign_identity p q (psum D A) (psum D B) (psum D C)

/-! ## Spanning by homogeneous pure tensors -/

/-- Coefficient-extended Homs are spanned by `α ⊗ d` with `α` homogeneous and `d` a normal-form
diagram. -/
theorem coef_induction {s t : List I}
    {P : (coefficientObj D Sc s ⟶ coefficientObj D Sc t) → Prop} (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (pure : ∀ (p : ZMod 2) (α : SKM.SYM D k), CoefParity D p α →
      ∀ (ls : List (LayerData I)) (hl : SChain s ls t),
        P (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D ls hl))))
    (x : coefficientObj D Sc s ⟶ coefficientObj D Sc t) : P x := by
  refine BoxProd.induction_on_homogeneous (P := P) x zero (fun p _ f g hf _ => ?_) add
  have key : ∀ g : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t),
      ∀ f : (coefficientObj D Sc s).fst ⟶ (coefficientObj D Sc t).fst,
      f ∈ Supercategory.parity (R := k) (coefficientObj D Sc s).fst (coefficientObj D Sc t).fst p →
        P (f ⊗ₜ[k] g) := by
    intro g
    refine (pres D Sc).hom_induction (p := fun g => ∀ f : (coefficientObj D Sc s).fst ⟶
      (coefficientObj D Sc t).fst, f ∈ Supercategory.parity (R := k) (coefficientObj D Sc s).fst (coefficientObj D Sc t).fst p →
        P (f ⊗ₜ[k] g))
      ?_ ?_ ?_ ?_ g
    · intro d f hf
      obtain ⟨ls, hl, rfl⟩ := exists_mkD d
      have := pure p ((SKM.SYM.polynomialExteriorEquiv D k).symm (SuperalgebraCat.toElem f))
        (by unfold CoefParity; rw [AlgEquiv.apply_symm_apply]; exact hf) ls hl
      have hx : sourceCoefficientHom D Sc ((SKM.SYM.polynomialExteriorEquiv D k).symm
          (SuperalgebraCat.toElem f)) ((pres D Sc).diag (mkD D ls hl)) =
          f ⊗ₜ[k] (pres D Sc).diag (mkD D ls hl) := by
        change SKM.SYM.polynomialExteriorEquiv D k _ ⊗ₜ[k] _ = _
        rw [AlgEquiv.apply_symm_apply]; rfl
      rwa [hx] at this
    · intro f _; rw [TensorProduct.tmul_zero]; exact zero
    · intro g g' hg hg' f hf; rw [TensorProduct.tmul_add]; exact add _ _ (hg f hf) (hg' f hf)
    · intro c g hg f hf
      rw [← TensorProduct.smul_tmul]
      exact hg _ (Submodule.smul_mem _ c hf)
  exact key g f hf

/-! ## The half-turn of a dot power -/

theorem pl_replicate_dot (t : List I) (n j : ℕ) {x : I} {r : List I} (h : t.drop n = x :: r) :
    pl t ((List.replicate j n).map PG.dot) = List.replicate j (t.take n, Shape.dot x, r) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, List.map_cons, pl, List.replicate_succ]
    have e : (PG.dot n).act t = t := rfl
    rw [e, ih]
    simp [PG.ld, h]

theorem halfTurnC_replicate_dot (x : LayerData I) (i : I) (hx : x.2.1 = Shape.dot i) (j : ℕ) :
    halfTurnC (k := k) D (List.replicate j x) = zsign k (D.parity i * (j.choose 2 : ℕ)) := by
  induction j with
  | zero => simp [SKM.zsign]
  | succ j ih =>
    rw [List.replicate_succ, halfTurnC_cons, ih, psum_replicate, hx, halfTurnWeight, mul_one,
      ← SKM.zsign_add, Nat.choose_succ_succ, Nat.choose_one_right]
    congr 1
    simp only [Shape.parity]
    have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hz (D.parity i) with h | h <;> rw [h] <;> push_cast <;> ring

theorem lastDot_layers (v : List I) (i : I) (j : ℕ) :
    pl (v ++ [i]) ((List.replicate j ((v ++ [i]).length - 1)).map PG.dot) =
      List.replicate j (v, Shape.dot i, []) := by
  rw [pl_replicate_dot (v ++ [i]) _ j (x := i) (r := []) (by simp)]
  simp

theorem firstDot_layers (u : List I) (i : I) (j : ℕ) :
    pl (i :: u) ((List.replicate j 0).map PG.dot) = List.replicate j ([], Shape.dot i, u) := by
  rw [pl_replicate_dot (i :: u) 0 j (x := i) (r := u) rfl]
  rfl

theorem reverse_concat_eq (v : List I) (i : I) : i :: v.reverse = (v ++ [i]).reverse := by simp

set_option backward.isDefEq.respectTransparency false in
/-- **The half-turn of a last-strand dot power**: `U(y_last^j) = (-1)^{p(i) C(j,2)} y_first^j`. -/
theorem htPres_lastDotPower (v : List I) (i : I) (j : ℕ) :
    htPres D Sc (v ++ [i]) (v ++ [i]) (lastDotPower D Sc (v ++ [i]) j) =
      zsign k (D.parity i * (j.choose 2 : ℕ)) •
        (pres D (parameterTwist D Sc)).castHom (congrArg (ob D) (reverse_concat_eq v i))
          (congrArg (ob D) (reverse_concat_eq v i))
          (firstDotPower D (parameterTwist D Sc) (i :: v.reverse) j) := by
  have hc : halfTurnC (k := k) D
      (pl (v ++ [i]) ((List.replicate j ((v ++ [i]).length - 1)).map PG.dot)) =
      zsign k (D.parity i * (j.choose 2 : ℕ)) := by
    rw [lastDot_layers]; exact halfTurnC_replicate_dot D _ i rfl j
  unfold lastDotPower firstDotPower cl
  rw [htPres_diag_mkD, hc, Presentation.castHom_diag]
  congr 1
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_cast, layers_mkD]
  rw [lastDot_layers, firstDot_layers]
  simp [halfTurnL, halfTurnLD]

/-! ## Homogeneous decomposition of the coefficient ideal -/

theorem mem_span_homogeneous (r : SKM.SYM D k) :
    r ∈ Submodule.span k {y : SKM.SYM D k | ∃ q, CoefParity D q y} := by
  set e := SKM.SYM.polynomialExteriorEquiv D k
  have hr : r = ∑ q ∈ (DirectSum.decompose (SKM.SYM.polynomialExteriorParity D k) (e r)).support,
      e.symm ((DirectSum.decompose (SKM.SYM.polynomialExteriorParity D k) (e r) q : _)) := by
    rw [← map_sum, DirectSum.sum_support_decompose, AlgEquiv.symm_apply_apply]
  rw [hr]
  refine Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨q, ?_⟩
  unfold CoefParity
  rw [AlgEquiv.apply_symm_apply]
  exact Subtype.prop _

/-- The homogeneous elements of the ideal `J`. -/
def homogeneousSpan (J : TwoSidedIdeal (SKM.SYM D k)) : Submodule k (SKM.SYM D k) :=
  Submodule.span k {y | y ∈ J ∧ ∃ q, CoefParity D q y}

theorem homogeneousSpan_mul_left (J : TwoSidedIdeal (SKM.SYM D k)) (a : SKM.SYM D k)
    {x : SKM.SYM D k} (hx : x ∈ homogeneousSpan D J) : a * x ∈ homogeneousSpan D J := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨hyJ, q, hq⟩ := hy
    induction mem_span_homogeneous D a using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨p, hp⟩ := hb
      exact Submodule.subset_span ⟨J.mul_mem_left _ _ hyJ, p + q, hp.mul D hq⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add b c _ _ hb hc => rw [add_mul]; exact Submodule.add_mem _ hb hc
    | smul c b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hb
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem homogeneousSpan_mul_right (J : TwoSidedIdeal (SKM.SYM D k)) (a : SKM.SYM D k)
    {x : SKM.SYM D k} (hx : x ∈ homogeneousSpan D J) : x * a ∈ homogeneousSpan D J := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨hyJ, q, hq⟩ := hy
    induction mem_span_homogeneous D a using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨p, hp⟩ := hb
      exact Submodule.subset_span ⟨J.mul_mem_right _ _ hyJ, q + p, hq.mul D hp⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- The coefficient ideal `J_N` is spanned by its homogeneous elements. -/
theorem elvCoefficientIdeal_le_homogeneousSpan (cutoff : I → ℕ) {x : SKM.SYM D k}
    (hx : x ∈ SKM.SYM.elvCoefficientIdeal D k cutoff) :
    x ∈ homogeneousSpan D (SKM.SYM.elvCoefficientIdeal D k cutoff) := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem y hy =>
    refine Submodule.subset_span ⟨TwoSidedIdeal.subset_span hy, ?_⟩
    rcases hy with ⟨i, r, _, rfl⟩ | ⟨i, _, rfl⟩
    · exact ⟨0, coefParity_e D i r⟩
    · exact ⟨1 + 0, (coefParity_delta D i).mul D (coefParity_elvChi D i _)⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | neg x _ hx => exact Submodule.neg_mem _ hx
  | left_absorb a x _ hx => exact homogeneousSpan_mul_left D _ a hx
  | right_absorb b x _ hx => exact homogeneousSpan_mul_right D _ b hx

/-! ## The half-turn of the transformed generators -/

theorem sChain_length {t t' : List I} {ls : List (LayerData I)} (h : SChain t ls t') :
    t'.length = t.length := by
  induction ls generalizing t with
  | nil => exact (congrArg List.length h).symm
  | cons x ls ih =>
    obtain ⟨h1, h2⟩ := h
    rw [ih h2, h1]
    obtain ⟨u, g, w⟩ := x
    cases g <;> simp [Shape.dom, Shape.cod]

theorem zsign_natCast (n : ℕ) : zsign k (n : ZMod 2) = (-1 : k) ^ n := by
  induction n with
  | zero => simp [SKM.zsign]
  | succ n ih =>
    rw [Nat.cast_succ, SKM.zsign_add, ih, pow_succ]
    simp [SKM.zsign]

theorem transformedSign_eq (P : ZMod 2) (c : ℕ) :
    (if P = 1 then (-1 : k) ^ c else 1) = zsign k (P * (c : ZMod 2)) := by
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz P with rfl | rfl
  · simp [SKM.zsign]
  · rw [one_mul, zsign_natCast]; simp

theorem sourceCoefficientHom_castHom {u u' w w' : List I} (hu : u = u') (hw : w = w')
    (a : SKM.SYM D k) (f : (pres D Sc).obj (ob D u) ⟶ (pres D Sc).obj (ob D w)) :
    sourceCoefficientHom D Sc a ((pres D Sc).castHom (congrArg (ob D) hu) (congrArg (ob D) hw) f) =
      eqToHom (congrArg (coefficientObj D Sc) hu.symm) ≫ sourceCoefficientHom D Sc a f ≫
        eqToHom (congrArg (coefficientObj D Sc) hw) := by
  subst hu hw
  simp

/-- The sign identity behind the cyclotomic case: the sandwich sign does not depend on the
power `j`. -/
theorem cyclotomic_sign_identity (N j P c p A C : ZMod 2) :
    ((N + j) * P * C + p * (j * P + C) + A * (j * P + C) + j * P * C + (N + j) * P * A +
        p * (j * P + A)) + (P * c + P * c) =
      N * P * (A + C) + p * (A + C) + A * C := by
  revert N j P c p A C; decide

set_option backward.isDefEq.respectTransparency false in
/-- **The half-turn of one term of a transformed cyclotomic sandwich**: the transformed
coefficient `(-1)^{p(i) C(j,2)} c_j` of `y_last^j` becomes the factor coefficient `c_j` of
`y_first^j`, with a sign independent of `j`. -/
theorem htCoef_cyclotomic_term {s w t : List I} {i : I} {p : ZMod 2} {α : SKM.SYM D k}
    (hα : CoefParity D p α) (β : SKM.SYM D k) (A C : List (LayerData I))
    (hA : SChain s A (w ++ [i])) (hC : SChain (w ++ [i]) C t) (N : ℕ) (j : Fin (N + 1)) :
    htCoef D Sc s t (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D A hA)) ≫
        sourceCoefficientHom D Sc (transformedCoefficient D i N j)
          (lastDotPower D Sc (w ++ [i]) j.val) ≫
        sourceCoefficientHom D Sc β ((pres D Sc).diag (mkD D C hC))) =
      zsign k ((N : ZMod 2) * D.parity i * (psum D A + psum D C) + p * (psum D A + psum D C) +
          psum D A * psum D C) •
        ((sourceCoefficientHom D (parameterTwist D Sc) α
            (htPres D Sc (w ++ [i]) t ((pres D Sc).diag (mkD D C hC))) ≫
            eqToHom (congrArg (coefficientObj D (parameterTwist D Sc))
              (reverse_concat_eq w i).symm)) ≫
          sourceCoefficientHom D (parameterTwist D Sc) (factorCoefficient D i N j)
            (firstDotPower D (parameterTwist D Sc) (i :: w.reverse) j.val) ≫
          (eqToHom (congrArg (coefficientObj D (parameterTwist D Sc)) (reverse_concat_eq w i)) ≫
            sourceCoefficientHom D (parameterTwist D Sc) β
              (htPres D Sc s (w ++ [i]) ((pres D Sc).diag (mkD D A hA))))) := by
  have hB := sChain_pl (w ++ [i]) ((List.replicate j.val ((w ++ [i]).length - 1)).map PG.dot)
  simp only [tgt_map_dot] at hB
  have e : lastDotPower D Sc (w ++ [i]) j.val = (pres D Sc).diag (mkD D _ hB) := rfl
  rw [e, htCoef_sandwich D Sc hα (coefParity_transformedCoefficient D i N j) β A _ C hA hB hC,
    ← e, htPres_lastDotPower, sourceCoefficientHom_smul_right,
    sourceCoefficientHom_castHom D (parameterTwist D Sc) (reverse_concat_eq w i)
      (reverse_concat_eq w i),
    transformedCoefficient, sourceCoefficientHom_smul]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, Category.assoc]
  congr 1
  rw [transformedSign_eq, ← SKM.zsign_add, ← SKM.zsign_add, lastDot_layers, psum_replicate]
  congr 1
  simp only [Shape.parity]
  linear_combination cyclotomic_sign_identity (N : ZMod 2) (j.val : ZMod 2) (D.parity i)
    ((j.val.choose 2 : ℕ) : ZMod 2) p (psum D A) (psum D C)

/-- **The half-turn maps the transformed ideal into the ELV relation span**:
`U(K_N) ⊆ I_N` (`SwappedVacuumCoordinates.md` §5), for the transformed ideal with no extra
coefficients. The coefficient generators `J_N` go to themselves, and the transformed
last-strand polynomial (4) of colour `i` goes, up to a sign, to the first-strand cyclotomic
polynomial of colour `i` of the twisted parameters. -/
theorem htCoef_transformedIdeal_le (cutoff : I → ℕ) (s t : List I) :
    (TransformedIdeal D Sc cutoff ∅ s t).map (htCoef D Sc s t) ≤
      ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, -, r, hr, a, b, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  refine coef_induction D Sc (P := fun a => htCoef D Sc s t (a ≫ r ≫ b) ∈
    ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse) ?_ ?_ ?_ a
  · simp
  · intro x y hx hy
    rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ hx hy
  intro p α hα A hA
  refine coef_induction D Sc (P := fun b => htCoef D Sc s t
    (sourceCoefficientHom D Sc α ((pres D Sc).diag (mkD D A hA)) ≫ r ≫ b) ∈
      ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse) ?_ ?_ ?_ b
  · simp
  · intro x y hx hy
    rw [Preadditive.comp_add, Preadditive.comp_add, map_add]; exact Submodule.add_mem _ hx hy
  intro _ β _ C hC
  rcases hr with ⟨γ, hγ, rfl⟩ | ⟨γ, hγ, _⟩ | ⟨w, i, h, rfl⟩
  · have e1 : (𝟙 ((pres D Sc).obj (ob D v))) =
        (pres D Sc).diag (mkD D [] (t := v) (t' := v) rfl) := by
      rw [← Presentation.diag_id]; rfl
    have e2 : htPres D Sc v v ((pres D Sc).diag (mkD D [] (t := v) (t' := v) rfl)) = 𝟙 _ := by
      rw [← e1]; exact htPres_id D Sc v
    have hH := elvCoefficientIdeal_le_homogeneousSpan D cutoff hγ
    clear hγ
    induction hH using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨hyJ, q, hq⟩ := hy
      rw [e1, htCoef_sandwich D Sc hα hq β A [] C hA rfl hC, e2]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨v.reverse, ?_, _,
        Or.inl ⟨y, hyJ, rfl⟩, _, _, rfl⟩)
      simp [sChain_length hC]
    | zero => simp
    | add x y _ _ hx hy =>
      rw [sourceCoefficientHom_add_left, Preadditive.add_comp, Preadditive.comp_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [sourceCoefficientHom_smul, Linear.smul_comp, Linear.comp_smul, map_smul]
      exact Submodule.smul_mem _ c hx
  · exact absurd hγ (Set.notMem_empty γ)
  · subst h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, transformedCyclotomic,
      lastBoundaryPolynomial, Preadditive.sum_comp, Preadditive.comp_sum, map_sum]
    rw [Finset.sum_congr rfl fun j _ => htCoef_cyclotomic_term D Sc hα β A C hA hC (cutoff i) j,
      ← Finset.smul_sum, ← Preadditive.comp_sum, ← Preadditive.sum_comp]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i :: w.reverse, ?_, _, ?_, _, _, rfl⟩)
    · simp [sChain_length hC]
    by_cases hP : D.parity i = 1
    · refine Or.inr (Or.inl ⟨⟨i, hP⟩, w.reverse, rfl, ?_⟩)
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id, elvCyclotomic,
        deformedCyclotomic]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [factorCoefficient, hP, ↓reduceDIte]
    · have h0 : D.parity i = 0 := by
        have : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
        exact this _ hP
      refine Or.inr (Or.inr ⟨i, h0, w.reverse, rfl, ?_⟩)
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id, evenCyclotomic,
        deformedCyclotomic]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [factorCoefficient, hP, ↓reduceDIte]

end OddMath.QuiverHecke
