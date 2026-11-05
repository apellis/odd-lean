/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicTopQuotient
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVCokernel

/-! # Two-colour cyclotomic crossing tensors

The independently balanced source for Brundan–Ellis (1.12), with the literal
crossing map of `DeformedActionAssembly.md` §§3–4. The induction endpoint is
i, the coefficient endpoint is j, and the coefficient parity shift is
p(i)p(j). Its right action remains ordinary. Both outer cyclotomic ideals
descend before lower balance is imposed. Bijectivity is a separate result.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Matrix-Hom component of `Be ⊗_D Πᵖ(eB)`, with its prescribed lower balance. -/
abbrev Source (i j : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) (⟨t⟩ : OldCategory D Sc cutoff)

/-- A tensor in the prescribed source; neither factor is an image coordinate. -/
def tensor (i j : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    Source D Sc cutoff i j v t :=
  BalancedInduction.tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨s⟩ c b

/-- The literal crossing word on affine representatives, in diagram order. -/
def crossing (i j : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k]
      hom D Sc cutoff v (s ++ [j]) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) where
  toFun c :=
    (ideal D Sc cutoff (v ++ [i]) (t ++ [j])).mkQ ∘ₗ
      (Linear.rightComp k _ (affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c)) ∘ₗ rightContext D Sc cutoff [i] _ _
  map_add' c c' := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      LinearMap.add_apply, map_add, Preadditive.comp_add]
  map_smul' a c := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      LinearMap.smul_apply, map_smul, Linear.comp_smul, RingHom.id_apply]

/-- Both cyclotomic ideals descend separately before imposing lower balance. -/
def pairing (i j : I) (v s t : List I) :
    Old D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [j]) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  LinearMap.liftQ₂ _ _ (crossing D Sc cutoff i j v s t)
    (by
      intro c hc
      apply LinearMap.ext
      intro b
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact comp_ideal D Sc cutoff _
        (comp_ideal D Sc cutoff _ (ideal_rightContext D Sc cutoff [j] hc)))
    (by
      intro b hb
      ext c
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ideal_comp D Sc cutoff (ideal_rightContext D Sc cutoff [i] hb) _)

@[simp] theorem pairing_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [j])) :
    pairing D Sc cutoff i j v s t ((ideal D Sc cutoff _ _).mkQ c)
      ((ideal D Sc cutoff _ _).mkQ b) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [j])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c) := rfl

/-- Lower cyclotomic balance retains the total-parity twist on the coefficient. -/
theorem pairing_balance (i j : I) (v : List I) (s s' t : OldCategory D Sc cutoff)
    (r : s ⟶ s') (c : (append D Sc cutoff i).obj s' ⟶ t)
    (b : (coefficient D Sc cutoff (D.parity i * D.parity j) j v).obj s) :
    pairing D Sc cutoff i j v s.word t.word ((append D Sc cutoff i).map r ≫ c) b =
      pairing D Sc cutoff i j v s'.word t.word c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map r b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word s'.word).mkQ_surjective r
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s'.word ++ [i]) t.word).mkQ_surjective c
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j])).mkQ_surjective b
  change (ideal D Sc cutoff _ _).mkQ
    (rightContext D Sc cutoff [i] _ _ b ≫
      affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i) ≫
      rightContext D Sc cutoff [j] _ _ (rightContext D Sc cutoff [i] _ _ r ≫ c)) =
    (ideal D Sc cutoff _ _).mkQ
      (rightContext D Sc cutoff [i] _ _ (b ≫ rightContext D Sc cutoff [j] _ _
        (twist k (D.parity i * D.parity j) r)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s'.word j i) ≫
        rightContext D Sc cutoff [j] _ _ c)
  have h := crossLast_comp_rightContext D Sc cutoff j i r
  rw [mul_comm (D.parity j) (D.parity i)] at h
  simp only [rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i)), h]
  simp only [Category.assoc]

/-- The prescribed crossing column after both cyclotomic descent and lower balance. -/
def toCyclotomic (i j : I) (v t : List I) : Source D Sc cutoff i j v t →ₗ[k]
    Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  BalancedInduction.lift (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩
    (fun s => TensorProduct.lift (pairing D Sc cutoff i j v s.word t))
    (fun s s' r c b => pairing_balance D Sc cutoff i j v s s' ⟨t⟩ r c b)

@[simp] theorem toCyclotomic_tensor (i j : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    toCyclotomic D Sc cutoff i j v t (tensor D Sc cutoff i j v s t c b) =
      pairing D Sc cutoff i j v s t c b := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- In algebra order this is exactly `c τₙ b`, without a coefficient permutation. -/
theorem toCyclotomic_tensor_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [j])) :
    toCyclotomic D Sc cutoff i j v t (tensor D Sc cutoff i j v s t
      ((ideal D Sc cutoff _ _).mkQ c) ((ideal D Sc cutoff _ _).mkQ b)) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [j])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c) := by
  rw [toCyclotomic_tensor, pairing_mk]

/-- `Re ⊗_S Πᵖ(eB)`, balanced before quotienting the first factor. -/
abbrev ShortTarget (i j : I) (v t : List I) :=
  BalancedInduction.Obj (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v)
    (⟨t⟩ : AffineWord D Sc cutoff)

def shortTensor (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    ShortTarget D Sc cutoff i j v t :=
  BalancedInduction.tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨s⟩ c b

/-- Quotienting the first factor on one tensor summand. -/
def qSummand (i j : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t ⊗[k] Old D Sc cutoff v (s ++ [j]) →ₗ[k]
      Source D Sc cutoff i j v t :=
  BalancedInduction.inclusion (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ ⟨s⟩ ∘ₗ
      TensorProduct.map (ideal D Sc cutoff (s ++ [i]) t).mkQ LinearMap.id

@[simp] theorem qSummand_tmul (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    qSummand D Sc cutoff i j v s t (c ⊗ₜ[k] b) =
      tensor D Sc cutoff i j v s t ((ideal D Sc cutoff _ _).mkQ c) b := rfl

theorem qSummand_balance (i j : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    qSummand D Sc cutoff i j v s t ((rightContext D Sc cutoff [i] _ _ r ≫ c) ⊗ₜ[k] b) =
      qSummand D Sc cutoff i j v s' t (c ⊗ₜ[k]
        (coefficient D Sc cutoff (D.parity i * D.parity j) j v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  rw [qSummand_tmul, qSummand_tmul]
  exact BalancedInduction.balance (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v)
    ((ideal D Sc cutoff s s').mkQ r)
    ((ideal D Sc cutoff (s' ++ [i]) t).mkQ c) b

/-- The canonical quotient changes only the first tensor factor. -/
def q (i j : I) (v t : List I) : ShortTarget D Sc cutoff i j v t →ₗ[k]
    Source D Sc cutoff i j v t :=
  BalancedInduction.lift (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩
    (fun s => qSummand D Sc cutoff i j v s.word t)
    (fun s s' r c b => qSummand_balance D Sc cutoff i j v s.word s'.word t r c b)

@[simp] theorem q_shortTensor (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    q D Sc cutoff i j v t (shortTensor D Sc cutoff i j v s t c b) =
      tensor D Sc cutoff i j v s t ((ideal D Sc cutoff _ _).mkQ c) b := by
  exact BalancedInduction.lift_tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- The canonical quotient is surjective without flatness or projectivity. -/
theorem q_surjective (i j : I) (v t : List I) : Function.Surjective (q D Sc cutoff i j v t) := by
  classical
  intro z
  obtain ⟨z, rfl⟩ := (BalancedInduction.relations (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩).mkQ_surjective z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩
  | of s z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', map_add, map_add]⟩
    | tmul c b =>
      obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s.word ++ [i]) t).mkQ_surjective c
      exact ⟨shortTensor D Sc cutoff i j v s.word t c b, q_shortTensor D Sc cutoff i j v s.word t c b⟩

/-- The descended vertical map has the literal crossing-column formula on lifts. -/
theorem toCyclotomic_q_shortTensor (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [j])) :
    toCyclotomic D Sc cutoff i j v t
      (q D Sc cutoff i j v t (shortTensor D Sc cutoff i j v s t c
        ((ideal D Sc cutoff _ _).mkQ b))) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [j])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c) := by
  rw [q_shortTensor, toCyclotomic_tensor_mk]

/-- The crossing column before imposing the enlarged cyclotomic ideal. -/
def shortCrossPair (i j : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k] Old D Sc cutoff v (s ++ [j]) →ₗ[k]
      AppendTarget D Sc cutoff i v (t ++ [j]) where
  toFun c := appendPair D Sc cutoff 0 i
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫ rightContext D Sc cutoff [j] _ _ c)
  map_add' c c' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
    simp only [appendPair_mk, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a c := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
    simp only [appendPair_mk, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem shortCrossPair_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [j])) :
    shortCrossPair D Sc cutoff i j v s t c ((ideal D Sc cutoff _ _).mkQ b) =
      appendProjection D Sc cutoff i v (t ++ [j])
        (rightContext D Sc cutoff [i] _ _ b ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
          rightContext D Sc cutoff [j] _ _ c) := by
  change appendProjection D Sc cutoff i v (t ++ [j]) _ = _
  simp only [LinearMap.comp_apply, Linear.rightComp_apply, twist_zero]

theorem shortCrossPair_balance (i j : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    shortCrossPair D Sc cutoff i j v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortCrossPair D Sc cutoff i j v s' t c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
  change shortCrossPair D Sc cutoff i j v s t _ ((ideal D Sc cutoff _ _).mkQ b) =
    shortCrossPair D Sc cutoff i j v s' t _ ((ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [j] _ _ (twist k (D.parity i * D.parity j) r)))
  rw [shortCrossPair_mk, shortCrossPair_mk]
  have h := crossLast_comp_rightContext D Sc cutoff j i r
  rw [mul_comm (D.parity j) (D.parity i)] at h
  simp only [rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s j i)), h]
  simp only [Category.assoc]

/-- The balanced short crossing column into the old-only append target. -/
def shortCross (i j : I) (v t : List I) : ShortTarget D Sc cutoff i j v t →ₗ[k]
    AppendTarget D Sc cutoff i v (t ++ [j]) :=
  BalancedInduction.lift (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩
    (fun s => TensorProduct.lift (shortCrossPair D Sc cutoff i j v s.word t))
    (fun s s' r c b => shortCrossPair_balance D Sc cutoff i j v s.word s'.word t r c b)

@[simp] theorem shortCross_tensor (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    shortCross D Sc cutoff i j v t (shortTensor D Sc cutoff i j v s t c b) =
      shortCrossPair D Sc cutoff i j v s t c b := by
  exact BalancedInduction.lift_tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- The square imposes precisely the remaining old output ideal. -/
theorem shortCross_quotient_square (i j : I) (v t : List I) :
    canonicalAppendTarget D Sc cutoff i v (t ++ [j]) ∘ₗ shortCross D Sc cutoff i j v t =
      toCyclotomic D Sc cutoff i j v t ∘ₗ q D Sc cutoff i j v t := by
  apply BalancedInduction.hom_ext
  intro s c b
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j])).mkQ_surjective b
  change canonicalAppendTarget D Sc cutoff i v (t ++ [j])
    (shortCross D Sc cutoff i j v t (shortTensor D Sc cutoff i j v s.word t c
      ((ideal D Sc cutoff _ _).mkQ b))) =
    toCyclotomic D Sc cutoff i j v t
      (q D Sc cutoff i j v t (shortTensor D Sc cutoff i j v s.word t c
        ((ideal D Sc cutoff _ _).mkQ b)))
  rw [shortCross_tensor, shortCrossPair_mk, canonicalAppendTarget_projection]
  exact (toCyclotomic_q_shortTensor D Sc cutoff i j v s.word t c b).symm

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
