import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.SKM.RouquierMixedMate
import StringDiagrams.Super.SCat
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.EvenBoundaryRecurrence
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.BoundaryNumerator
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.ContentModule

/-!
# Distinct crossing

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The old two-colour crossing and its prescribed mate

The positive distinct-colour crossing and the even balanced-induction
adjunction give the literal cup-crossing-cap of Brundan–Ellis (1.12).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def crossComponent (i j : I) (s : OldCategory D Sc cutoff) :
    ((append D Sc cutoff j) ⋙ (append D Sc cutoff i)).obj s ⟶
      ((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s :=
  (ideal D Sc cutoff _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i))

theorem cross_supernatural (i j : I) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := (append D Sc cutoff j) ⋙ (append D Sc cutoff i))
      (G := (append D Sc cutoff i) ⋙ (append D Sc cutoff j))
      (crossComponent D Sc cutoff i j) := by
  apply IsSupernatural.of_twist
  · intro s
    have hc := ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word j i)
    rw [mul_comm (D.parity j) (D.parity i)] at hc
    exact Submodule.mem_map_of_mem hc
  · intro s t f

    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    have htw : twist k (D.parity i * D.parity j) (X := s) (Y := t)
        (((ideal D Sc cutoff s.word t.word).mkQ r) : s ⟶ t) =
        ((ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r) : s ⟶ t) := by
      rw [twist_apply, oldCategory_proj, oldCategory_proj]
      change (ideal D Sc cutoff s.word t.word).mkQ (proj k 0 r) +
        sign k (D.parity i * D.parity j) • (ideal D Sc cutoff s.word t.word).mkQ (proj k 1 r) =
        (ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
      rw [twist_apply, map_add, map_smul]
    rw [htw]
    change (ideal D Sc cutoff (s.word ++ [j] ++ [i]) (t.word ++ [i] ++ [j])).mkQ
      (rightContext D Sc cutoff [i] _ _ (rightContext D Sc cutoff [j] _ _ r) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc t.word j i)) =
      (ideal D Sc cutoff (s.word ++ [j] ++ [i]) (t.word ++ [i] ++ [j])).mkQ
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i) ≫
          rightContext D Sc cutoff [j] _ _
            (rightContext D Sc cutoff [i] _ _ (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)))
    have h := crossLast_comp_rightContext D Sc cutoff j i
      (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
    rw [mul_comm (D.parity j) (D.parity i), twist_twist] at h
    exact congrArg
      (ideal D Sc cutoff (s.word ++ [j] ++ [i]) (t.word ++ [i] ++ [j])).mkQ h.symm

/-- Positive two-colour crossing under the canonical induction comparisons. -/
def moduleCross (i j : I) :
    oldInduction D Sc cutoff i ≫ oldInduction D Sc cutoff j ⟶
      oldInduction D Sc cutoff j ≫ oldInduction D Sc cutoff i :=
  Superfunctor.homMk (BalancedInduction.mixedCrossComponent_supernatural
    (append D Sc cutoff i) (append D Sc cutoff j) (cross_supernatural D Sc cutoff i j)).toSuperNatTrans

@[simp] theorem moduleCross_app (i j : I) (r : ZMod 2)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (moduleCross D Sc cutoff i j).app r N =
      if r = D.parity i * D.parity j then
        BalancedInduction.mixedCrossComponent (append D Sc cutoff i) (append D Sc cutoff j)
          (cross_supernatural D Sc cutoff i j) N else 0 := rfl

/-- The prescribed rectangular cup-crossing-cap, using the fixed even adjunction. -/
def moduleMate (i j : I) :
    oldRestriction D Sc cutoff j ≫ oldInduction D Sc cutoff i ⟶
      oldInduction D Sc cutoff i ≫ oldRestriction D Sc cutoff j :=
  SKM.rectangularMate (k := k) (B := SCat.{u,u,u + 1} k)
    (oldAppendAdjunction D Sc cutoff j) (oldAppendAdjunction D Sc cutoff j)
    (oldInduction D Sc cutoff i) (oldInduction D Sc cutoff i) (moduleCross D Sc cutoff i j)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

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
end

end

section

/-! # Canonical parity transport for the two-colour balanced source

The map J in `DeformedActionAssembly.md` §4 twists the entire first tensor
factor. The coefficient's right action remains ordinary, including its
exterior directions. These are underlying linear equivalences; no claim
about representing a supernatural map by ordinary precomposition is made.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev SourceWithParity (p : ZMod 2) (i j : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i) (coefficient D Sc cutoff p j v)
    (⟨t⟩ : OldCategory D Sc cutoff)

def parityTensor (p : ZMod 2) (i j : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    SourceWithParity D Sc cutoff p i j v t :=
  BalancedInduction.tensor (append D Sc cutoff i) (coefficient D Sc cutoff p j v) ⟨s⟩ c b

private theorem parityTensor_balance (p q : ZMod 2) (i j : I) (v s s' t : List I)
    (r : Old D Sc cutoff s s') (c : Old D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    parityTensor D Sc cutoff q i j v s t
      (oldTwist D Sc cutoff (p + q) (s ++ [i]) t
        ((append D Sc cutoff i).map (X := ⟨s⟩) (Y := ⟨s'⟩) r ≫ c)) b =
      parityTensor D Sc cutoff q i j v s' t
        (oldTwist D Sc cutoff (p + q) (s' ++ [i]) t c)
        ((coefficient D Sc cutoff p j v).map (X := ⟨s⟩) (Y := ⟨s'⟩) r b) := by
  have hb := BalancedInduction.balance (append D Sc cutoff i) (coefficient D Sc cutoff q j v)
    (v := (⟨s⟩ : OldCategory D Sc cutoff)) (v' := ⟨s'⟩)
    (twist k (p + q) r) (twist k (p + q) c) b
  rw [Supercategory.map_twist, ← twist_comp] at hb
  rw [oldCategory_twist, oldCategory_twist] at hb
  change parityTensor D Sc cutoff q i j v s t _ b =
    parityTensor D Sc cutoff q i j v s' t _
      ((coefficient D Sc cutoff q j v).map (twist k (p + q) r) b) at hb
  trans parityTensor D Sc cutoff q i j v s' t
    (oldTwist D Sc cutoff (p + q) (s' ++ [i]) t c)
      ((coefficient D Sc cutoff q j v).map (X := ⟨s⟩) (Y := ⟨s'⟩) (twist k (p + q) r) b)
  · exact hb
  congr 1
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s s').mkQ_surjective r
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
  rw [oldCategory_twist]
  change (ideal D Sc cutoff v (s' ++ [j])).mkQ
      (b ≫ rightContext D Sc cutoff [j] _ _ (twist k q (twist k (p + q) r))) =
    (ideal D Sc cutoff v (s' ++ [j])).mkQ
      (b ≫ rightContext D Sc cutoff [j] _ _ (twist k p r))
  rw [← twist_add, show q + (p + q) = p by rw [add_left_comm, zmod2_add_self, add_zero]]

/-- Change the coefficient shift by twisting the whole first tensor factor. -/
def parityTransport (p q : ZMod 2) (i j : I) (v t : List I) :
    SourceWithParity D Sc cutoff p i j v t →ₗ[k] SourceWithParity D Sc cutoff q i j v t :=
  BalancedInduction.lift (append D Sc cutoff i) (coefficient D Sc cutoff p j v) ⟨t⟩
    (fun s => BalancedInduction.inclusion (append D Sc cutoff i)
      (coefficient D Sc cutoff q j v) ⟨t⟩ s ∘ₗ
        TensorProduct.map (oldTwist D Sc cutoff (p + q) (s.word ++ [i]) t) LinearMap.id)
    (fun s s' r c b => parityTensor_balance D Sc cutoff p q i j v s.word s'.word t r c b)

@[simp] theorem parityTransport_tensor (p q : ZMod 2) (i j : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    parityTransport D Sc cutoff p q i j v t (parityTensor D Sc cutoff p i j v s t c b) =
      parityTensor D Sc cutoff q i j v s t (oldTwist D Sc cutoff (p + q) (s ++ [i]) t c) b := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i) (coefficient D Sc cutoff p j v)
    ⟨t⟩ _ _ ⟨s⟩ c b

/-- The canonical transport and its prescribed reverse are inverse. -/
theorem parityTransport_involutive (p q : ZMod 2) (i j : I) (v t : List I) :
    parityTransport D Sc cutoff q p i j v t ∘ₗ parityTransport D Sc cutoff p q i j v t =
      LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s c b
  change parityTransport D Sc cutoff q p i j v t
    (parityTransport D Sc cutoff p q i j v t (parityTensor D Sc cutoff p i j v s.word t c b)) = _
  rw [parityTransport_tensor, parityTransport_tensor, add_comm q p, oldTwist_twice]
  rfl

def sourceParityEquiv (i j : I) (v t : List I) :
    SourceWithParity D Sc cutoff 0 i j v t ≃ₗ[k] Source D Sc cutoff i j v t :=
  LinearEquiv.ofLinearMap
    (parityTransport D Sc cutoff 0 (D.parity i * D.parity j) i j v t)
    (parityTransport D Sc cutoff (D.parity i * D.parity j) 0 i j v t)
    (parityTransport_involutive D Sc cutoff (D.parity i * D.parity j) 0 i j v t)
    (parityTransport_involutive D Sc cutoff 0 (D.parity i * D.parity j) i j v t)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # Distinct-colour append tails

The PBW crossing decoder for Brundan–Ellis (1.12) peels the first crossing
of every mixed append tail. Identity tails are absent by last-colour support;
the distinct-colour dot slide has no divided-difference correction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem append_cl_heq {s s' t t' : List I} {L L' : List PG}
    (hs : s = s') (ht : t = t') (hL : L = L')
    (h : SChain s (pl s L) t) (h' : SChain s' (pl s' L') t') :
    HEq (cl D Sc s t L h) (cl D Sc s' t' L' h') := by
  subst s'
  subst t'
  subst L'
  rfl

def appendShuffleSizeCast {n n' : ℕ} (e : n = n') :
    AppendShuffle (show n + 1 = n + 1 from rfl) ≃
      AppendShuffle (show n' + 1 = n' + 1 from rfl) := by
  subst n'
  exact Equiv.refl _

theorem appendShuffleSizeCast_word {n n' : ℕ} (e : n = n')
    (d : AppendShuffle (show n + 1 = n + 1 from rfl)) :
    Categorification.TypeA.canWord (n' + 1) (appendShuffleSizeCast e d).1⁻¹ =
    Categorification.TypeA.canWord (n + 1) d.1⁻¹ := by
  subst n'
  rfl

def appendIndexWithTail (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    AppendIdx i v w :=
  ⟨(m, y.1.1, y.1.2, d), y.2.1, y.2.2.1, by
    rw [appendCrossingWord, cw_append, tgt_append,
      tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2)),
      y.tgt_cw]
    exact h⟩

theorem appendIndexWithTail_target (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    (appendIndexWithTail i y d m h).oldTarget = u := y.tgt_cw

theorem appendTail_cross_chain {i : I} {s t : List I} (z : AppendIdx i s t) :
    SChain (z.oldTarget ++ [i])
      (pl (z.oldTarget ++ [i]) (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))) t := by
  have hz := z.2.2.2
  rw [appendCrossingWord, cw_append, tgt_append,
    tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord s.length z.1.2.2.1))] at hz
  change tgt (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) = t at hz
  simpa only [hz] using sChain_pl (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))

theorem appendTail_cross_fits {i : I} {s t : List I} (z : AppendIdx i s t) :
    Fits (z.oldTarget ++ [i]).length
      (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) := by
  simpa only [AppendIdx.oldTarget, List.length_append, length_tgt] using
    fits_cw (Categorification.TypeA.validWord_canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)

theorem appendRunWord_castSucc (n : ℕ) (j : Fin (n + 1)) :
    cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
      PG.cross n :: cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) := by
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc]
  have hj : j.val ≤ n := Nat.lt_succ_iff.mp j.2
  rw [show n + 1 - j.val = (n - j.val) + 1 by omega, List.range'_concat, cw_append]
  simp only [cw, List.reverse_singleton, List.map_singleton, List.cons_append, List.nil_append]
  congr 2
  omega

theorem appendCrossingShuffle_exists (i : I) (v s t : List I)
    (z : AppendIdx i s t) (hv : s.length + 1 = v.length) :
    ∃ d : AppendShuffle (appendLen v i),
      cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹) =
        PG.cross s.length ::
          cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹) := by
  let d0 := AppendShuffle.cast (appendLen s i) rfl z.1.2.2.2
  let j := (appendRunEquiv s.length).symm d0
  let d1 := appendShuffleSizeCast hv (appendRun (s.length + 1) j.castSucc)
  refine ⟨AppendShuffle.cast rfl (appendLen v i) d1, ?_⟩
  rw [AppendShuffle.canWord_cast, appendShuffleSizeCast_word]
  rw [appendRunWord_castSucc]
  have hj : appendRun s.length j = d0 := (appendRunEquiv s.length).apply_symm_apply d0
  rw [hj, AppendShuffle.canWord_cast]

theorem appendTail_power_cross (i : I) (s t : List I) (z : AppendIdx i s t) :
    affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
      appendMovingPower D Sc cutoff i z.oldTarget z.1.1 ≫
        affineUnit D Sc cutoff _ _
          (cl D Sc _ _ (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))
            (appendTail_cross_chain z)) := by
  have hl : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  unfold appendMovingPower
  rw [← affineUnit_comp]
  apply congrArg (affineUnit D Sc cutoff _ _)
  unfold appendTail
  rw [dotE_pow, cl_comp]
  apply eq_of_heq
  apply append_cl_heq D Sc rfl rfl
  simp only [hl, List.map_replicate]

/-- The first crossing exchanges the two literal last colours, with the
unchanged final output colour retained as a spectator through the tail. -/
theorem appendTail_cross_heq (i j : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [j])) (e : x.oldTarget = s ++ [j])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    HEq (appendTail D Sc x)
      (((dotE D Sc (s ++ [j] ++ [i]) (s.length + 1)) ^ x.1.1) ≫
        crossLast D Sc s j i ≫ affineRightContext D Sc [j] _ _ (cl D Sc _ _ L h)) := by
  have hl : v.length = s.length + 1 := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt, List.length_append,
      List.length_singleton] using hh
  change HEq (appendTail D Sc x)
    (_ ≫ crossLast D Sc s j i ≫ (cl D Sc _ _ L h ▷ (pres D Sc).obj (ob D [j])))
  rw [dotE_pow, crossLast, cl_whiskerRight D Sc _ _ [j] hf, cl_comp, cl_comp]
  unfold appendTail
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.singleton_append]

theorem appendRunWord_mixed_shape (i j : I) (hij : i ≠ j)
    (u t : List I) (n : ℕ) (hn : u.length = n) (a : Fin (n + 1))
    (ht : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (n + 1)
      (appendRun n a).1⁻¹)) = t ++ [j]) :
    ∃ (s : List I) (L : List PG), u = s ++ [j] ∧
      cw (Categorification.TypeA.canWord (n + 1) (appendRun n a).1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  cases n with
  | zero =>
    have ha : a = Fin.last 0 := by apply Fin.ext; have := a.2; simp only [Fin.val_last]; omega
    have hw : cw (Categorification.TypeA.canWord 1 (appendRun 0 a).1⁻¹) = [] := by
      rw [ha, canWord_appendRun]
      simp
    rw [hw, tgt_nil] at ht
    have he : i = j := by simpa using congrArg List.getLast? ht
    exact (hij he).elim
  | succ n =>
    revert ht
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro ht
      have hw : cw (Categorification.TypeA.canWord (n + 1 + 1)
          (appendRun (n + 1) (Fin.last (n + 1))).1⁻¹) = [] := by
        rw [canWord_appendRun]
        simp
      rw [hw, tgt_nil] at ht
      have he : i = j := by simpa using congrArg List.getLast? ht
      exact (hij he).elim
    · intro ht
      have hu : u ≠ [] := by intro h; simp [h] at hn
      obtain ⟨s, c, rfl⟩ := (List.eq_nil_or_concat' u).resolve_left hu
      have hs : s.length = n := by
        simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hn
      let L := cw (Categorification.TypeA.canWord (n + 1) (appendRun n a).1⁻¹)
      have hw : cw (Categorification.TypeA.canWord (n + 2)
          (appendRun (n + 1) a.castSucc).1⁻¹) = PG.cross s.length :: L := by
        simpa only [hs] using appendRunWord_castSucc n a
      have hf : Fits (s ++ [i]).length L := by
        simpa only [List.length_append, List.length_singleton, hs] using
          fits_cw (Categorification.TypeA.validWord_canWord (n + 1) (appendRun n a).1⁻¹)
      rw [hw, tgt_cons] at ht
      have hcross : (PG.cross s.length).act (s ++ [c] ++ [i]) = s ++ [i] ++ [c] := by
        have hc : tgt (s ++ [c] ++ [i]) [PG.cross s.length] = s ++ [i] ++ [c] :=
          tgt_eq (by simpa using sChain_crossAt s [] c i)
        simpa only [tgt_cons, tgt_nil] using hc
      rw [hcross, tgt_append_right [c] hf] at ht
      have hcj : c = j := by simpa using congrArg List.getLast? ht
      subst c
      have ht' := List.append_cancel_right ht
      exact ⟨s, L, rfl, hw, hf, by rw [← ht']; exact sChain_pl _ _⟩

/-- Every mixed append coordinate has a first crossing; no identity row is
discarded or quotiented out. -/
theorem appendTail_mixed_shape (i j : I) (hij : i ≠ j) (v t : List I)
    (x : AppendIdx i v (t ++ [j])) :
    ∃ (s : List I) (L : List PG), x.oldTarget = s ++ [j] ∧
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  let d₀ := AppendShuffle.cast (appendLen v i) rfl x.1.2.2.2
  let a := (appendRunEquiv v.length).symm d₀
  have ha : appendRun v.length a = d₀ := (appendRunEquiv v.length).apply_symm_apply d₀
  have hw : cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length a).1⁻¹) =
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) := by
    rw [ha, AppendShuffle.canWord_cast]
  have hl : x.oldTarget.length = v.length := by simp only [AppendIdx.oldTarget, length_tgt]
  have ht : tgt (x.oldTarget ++ [i])
      (cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length a).1⁻¹)) = t ++ [j] := by
    rw [hw]
    exact tgt_eq (appendTail_cross_chain x)
  simpa only [hw] using appendRunWord_mixed_shape i j hij x.oldTarget t v.length hl a ht

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # Distinct-colour crossing power slides

The mixed PBW inverse in `DeformedActionAssembly.md` §3 uses the signed
substitution of the moving input dot across the last crossing. Distinct
colours have no divided-difference correction. All old arrows retain their
full exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem crossing_dot_slide (i j : I) (hij : i ≠ j) (s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPower D Sc cutoff i (s ++ [j]) 1 ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c =
      SKM.zsign k (D.parity i * D.parity j) •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
          rightContext D Sc cutoff [j] _ _ (appendMovingPower D Sc cutoff i s 1 ≫ c)) := by
  have hd : rightContext D Sc cutoff [j] (s ++ [i]) (s ++ [i])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) =
      affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [j]) s.length) := by
    apply congrArg (affineUnit D Sc cutoff (s ++ [i] ++ [j]) (s ++ [i] ++ [j]))
    exact dotE_whiskerRight D Sc (s ++ [i]) [j] s.length (by simp)
  have hs := lastDotE_comp_crossLast_ne D Sc (i := i) s hij.symm
  rw [mul_comm (D.parity j) (D.parity i)] at hs
  simp only [appendMovingPower, pow_one, List.length_append, List.length_singleton]
  rw [rightContext_comp, hd,
    ← Category.assoc (affineUnit D Sc cutoff _ _ _), ← affineUnit_comp,
    hs, map_smul, affineUnit_comp]
  simp only [Linear.smul_comp, Category.assoc]

theorem crossing_power_slide (i j : I) (hij : i ≠ j) (s t : List I) (m : ℕ)
    (c : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPower D Sc cutoff i (s ++ [j]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c =
      SKM.zsign k (D.parity i * D.parity j) ^ m •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
          rightContext D Sc cutoff [j] _ _ (appendMovingPower D Sc cutoff i s m ≫ c)) := by
  induction m generalizing c with
  | zero => simp [appendMovingPower, affineUnit_id, End.one_def]
  | succ m ih =>
    have hp (v : List I) : appendMovingPower D Sc cutoff i v (m + 1) =
        appendMovingPower D Sc cutoff i v m ≫ appendMovingPower D Sc cutoff i v 1 := by
      unfold appendMovingPower
      rw [pow_one, pow_succ', End.mul_def, affineUnit_comp]
    rw [hp, Category.assoc, crossing_dot_slide D Sc cutoff i j hij,
      Linear.comp_smul, ih, smul_smul, ← pow_succ']
    rw [hp]
    simp only [Category.assoc]

theorem projection_crossing_power_slide (i j : I) (hij : i ≠ j) (v s t : List I)
    (m : ℕ) (r : hom D Sc cutoff v (s ++ [j])) (c : hom D Sc cutoff (s ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [j])
      (rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [j]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
        rightContext D Sc cutoff [j] _ _ c) =
      SKM.zsign k (D.parity i * D.parity j) ^ m •
        appendProjection D Sc cutoff i v (t ++ [j])
          (rightContext D Sc cutoff [i] _ _ r ≫
            affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
            rightContext D Sc cutoff [j] _ _ (appendMovingPower D Sc cutoff i s m ≫ c)) := by
  rw [crossing_power_slide D Sc cutoff i j hij, Linear.comp_smul, map_smul]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # Distinct-colour balanced PBW crossing decoder

The crossing-coset inverse required in Brundan–Ellis (1.12) and
`DeformedActionAssembly.md` §3, before imposing the output-old ideal.
The full cyclotomic quotient and prescribed mate comparison are separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Insert a shorter crossing word with its unchanged old quotient coefficient. -/
def wordLift (i j : I) (v q s t : List I) (hs : q = s ++ [j])
    (L : List PG) (m : ℕ) (ht : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i j v t := by
  subst q
  exact (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ ⟨s⟩) ∘ₗ
      TensorProduct.mk k _ _ (appendMovingPower D Sc cutoff i s m ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L ht))

/-- Decode the crossing part of a normalized append tail. -/
def data (i j : I) (v q t : List I) (L : List PG) (m : ℕ) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i j v t := by
  by_cases hL : L = []
  · exact 0
  · by_cases hs : q = q.dropLast ++ [j]
    · by_cases ht : SChain (q.dropLast ++ [i]) (pl (q.dropLast ++ [i]) L.tail) t
      · exact SKM.zsign k (D.parity i * D.parity j) ^ m •
          wordLift D Sc cutoff i j v q q.dropLast t hs L.tail m ht
      · exact 0
    · exact 0

/-- Full old quotient coordinates are decoded without choosing representatives in the ideal. -/
def decode (i j : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [j]) →ₗ[k] ShortTarget D Sc cutoff i j v t :=
  (DirectSum.toModule k _ _ fun q : AppendIdx.Tail i v (t ++ [j]) =>
    data D Sc cutoff i j v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1) ∘ₗ
      (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [j])).toLinearMap

@[simp] theorem data_nil (i j : I) (v q t : List I) (m : ℕ) :
    data D Sc cutoff i j v q t [] m = 0 := by
  simp [data]

private theorem appendTailPair_transport {i : I} {v s s' w : List I}
    (e : s = s') (r : hom D Sc cutoff v s)
    (a : (pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (b : (pres D Sc).obj (ob D (s' ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (hab : HEq a b) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ a)
      ((ideal D Sc cutoff v s).mkQ r) =
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ b)
      ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'
  cases hab
  rfl

@[simp] theorem data_cross (i j : I) (v s t : List I) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    data D Sc cutoff i j v (s ++ [j]) t (PG.cross s.length :: L) m b =
      SKM.zsign k (D.parity i * D.parity j) ^ m •
        shortTensor D Sc cutoff i j v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
  dsimp only [data]
  rw [dite_eq_right (List.cons_ne_nil _ _)]
  have he : (s ++ [j]).dropLast = s := List.dropLast_concat
  rw [dite_eq_left (congrArg (· ++ [j]) he).symm]
  have ht : SChain ((s ++ [j]).dropLast ++ [i])
      (pl ((s ++ [j]).dropLast ++ [i]) (PG.cross s.length :: L).tail) t := by
    simpa only [he, List.tail_cons] using h
  rw [dite_eq_left ht, LinearMap.smul_apply]
  congr 1
  have aux (s' : List I) (e : s' = s) (hs : s ++ [j] = s' ++ [j])
      (hc : SChain (s' ++ [i]) (pl (s' ++ [i]) L) t) :
      wordLift D Sc cutoff i j v (s ++ [j]) s' t hs L m hc b =
        shortTensor D Sc cutoff i j v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
    subst s'; rfl
  exact aux _ he _ ht

theorem decode_pair_representative (i j : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [j]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    decode D Sc cutoff i j v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _
        (appendTail D Sc q.representative)) b) =
    data D Sc cutoff i j v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
  have he : decode D Sc cutoff i j v t
      (appendOldReconstruct D Sc cutoff 0 i v (t ++ [j]) (DirectSum.lof k _ _ q b)) =
      data D Sc cutoff i j v q.representative.oldTarget t
        (cw (Categorification.TypeA.canWord (v ++ [i]).length
          q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
    simp only [decode, LinearMap.comp_apply, LinearEquiv.coe_coe,
      appendOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]
  have hu : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc q.representative : hom D Sc cutoff
          (q.representative.oldTarget ++ [i]) (t ++ [j])) := rfl
  rw [hu]
  simpa only [appendOldReconstruct, DirectSum.toModule_lof] using he

private theorem data_transport (i j : I) {v s s' t : List I}
    (e : s = s') (L : List PG) (m : ℕ) (r : hom D Sc cutoff v s) :
    data D Sc cutoff i j v s t L m ((ideal D Sc cutoff v s).mkQ r) =
    data D Sc cutoff i j v s' t L m ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'; rfl

/-- Repeated old normal forms with the same tail give the same decoded balanced class. -/
theorem decode_pair (i j : I) (v t : List I)
    (x : AppendIdx i v (t ++ [j])) (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i j v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
        ((ideal D Sc cutoff v x.oldTarget).mkQ r)) =
    data D Sc cutoff i j v x.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)) x.1.1
        ((ideal D Sc cutoff v x.oldTarget).mkQ r) := by
  let q : AppendIdx.Tail i v (t ++ [j]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  rw [appendTailPair_transport D Sc cutoff ht r _ _
    (appendTail_heq_of_tailKey_eq D Sc x q.representative hk), decode_pair_representative]
  have hm := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = q.representative.1.1 at hm
  change x.1.2.2.2 = q.representative.1.2.2.2 at hd
  rw [← hm, ← hd]
  exact (data_transport D Sc cutoff i j ht _ _ r).symm

/-- The mixed crossing word in the old-only append quotient. -/
def crossingClass (i j : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [j])) (c : hom D Sc cutoff (s ++ [i]) t) :
    AppendTarget D Sc cutoff i v (t ++ [j]) :=
  appendProjection D Sc cutoff i v (t ++ [j])
    (rightContext D Sc cutoff [i] _ _ r ≫
      affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
      rightContext D Sc cutoff [j] _ _ c)

theorem decode_canonical_crossing (i j : I) (hij : i ≠ j) (v s t : List I)
    (x : AppendIdx i v (t ++ [j])) (e : x.oldTarget = s ++ [j])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i j v t
      (crossingClass D Sc cutoff i j v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) =
      shortTensor D Sc cutoff i j v s t
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))
        ((ideal D Sc cutoff v (s ++ [j])).mkQ (e ▸ r)) := by
  have he := appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i j v s t x e L hw hf h)
  have hc := decode_pair D Sc cutoff i j v t x r
  rw [he, hw, data_transport D Sc cutoff i j e, data_cross D Sc cutoff i j v s t L x.1.1 h] at hc
  simp only [appendPair_mk, twist_zero, affineUnit_comp,
    ← rightContext_affineUnit] at hc
  have hp : appendMovingPower D Sc cutoff i (s ++ [j]) x.1.1 =
      affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [j] ++ [i]) (s.length + 1)) ^ x.1.1) := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [← hp, projection_crossing_power_slide D Sc cutoff i j hij, map_smul] at hc
  have hu : IsUnit (SKM.zsign k (D.parity i * D.parity j) ^ x.1.1) := by
    apply IsUnit.pow
    unfold SKM.zsign
    split <;> simp
  exact hu.smul_left_cancel.mp hc

/-- Recover every smaller append tail, including zero Hom corners. -/
theorem decode_crossing_tail (i j : I) (hij : i ≠ j) (v s t : List I)
    (z : AppendIdx i s t) (r : hom D Sc cutoff v (z.oldTarget ++ [j])) :
    decode D Sc cutoff i j v t
      (crossingClass D Sc cutoff i j v z.oldTarget t r
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))) =
      shortTensor D Sc cutoff i j v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))
        ((ideal D Sc cutoff v (z.oldTarget ++ [j])).mkQ r) := by
  by_cases hr : r = 0
  · simp [hr, crossingClass, shortTensor, BalancedInduction.tensor]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hr
  have hv : s.length + 1 = v.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, List.length_append, List.length_singleton,
      AppendIdx.oldTarget] using hh.symm
  obtain ⟨d, hd⟩ := appendCrossingShuffle_exists i v s t z hv
  have hzlen : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  let L := cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)
  have hc := appendTail_cross_chain z
  have hf := appendTail_cross_fits z
  have htarget : tgt (z.oldTarget ++ [j] ++ [i])
      (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = t ++ [j] := by
    rw [hd, show PG.cross s.length = PG.cross z.oldTarget.length from congrArg PG.cross hzlen.symm,
      tgt_cons]
    have hcross : tgt (z.oldTarget ++ [j] ++ [i]) [PG.cross z.oldTarget.length] =
        z.oldTarget ++ [i] ++ [j] := tgt_eq (by simpa using sChain_crossAt z.oldTarget [] j i)
    simp only [tgt_cons, tgt_nil] at hcross
    rw [hcross]
    exact (tgt_append_right [j] hf).trans (congrArg (· ++ [j]) (tgt_eq hc))
  let x := appendIndexWithTail i y d z.1.1 htarget
  have he : x.oldTarget = z.oldTarget ++ [j] := appendIndexWithTail_target i y d z.1.1 htarget
  let r' : hom D Sc cutoff v x.oldTarget := he.symm ▸ r
  have hr' : he ▸ r' = r := by
    exact (show ∀ {a b : List I} (e : a = b) (q : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ q : hom D Sc cutoff v a) = q from
        by intro a b e q; cases e; rfl) he r
  have hword : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross z.oldTarget.length :: L := by simpa only [x, appendIndexWithTail, hzlen] using hd
  have hh := decode_canonical_crossing D Sc cutoff i j hij v z.oldTarget t
    x he L hword hf hc r'
  rw [hr'] at hh
  rw [appendTail_power_cross]
  exact hh

/-- Full affine balance in the independently defined short source. -/
theorem tensor_balance (i j : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    shortTensor D Sc cutoff i j v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i j v s' t c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

/-- The prescribed column on an arbitrary lifted old quotient coefficient. -/
theorem column_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (r : hom D Sc cutoff v (s ++ [j])) :
    shortCross D Sc cutoff i j v t
      (shortTensor D Sc cutoff i j v s t c ((ideal D Sc cutoff _ _).mkQ r)) =
      crossingClass D Sc cutoff i j v s t r c := by
  rw [shortCross_tensor, shortCrossPair_mk]
  rfl

/-- Recovery on a smaller tail for every old quotient coefficient. -/
theorem decode_short_tail (i j : I) (hij : i ≠ j) (v s t : List I) (z : AppendIdx i s t)
    (b : Old D Sc cutoff v (z.oldTarget ++ [j])) :
    decode D Sc cutoff i j v t (shortCross D Sc cutoff i j v t
      (shortTensor D Sc cutoff i j v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b)) =
      shortTensor D Sc cutoff i j v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (z.oldTarget ++ [j])).mkQ_surjective b
  rw [column_mk]
  exact decode_crossing_tail D Sc cutoff i j hij v s t z r

/-- Every full-coefficient balanced generator is recovered. -/
theorem decode_tensor (i j : I) (hij : i ≠ j) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    decode D Sc cutoff i j v t (shortCross D Sc cutoff i j v t
      (shortTensor D Sc cutoff i j v s t c b)) = shortTensor D Sc cutoff i j v s t c b := by
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i s t).symm.surjective c
  induction f using Finsupp.induction_linear with
  | zero => simp [shortTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    have hadd (c c' : hom D Sc cutoff (s ++ [i]) t) :
        shortTensor D Sc cutoff i j v s t (c + c') b =
          shortTensor D Sc cutoff i j v s t c b + shortTensor D Sc cutoff i j v s t c' b := by
      simp only [shortTensor, BalancedInduction.tensor, TensorProduct.add_tmul, map_add]
    simp only [map_add, hadd, hf, hg]
  | single z a =>
    rw [appendAffineEquiv_symm_single]
    have hfactor : (a ⊗ₜ[k] appendElt D Sc z : hom D Sc cutoff (s ++ [i]) t) =
        rightContext D Sc cutoff [i] _ _
          (coefficientTwist D cutoff (appendTailParity D z) a ⊗ₜ[k] z.old.nf) ≫
            affineUnit D Sc cutoff _ _ (appendTail D Sc z) := by
      have he : affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z :
            hom D Sc cutoff (z.oldTarget ++ [i]) t) := rfl
      rw [he]
      exact (append_insert_twisted_coefficient D Sc cutoff z a).symm
    rw [hfactor, tensor_balance]
    exact decode_short_tail D Sc cutoff i j hij v s t z _

/-- Left inverse on all balanced classes, not only their chosen representatives. -/
theorem decode_comp_shortCross (i j : I) (hij : i ≠ j) (v t : List I) :
    decode D Sc cutoff i j v t ∘ₗ shortCross D Sc cutoff i j v t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s c b
  exact decode_tensor D Sc cutoff i j hij v s.word t c b

@[simp] theorem decode_shortCross (i j : I) (hij : i ≠ j) (v t : List I)
    (z : ShortTarget D Sc cutoff i j v t) :
    decode D Sc cutoff i j v t (shortCross D Sc cutoff i j v t z) = z :=
  LinearMap.congr_fun (decode_comp_shortCross D Sc cutoff i j hij v t) z

theorem shortCross_injective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Injective (shortCross D Sc cutoff i j v t) :=
  Function.LeftInverse.injective (decode_shortCross D Sc cutoff i j hij v t)

/-- Every mixed append tail lies in the crossing column; distinct support
leaves no polynomial row. -/
theorem appendPair_mem_range_shortCross (i j : I) (hij : i ≠ j) (v t : List I)
    (x : AppendIdx i v (t ++ [j])) (r : hom D Sc cutoff v x.oldTarget) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
      ((ideal D Sc cutoff v x.oldTarget).mkQ r) ∈
      LinearMap.range (shortCross D Sc cutoff i j v t) := by
  obtain ⟨s, L, e, hw, hf, h⟩ := appendTail_mixed_shape i j hij v t x
  rw [appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i j v s t x e L hw hf h)]
  simp only [appendPair_mk, twist_zero, affineUnit_comp, ← rightContext_affineUnit]
  have hp : affineUnit D Sc cutoff _ _
      ((dotE D Sc (s ++ [j] ++ [i]) (s.length + 1)) ^ x.1.1) =
      appendMovingPower D Sc cutoff i (s ++ [j]) x.1.1 := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [hp, projection_crossing_power_slide D Sc cutoff i j hij]
  refine ⟨SKM.zsign k (D.parity i * D.parity j) ^ x.1.1 •
    shortTensor D Sc cutoff i j v s t
      (appendMovingPower D Sc cutoff i s x.1.1 ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))
      ((ideal D Sc cutoff v (s ++ [j])).mkQ (e ▸ r)), ?_⟩
  rw [map_smul, column_mk]
  rfl

/-- The crossing column is onto the entire mixed old-only append target. -/
theorem shortCross_surjective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Surjective (shortCross D Sc cutoff i j v t) := by
  intro z
  obtain ⟨f, rfl⟩ := appendOldReconstruct_surjective D Sc cutoff 0 i v (t ++ [j]) z
  change appendOldReconstruct D Sc cutoff 0 i v (t ++ [j]) f ∈
    LinearMap.range (shortCross D Sc cutoff i j v t)
  induction f using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | of q b =>
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective b
    change appendOldReconstruct D Sc cutoff 0 i v (t ++ [j]) (DirectSum.lof k _ _ q _) ∈ _
    rw [appendOldReconstruct, DirectSum.toModule_lof]
    exact appendPair_mem_range_shortCross D Sc cutoff i j hij v t q.representative r

/-- The explicit PBW crossing equivalence before the output-old quotient. -/
def crossingEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    ShortTarget D Sc cutoff i j v t ≃ₗ[k] AppendTarget D Sc cutoff i v (t ++ [j]) :=
  LinearEquiv.ofBijective (shortCross D Sc cutoff i j v t)
    ⟨shortCross_injective D Sc cutoff i j hij v t,
      shortCross_surjective D Sc cutoff i j hij v t⟩

@[simp] theorem crossingEquiv_symm (i j : I) (hij : i ≠ j) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [j])) :
    (crossingEquiv D Sc cutoff i j hij v t).symm z = decode D Sc cutoff i j v t z := by
  obtain ⟨w, rfl⟩ := shortCross_surjective D Sc cutoff i j hij v t z
  rw [decode_shortCross D Sc cutoff i j hij]
  exact (crossingEquiv D Sc cutoff i j hij v t).symm_apply_apply w

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # Kernel of the two-colour short-column quotient

The kernel is computed from the first-factor cyclotomic ideal on the prescribed
balanced tensor. No crossing-image source or injectivity assertion is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor.Distinct

/-- First-factor cyclotomic relations in the affine balanced source. -/
def firstIdeal (i j : I) (v t : List I) : Submodule k (ShortTarget D Sc cutoff i j v t) :=
  Submodule.span k {z | ∃ s, ∃ c : hom D Sc cutoff (s ++ [i]) t,
    c ∈ ideal D Sc cutoff (s ++ [i]) t ∧ ∃ b : Old D Sc cutoff v (s ++ [j]),
      shortTensor D Sc cutoff i j v s t c b = z}

/-- Each indicated ideal tensor is killed by the canonical quotient. -/
theorem firstIdeal_le_ker_q (i j : I) (v t : List I) :
    firstIdeal D Sc cutoff i j v t ≤ LinearMap.ker (q D Sc cutoff i j v t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, c, hc, b, rfl⟩
  change q D Sc cutoff i j v t _ = 0
  have hz : (ideal D Sc cutoff (s ++ [i]) t).mkQ c = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hc
  rw [q_shortTensor, hz]
  change BalancedInduction.inclusion (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ ⟨s⟩ (0 ⊗ₜ[k] b) = 0
  rw [zero_tmul, map_zero]

/-- The affine tensor pairing followed by the specified ideal quotient. -/
def quotientPair (i j : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [j]) →ₗ[k]
        ShortTarget D Sc cutoff i j v t ⧸ firstIdeal D Sc cutoff i j v t :=
  LinearMap.compr₂
    ((TensorProduct.mk k _ _).compr₂
      (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
        (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ ⟨s⟩))
    (firstIdeal D Sc cutoff i j v t).mkQ

/-- Descent in the first factor alone. -/
def inversePair (i j : I) (v s t : List I) :
    Old D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [j]) →ₗ[k]
        ShortTarget D Sc cutoff i j v t ⧸ firstIdeal D Sc cutoff i j v t :=
  (ideal D Sc cutoff (s ++ [i]) t).liftQ (quotientPair D Sc cutoff i j v s t) (by
    intro c hc
    apply LinearMap.ext
    intro b
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span ⟨s, c, hc, b, rfl⟩)

@[simp] theorem inversePair_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    inversePair D Sc cutoff i j v s t ((ideal D Sc cutoff _ _).mkQ c) b =
      (firstIdeal D Sc cutoff i j v t).mkQ (shortTensor D Sc cutoff i j v s t c b) := rfl

theorem shortTensor_balance (i j : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    shortTensor D Sc cutoff i j v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i j v s' t c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

theorem inversePair_balance (i j : I) (v : List I) (s s' t : OldCategory D Sc cutoff)
    (r : s ⟶ s') (c : (append D Sc cutoff i).obj s' ⟶ t)
    (b : (coefficient D Sc cutoff (D.parity i * D.parity j) j v).obj s) :
    inversePair D Sc cutoff i j v s.word t.word ((append D Sc cutoff i).map r ≫ c) b =
      inversePair D Sc cutoff i j v s'.word t.word c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map r b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word s'.word).mkQ_surjective r
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s'.word ++ [i]) t.word).mkQ_surjective c
  exact congrArg (firstIdeal D Sc cutoff i j v t.word).mkQ
    (shortTensor_balance D Sc cutoff i j v s.word s'.word t.word r c b)

/-- The reverse map is defined on the lower-cyclotomic balanced tensor itself. -/
def inverse (i j : I) (v t : List I) : Source D Sc cutoff i j v t →ₗ[k]
    ShortTarget D Sc cutoff i j v t ⧸ firstIdeal D Sc cutoff i j v t :=
  BalancedInduction.lift (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩
    (fun s => TensorProduct.lift (inversePair D Sc cutoff i j v s.word t))
    (fun s s' r c b => inversePair_balance D Sc cutoff i j v s s' ⟨t⟩ r c b)

@[simp] theorem inverse_tensor_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    inverse D Sc cutoff i j v t (tensor D Sc cutoff i j v s t
      ((ideal D Sc cutoff _ _).mkQ c) b) =
      (firstIdeal D Sc cutoff i j v t).mkQ (shortTensor D Sc cutoff i j v s t c b) := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ _ _ ⟨s⟩ _ b

theorem inverse_q (i j : I) (v t : List I) :
    inverse D Sc cutoff i j v t ∘ₗ q D Sc cutoff i j v t =
      (firstIdeal D Sc cutoff i j v t).mkQ := by
  apply BalancedInduction.hom_ext
  intro s c b
  change inverse D Sc cutoff i j v t
    (q D Sc cutoff i j v t (shortTensor D Sc cutoff i j v s.word t c b)) = _
  rw [q_shortTensor, inverse_tensor_mk]
  rfl

/-- Exact kernel equality for the canonical quotient, without a flatness assumption. -/
theorem ker_q (i j : I) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i j v t) = firstIdeal D Sc cutoff i j v t := by
  apply le_antisymm
  · intro z hz
    have h := congrArg (fun f => f z) (inverse_q D Sc cutoff i j v t)
    change inverse D Sc cutoff i j v t (q D Sc cutoff i j v t z) =
      (firstIdeal D Sc cutoff i j v t).mkQ z at h
    rw [LinearMap.mem_ker.mp hz, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h.symm
  · exact firstIdeal_le_ker_q D Sc cutoff i j v t

end CyclotomicCrossingTensor.Distinct
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The output-old ideal in distinct last-colour corners

Advances `DeformedActionAssembly.md` §2, the full-ELV extension of KKO I
equality (9.3). The output-old span retains the last colour as a spectator.
First-position relations move only past tail arrows, with their full total
parity. No relation is commuted through the first crossing.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Relations imposed on the old output word, keeping the last colour fixed. -/
def outputOldRelations (j : I) (v t : List I) :
    Submodule k (hom D Sc cutoff v (t ++ [j])) :=
  Submodule.span k {z | ∃ s, ∃ r : hom D Sc cutoff s t,
    r ∈ ideal D Sc cutoff s t ∧ ∃ c : hom D Sc cutoff v (s ++ [j]),
      c ≫ rightContext D Sc cutoff [j] s t r = z}

theorem outputOldRelations_le_ideal (j : I) (v t : List I) :
    outputOldRelations D Sc cutoff j v t ≤ ideal D Sc cutoff v (t ++ [j]) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, hr, c, rfl⟩
  exact comp_ideal D Sc cutoff c (ideal_rightContext D Sc cutoff [j] hr)

theorem outputOldRelations_precomp (j : I) {v w t : List I}
    (c : hom D Sc cutoff v w) {z : hom D Sc cutoff w (t ++ [j])}
    (hz : z ∈ outputOldRelations D Sc cutoff j w t) :
    c ≫ z ∈ outputOldRelations D Sc cutoff j v t := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, r, hr, b, rfl⟩ := hz
    exact Submodule.subset_span ⟨s, r, hr, c ≫ b, Category.assoc _ _ _⟩
  | zero => simpa only [Limits.comp_zero] using
      (outputOldRelations D Sc cutoff j v t).zero_mem
  | add a b _ _ ha hb =>
    simpa only [Preadditive.comp_add] using Submodule.add_mem _ ha hb
  | smul a z _ hz =>
    simpa only [Linear.comp_smul] using Submodule.smul_mem _ a hz

/-- Reverse tail transport uses the total relation parity. The first strand
is untouched throughout the tail arrow. -/
theorem relation_comp_tail (i : I) {v w : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    relation D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ (affineInsert D Sc i v w f) =
      affineUnit D Sc cutoff _ _
        (affineInsert D Sc i v w (twist k ((cutoff i : ZMod 2) * D.parity i) f)) ≫
          relation D Sc cutoff i w := by
  induction f using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [map_zero, Limits.comp_zero, Limits.zero_comp]
  | add f g hf hg =>
    simp only [map_add, Preadditive.comp_add, Preadditive.add_comp, hf, hg]
  | hom q f hf =>
    rw [twist_of_mem _ hf, map_smul, map_smul, Linear.smul_comp, ← koszulSign_smul]
    have h := congrArg (koszulSign ((cutoff i : ZMod 2) * D.parity i) q • ·)
      (tail_relation_homogeneous D Sc cutoff i f hf)
    simpa only [smul_smul, koszulSign_mul_self, one_smul] using h.symm

/-- A first-position relation followed by a last-dot power remains an
output-old relation. The parity involution acts on the whole old Hom. -/
theorem relation_lastPower_outputOldRelations (i j : I) (s t : List I)
    (m : ℕ) (b : hom D Sc cutoff (i :: s) t) :
    relation D Sc cutoff i (s ++ [j]) ≫ appendMovingPower D Sc cutoff j (i :: s) m ≫
        rightContext D Sc cutoff [j] (i :: s) t b ∈
      outputOldRelations D Sc cutoff j ((i :: s) ++ [j]) t := by
  have hmove := appendMovingPower_twisted_rightContext D Sc cutoff j (i :: s) (i :: s) m
    (twist k (m • D.parity j) (relation D Sc cutoff i s))
  rw [twist_twist] at hmove
  rw [← rightContext_relation D Sc cutoff [j] i s, ← Category.assoc, ← hmove,
    Category.assoc, ← rightContext_comp]
  exact Submodule.subset_span ⟨i :: s,
    twist k (m • D.parity j) (relation D Sc cutoff i s) ≫ b,
    ideal_comp D Sc cutoff (twist_ideal D Sc cutoff _ (relation_mem D Sc cutoff i s)) b,
    appendMovingPower D Sc cutoff j (i :: s) m, rfl⟩

private theorem relation_tail_parabolic_mem (i j : I) (v s t l r : List I)
    (hl : l = i :: s) (hr : r = [j])
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])))
    (F : (pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D (l ++ r)))
    (hF : HEq F (affineInsert D Sc i v (s ++ [j]) f))
    (b : NFIdx l t) (c : NFIdx r [j])
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    relation D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ F ≫
        (a ⊗ₜ[k] (((pres D Sc).obj (ob D l) ◁ c.nf) ≫
          (b.nf ▷ (pres D Sc).obj (ob D [j]))) :
            hom D Sc cutoff (l ++ r) (t ++ [j])) ∈
      outputOldRelations D Sc cutoff j (i :: v) t := by
  subst l
  subst r
  have hF' : F = affineInsert D Sc i v (s ++ [j]) f := eq_of_heq hF
  subst F
  let P : hom D Sc cutoff ((i :: s) ++ [j]) (t ++ [j]) :=
    a ⊗ₜ[k] (((pres D Sc).obj (ob D (i :: s)) ◁ c.nf) ≫
      (b.nf ▷ (pres D Sc).obj (ob D [j])))
  change relation D Sc cutoff i v ≫
    affineUnit D Sc cutoff _ _ (affineInsert D Sc i v (s ++ [j]) f) ≫ P ∈ _
  rw [← Category.assoc, relation_comp_tail D Sc cutoff i f, Category.assoc]
  apply outputOldRelations_precomp
  obtain ⟨m, rfl⟩ := (singleNFIndex_bijective j).surjective c
  have hp : P =
      appendMovingPower D Sc cutoff j (i :: s) m ≫
        rightContext D Sc cutoff [j] (i :: s) t (a ⊗ₜ[k] b.nf) := by
    dsimp only [P]
    rw [singleNFIndex_nf, appendMovingPower_whisker, rightContext_tmul]
    exact (affineUnit_comp_coefficient D Sc cutoff _ _ a).symm
  rw [hp]
  exact relation_lastPower_outputOldRelations D Sc cutoff i j s t m (a ⊗ₜ[k] b.nf)

private theorem relation_outputLast_term_mem (i j : I) (hij : i ≠ j) (v t : List I)
    (hlen : t.length + [j].length = (i :: v).length) (x : ShIdx hlen)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    relation D Sc cutoff i v ≫
        (affineUnit D Sc cutoff _ _ (shPsi D Sc t.length x.1.1) ≫
          shuffleParabolic D Sc cutoff x a) ∈
      outputOldRelations D Sc cutoff j (i :: v) t := by
  have hr := outputLast_last_block x
  obtain ⟨s, L, hL, hl, ht, hw⟩ :=
    outputLast_tail_factor hij v t.length hlen x.1 hr
  let f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])) :=
    cl D Sc v (s ++ [j]) (cw L) (by rw [← ht]; exact sChain_pl v (cw L))
  have hF : HEq (shPsi D Sc t.length x.1.1) (affineInsert D Sc i v (s ++ [j]) f) := by
    change HEq (shPsi D Sc t.length x.1.1) ((pres D Sc).obj (ob D [i]) ◁ f)
    dsimp only [f]
    rw [cl_whiskerLeft]
    exact OutputShuffle.cl_heq D Sc _ _ hw
  exact relation_tail_parabolic_mem D Sc cutoff i j v s t
    (shL (i :: v) t.length x.1.1) (shR (i :: v) t.length x.1.1)
    hl hr f (shPsi D Sc t.length x.1.1) hF x.2.1 x.2.2 a

/-- In a distinct last-colour corner, the first-position relation lands in
the old output ideal. The long output-last shuffle is absent by support. -/
theorem relation_comp_outputOldRelations (i j : I) (hij : i ≠ j) (v t : List I)
    (h : hom D Sc cutoff (i :: v) (t ++ [j])) :
    relation D Sc cutoff i v ≫ h ∈ outputOldRelations D Sc cutoff j (i :: v) t := by
  by_cases hlen : t.length + [j].length = (i :: v).length
  · let S := (outputOldRelations D Sc cutoff j (i :: v) t).comap
      (Linear.leftComp k _ (relation D Sc cutoff i v))
    exact hom_mem_of_shuffle_parabolic D Sc cutoff hlen S
      (relation_outputLast_term_mem D Sc cutoff i j hij v t hlen) h
  · have hh : h = 0 := hom_eq_zero_of_length_ne D Sc cutoff (by
      intro he
      apply hlen
      simpa only [List.length_append] using he.symm) h
    rw [hh, Limits.comp_zero]
    exact Submodule.zero_mem _

/-- The moving-strand summand of the one-sided ideal decomposition is
already an output-old relation in every distinct-colour corner. -/
theorem appendW_range_le_outputOldRelations (i j : I) (hij : i ≠ j) (v t : List I) :
    LinearMap.range (Linear.leftComp k (obj D Sc cutoff (t ++ [j]))
      (appendW D Sc cutoff i v)) ≤ outputOldRelations D Sc cutoff j (v ++ [i]) t := by
  rintro _ ⟨h, rfl⟩
  change appendW D Sc cutoff i v ≫ h ∈ _
  rw [appendW, Category.assoc]
  exact outputOldRelations_precomp D Sc cutoff j _
    (relation_comp_outputOldRelations D Sc cutoff i j hij v t h)

/-- The word-corner form of KKO I (9.3) for the noncentral full-ELV relation.
Both old ideals remain literal; empty words and zero cutoffs are included. -/
theorem ideal_eq_appendRelations_sup_outputOldRelations
    (i j : I) (hij : i ≠ j) (v t : List I) :
    ideal D Sc cutoff (v ++ [i]) (t ++ [j]) =
      appendRelations D Sc cutoff i v (t ++ [j]) ⊔
        outputOldRelations D Sc cutoff j (v ++ [i]) t := by
  apply le_antisymm
  · rw [ideal_eq_appendRelations_sup_range]
    exact sup_le_sup_left (appendW_range_le_outputOldRelations D Sc cutoff i j hij v t) _
  · exact sup_le (appendRelations_le_ideal D Sc cutoff i v (t ++ [j]))
      (outputOldRelations_le_ideal D Sc cutoff j (v ++ [i]) t)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The mixed crossing after both outer cyclotomic quotients

The full-coefficient crossing isomorphism required in Brundan–Ellis (1.12),
`DeformedActionAssembly.md` §§2–4. Equality (9.3) identifies the output-old
quotient with the first-factor quotient in the independently balanced source.
The literal cup-crossing-cap comparison is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Ordinary output postcomposition in the old-only append quotient. -/
def outputPost (i : I) (v : List I) {w z : List I} (r : hom D Sc cutoff w z) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v z :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v z)
    (Linear.rightComp k _ r) (fun _ hh => appendRelations_comp D Sc cutoff i hh r)

@[simp] theorem outputPost_projection (i : I) (v : List I) {w z : List I}
    (r : hom D Sc cutoff w z) (f : hom D Sc cutoff (v ++ [i]) w) :
    outputPost D Sc cutoff i v r (appendProjection D Sc cutoff i v w f) =
      appendProjection D Sc cutoff i v z (f ≫ r) := rfl

/-- Postcomposing a crossing class by an old ideal arrow lands in the
image of the literal first-factor tensor ideal. -/
theorem outputPost_shortCross_mem_map (i j : I) (v w z : List I)
    (r : hom D Sc cutoff w z) (hr : r ∈ ideal D Sc cutoff w z)
    (a : ShortTarget D Sc cutoff i j v w) :
    outputPost D Sc cutoff i v (rightContext D Sc cutoff [j] _ _ r)
      (shortCross D Sc cutoff i j v w a) ∈
      (firstIdeal D Sc cutoff i j v z).map (shortCross D Sc cutoff i j v z) := by
  let S := (firstIdeal D Sc cutoff i j v z).map (shortCross D Sc cutoff i j v z)
  have hzero : S.mkQ ∘ₗ outputPost D Sc cutoff i v
      (rightContext D Sc cutoff [j] _ _ r) ∘ₗ shortCross D Sc cutoff i j v w = 0 := by
    apply BalancedInduction.hom_ext
    intro s c b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [j])).mkQ_surjective b
    change S.mkQ (outputPost D Sc cutoff i v _
      (shortCross D Sc cutoff i j v w (shortTensor D Sc cutoff i j v s.word w c _))) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨shortTensor D Sc cutoff i j v s.word z (c ≫ r)
      ((ideal D Sc cutoff v (s.word ++ [j])).mkQ b),
        Submodule.subset_span ⟨s.word, c ≫ r, comp_ideal D Sc cutoff c hr, _, rfl⟩, ?_⟩
    rw [shortCross_tensor, shortCrossPair_mk, shortCross_tensor, shortCrossPair_mk,
      outputPost_projection, rightContext_comp]
    simp only [Category.assoc]
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun hzero a)

/-- The second outer ideal is precisely accounted for by the first tensor ideal. -/
theorem projection_outputOldRelations_mem_map (i j : I) (hij : i ≠ j) (v t : List I)
    (f : hom D Sc cutoff (v ++ [i]) (t ++ [j]))
    (hf : f ∈ outputOldRelations D Sc cutoff j (v ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [j]) f ∈
      (firstIdeal D Sc cutoff i j v t).map (shortCross D Sc cutoff i j v t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨s, r, hr, c, rfl⟩ := hf
    obtain ⟨a, ha⟩ := shortCross_surjective D Sc cutoff i j hij v s
      (appendProjection D Sc cutoff i v (s ++ [j]) c)
    have hs := outputPost_shortCross_mem_map D Sc cutoff i j v s t r hr a
    rw [ha, outputPost_projection] at hs
    exact hs
  | zero =>
    simpa only [map_zero] using Submodule.zero_mem
      ((firstIdeal D Sc cutoff i j v t).map (shortCross D Sc cutoff i j v t))
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul a b _ hb => simpa only [map_smul] using Submodule.smul_mem _ a hb

/-- Exact kernel after identifying both outer quotient spans by (9.3). -/
theorem ker_canonical_shortCross (i j : I) (hij : i ≠ j) (v t : List I) :
    LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [j]) ∘ₗ
      shortCross D Sc cutoff i j v t) = firstIdeal D Sc cutoff i j v t := by
  apply le_antisymm
  · intro a ha
    obtain ⟨f, hf⟩ := appendProjection_surjective D Sc cutoff i v (t ++ [j])
      (shortCross D Sc cutoff i j v t a)
    have hi : f ∈ ideal D Sc cutoff (v ++ [i]) (t ++ [j]) := by
      have hz := LinearMap.mem_ker.mp ha
      change canonicalAppendTarget D Sc cutoff i v (t ++ [j])
        (shortCross D Sc cutoff i j v t a) = 0 at hz
      rw [← hf, canonicalAppendTarget_projection] at hz
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [ideal_eq_appendRelations_sup_outputOldRelations D Sc cutoff i j hij v t] at hi
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp hi
    have he : appendProjection D Sc cutoff i v (t ++ [j]) c =
        shortCross D Sc cutoff i j v t a := by
      rw [← hf, ← hbc, map_add, (appendProjection_eq_zero_iff D Sc cutoff i v _ b).mpr hb,
        zero_add]
    obtain ⟨a', ha', h⟩ := projection_outputOldRelations_mem_map D Sc cutoff i j hij v t c hc
    have hsame : a' = a := shortCross_injective D Sc cutoff i j hij v t (h.trans he)
    exact hsame ▸ ha'
  · intro a ha
    rw [shortCross_quotient_square]
    change toCyclotomic D Sc cutoff i j v t (q D Sc cutoff i j v t a) = 0
    rw [LinearMap.mem_ker.mp (firstIdeal_le_ker_q D Sc cutoff i j v t ha), map_zero]

/-- Injectivity after both outer quotients, without tensor flatness. -/
theorem toCyclotomic_injective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Injective (toCyclotomic D Sc cutoff i j v t) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨a, rfl⟩ := q_surjective D Sc cutoff i j v t z
  have ha : a ∈ LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [j]) ∘ₗ
      shortCross D Sc cutoff i j v t) := by
    rw [shortCross_quotient_square]
    exact hz
  rw [ker_canonical_shortCross D Sc cutoff i j hij v t] at ha
  exact firstIdeal_le_ker_q D Sc cutoff i j v t ha

/-- Surjectivity after both outer quotients. -/
theorem toCyclotomic_surjective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Surjective (toCyclotomic D Sc cutoff i j v t) := by
  intro z
  obtain ⟨a, rfl⟩ := canonicalAppendTarget_surjective D Sc cutoff i v (t ++ [j]) z
  obtain ⟨b, rfl⟩ := shortCross_surjective D Sc cutoff i j hij v t a
  refine ⟨q D Sc cutoff i j v t b, ?_⟩
  exact (LinearMap.congr_fun (shortCross_quotient_square D Sc cutoff i j v t) b).symm

/-- The prescribed balanced crossing is an isomorphism in every distinct corner. -/
def cyclotomicEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    Source D Sc cutoff i j v t ≃ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  LinearEquiv.ofBijective (toCyclotomic D Sc cutoff i j v t)
    ⟨toCyclotomic_injective D Sc cutoff i j hij v t,
      toCyclotomic_surjective D Sc cutoff i j hij v t⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The prescribed distinct mate and the cyclotomic crossing decoder

Brundan–Ellis (1.12), via `DeformedActionAssembly.md` §4: the literal positive
cup-crossing-cap equals the checked crossing isomorphism after canonical J.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev ModuleSource (i j : I) (v t : List I) :=
  ((BalancedInduction.induction (append D Sc cutoff i)).obj
    ((BalancedInduction.restriction (append D Sc cutoff j)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)

/-- The canonical coefficient-zero identification, induced from the fixed module iso. -/
def moduleSourceZeroEquiv (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t ≃ₗ[k] SourceWithParity D Sc cutoff 0 i j v t :=
  moduleIsoLinearEquiv
    (((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientRestrictionModuleIso D Sc cutoff j v)).symm)
    (⟨t⟩ : OldCategory D Sc cutoff)

private theorem coefficientRestriction_inv_app (j : I) (v : List I) (q : ZMod 2)
    (s : OldCategory D Sc cutoff) :
    (coefficientRestrictionModuleIso D Sc cutoff j v).inv.app q s =
      if q = 0 then LinearMap.id else 0 := rfl

@[simp] theorem moduleSourceZeroEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    moduleSourceZeroEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff j)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b) =
      parityTensor D Sc cutoff 0 i j v s t g b := by
  have h := BalancedInduction.moduleMap_total_tensor (append D Sc cutoff i)
    (coefficientRestrictionModuleIso D Sc cutoff j v).inv
    (⟨t⟩ : OldCategory D Sc cutoff) (⟨s⟩ : OldCategory D Sc cutoff) g b
  rw [coefficientRestriction_inv_app, coefficientRestriction_inv_app] at h
  simp only [↓reduceIte, one_ne_zero] at h
  change _ = BalancedInduction.tensor (append D Sc cutoff i)
      (coefficientZeroModule D Sc cutoff j v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff i) (coefficientZeroModule D Sc cutoff j v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff) (twist k 1 g) (0 : Old D Sc cutoff v (s ++ [j])) at h
  rw [BalancedInduction.tensor_zero_right, add_zero] at h
  exact h

/-- The prescribed J twists the whole first factor, including exterior coefficients. -/
def moduleSourceParityEquiv (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t ≃ₗ[k] Source D Sc cutoff i j v t :=
  (moduleSourceZeroEquiv D Sc cutoff i j v t).trans (sourceParityEquiv D Sc cutoff i j v t)

@[simp] theorem moduleSourceParityEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    moduleSourceParityEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff j)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b) =
      tensor D Sc cutoff i j v s t
        (oldTwist D Sc cutoff (D.parity i * D.parity j) (s ++ [i]) t g) b := by
  rw [moduleSourceParityEquiv, LinearEquiv.trans_apply, moduleSourceZeroEquiv_tensor]
  change parityTransport D Sc cutoff 0 _ i j v t (parityTensor D Sc cutoff 0 i j v s t g b) = _
  rw [parityTransport_tensor, zero_add]
  rfl

theorem pairing_eq_append_comp (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    pairing D Sc cutoff i j v s t g b =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫
        crossComponent D Sc cutoff i j ⟨s⟩ ≫
        (append D Sc cutoff j).map
          (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
  rfl

/-- Co-Yoneda evaluation of the literal rectangular mate, with its target
endpoint fixed before comparing source carriers. -/
def evaluatedMate (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (OldInductionRepresentable.equiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj ⟨t⟩)).toLinearMap ∘ₗ
    SVec.toLinearMap (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total ⟨t⟩)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The ordinary-right kernel of the prescribed distinct mate

The arbitrary-module extension in `DeformedActionAssembly.md` §4, for
Brundan–Ellis (1.12), requires naturality under literal ordinary right
precomposition. The kernel map below is the evaluated categorical mate,
with its checked PBW inverse. No signed representing map is substituted
for the ordinary-right kernel action.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The source coefficient tensor retains ordinary precomposition on its
second factor. -/
abbrev sourceKernel (i j : I) (t : OldCategory D Sc cutoff) :=
  MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t

abbrev targetKernel (i j : I) (t : OldCategory D Sc cutoff) :=
  BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
    ((append D Sc cutoff j).obj t)

/-- The prescribed crossing-mate formula, before choosing its PBW inverse. -/
def kernelMateComponent (i j : I) (v t : OldCategory D Sc cutoff) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) v t →ₗ[k]
      ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff j).obj t) :=
  MixedIndResKernel.mateComponent (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) v t

@[simp] theorem kernelMateComponent_tensor (i j : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff j).obj s) :
    kernelMateComponent D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      (append D Sc cutoff i).map b ≫ crossComponent D Sc cutoff i j s ≫
        twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g) :=
  MixedIndResKernel.mateComponent_tensor (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) v s t g b

/-- Ordinary-right naturality holds for every old arrow, including odd
and inhomogeneous full exterior coefficients. -/
theorem kernelMateComponent_precompose (i j : I) (u v t : OldCategory D Sc cutoff)
    (r : u ⟶ v) :
    kernelMateComponent D Sc cutoff i j u t ∘ₗ
      MixedIndResKernel.precompose (k := k) (append D Sc cutoff i) (append D Sc cutoff j) r t =
      (Linear.leftComp k _ ((append D Sc cutoff i).map r)) ∘ₗ
        kernelMateComponent D Sc cutoff i j v t :=
  MixedIndResKernel.mateComponent_precompose (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) u v t r

/-- The zero-shift coefficient is identified before induction, using only
an ordinary coefficient natural isomorphism. -/
def kernelSourceCoefficientIso (j : I) (v : List I) :
    ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ≅
      coefficient D Sc cutoff 0 j v :=
  (coefficientRestrictionIso D Sc cutoff j v).symm

def kernelSourceZeroEquiv (i j : I) (v t : List I) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) ⟨v⟩ ⟨t⟩ ≃ₗ[k]
      SourceWithParity D Sc cutoff 0 i j v t :=
  BalancedInduction.coefficientEquiv (append D Sc cutoff i)
    (kernelSourceCoefficientIso D Sc cutoff j v) ⟨t⟩

@[simp] theorem kernelSourceZeroEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    kernelSourceZeroEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b) =
      parityTensor D Sc cutoff 0 i j v s t g b := by
  exact BalancedInduction.coefficientEquiv_tensor (append D Sc cutoff i)
    (kernelSourceCoefficientIso D Sc cutoff j v) ⟨t⟩ ⟨s⟩ g b

/-- The full quotient decoder and canonical J provide this kernel equivalence. -/
def kernelCrossingEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) ⟨v⟩ ⟨t⟩ ≃ₗ[k]
      Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (kernelSourceZeroEquiv D Sc cutoff i j v t).trans
    ((sourceParityEquiv D Sc cutoff i j v t).trans (cyclotomicEquiv D Sc cutoff i j hij v t))

theorem kernelCrossingEquiv_tensor (i j : I) (hij : i ≠ j) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    kernelCrossingEquiv D Sc cutoff i j hij v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b) =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫ crossComponent D Sc cutoff i j ⟨s⟩ ≫
      twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map
        (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g) := by
  change toCyclotomic D Sc cutoff i j v t
    (parityTransport D Sc cutoff 0 (D.parity i * D.parity j) i j v t
      (kernelSourceZeroEquiv D Sc cutoff i j v t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff j) ⋙ IndResKernel.homModule (k := k) (⟨v⟩ : OldCategory D Sc cutoff)) ⟨s⟩ g b))) = _
  rw [kernelSourceZeroEquiv_tensor, parityTransport_tensor, zero_add]
  change toCyclotomic D Sc cutoff i j v t
    (tensor D Sc cutoff i j v s t (oldTwist D Sc cutoff _ (s ++ [i]) t g) b) = _
  rw [toCyclotomic_tensor, pairing_eq_append_comp]
  have h := map_twist (R := k) (append D Sc cutoff j) (D.parity i * D.parity j)
    (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g
  rw [oldCategory_twist] at h
  exact congrArg (fun f :
      (append D Sc cutoff j).obj ((append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) ⟶
        (append D Sc cutoff j).obj (⟨t⟩ : OldCategory D Sc cutoff) =>
    (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
      (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫ crossComponent D Sc cutoff i j ⟨s⟩ ≫ f) h

private theorem kernelMateComponent_eq (i j : I) (hij : i ≠ j) (v t : List I) :
    kernelMateComponent D Sc cutoff i j ⟨v⟩ ⟨t⟩ =
      (kernelCrossingEquiv D Sc cutoff i j hij v t).toLinearMap := by
  apply BalancedInduction.hom_ext
  intro s g b
  rcases s with ⟨s⟩
  have hK := kernelMateComponent_tensor D Sc cutoff i j ⟨v⟩ ⟨s⟩ ⟨t⟩ g b
  have hE := kernelCrossingEquiv_tensor D Sc cutoff i j hij v s t g b
  exact hK.trans hE.symm

/-- Bijectivity of the literal ordinary-right kernel map follows from the
constructed PBW quotient decoder and source parity transport. -/
theorem kernelMateComponent_bijective (i j : I) (hij : i ≠ j) (v t : OldCategory D Sc cutoff) :
    Function.Bijective (kernelMateComponent D Sc cutoff i j v t) := by
  rcases v with ⟨v⟩
  rcases t with ⟨t⟩
  rw [kernelMateComponent_eq D Sc cutoff i j hij v t]
  exact (kernelCrossingEquiv D Sc cutoff i j hij v t).bijective

private def kernelNatTrans
    {C : Type u} [Category.{u} C] (K L : C ⥤ ModuleCat k)
    (f : ∀ v, K.obj v →ₗ[k] L.obj v)
    (hf : ∀ {v w} (a : v ⟶ w), (f w).comp (K.map a).hom = (L.map a).hom.comp (f v)) : K ⟶ L where
  app v := ModuleCat.ofHom (f v)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact hf a

/-- The literal mate as a natural transformation of ordinary-right kernels. -/
def kernelMate (i j : I) (t : OldCategory D Sc cutoff) :
    sourceKernel D Sc cutoff i j t ⟶ targetKernel D Sc cutoff i j t :=
  kernelNatTrans (sourceKernel D Sc cutoff i j t) (targetKernel D Sc cutoff i j t)
    (fun v => kernelMateComponent D Sc cutoff i j v.unop t)
    (fun {v w} r => kernelMateComponent_precompose D Sc cutoff i j w.unop v.unop t r.unop)

/-- Inverse naturality follows from the constructed component inverse. -/
def kernelMateIso (i j : I) (hij : i ≠ j) (t : OldCategory D Sc cutoff) :
    sourceKernel D Sc cutoff i j t ≅ targetKernel D Sc cutoff i j t :=
  BalancedKernelTensor.coefficientIso (kernelMate D Sc cutoff i j t)
    (fun v => kernelMateComponent_bijective D Sc cutoff i j hij v.unop t)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end

section

/-! # The prescribed distinct mate on arbitrary old modules

Brundan–Ellis (1.12), `DeformedActionAssembly.md` §4: tensor the ordinary-right
coefficient kernel isomorphism with the entire input module. The explicit
coend comparison identifies the resulting map with the fixed rectangular
cup-crossing-cap. No flatness or projectivity is required.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The fixed categorical mate with source and target coends exposed. -/
def moduleMateLinear (i j : I) (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) :=
  BalancedInduction.orderedMixedMateCoend (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) N t

@[simp] theorem moduleMateLinear_tensor (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : N.obj ((append D Sc cutoff j).obj s)) :
    moduleMateLinear D Sc cutoff i j N t
      (BalancedInduction.tensor (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj s)
        (crossComponent D Sc cutoff i j s ≫
          twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g)) b :=
  BalancedInduction.orderedMixedMateCoend_tensor (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) N s t g b

private theorem moduleMate_evaluate (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (v t : OldCategory D Sc cutoff)
    (m : N.obj v) :
    moduleMateLinear D Sc cutoff i j N t ∘ₗ
      MixedIndResKernel.evaluate (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor v t m =
      BalancedInduction.inclusion (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) v ∘ₗ
        (TensorProduct.mk k _ _).flip m ∘ₗ kernelMateComponent D Sc cutoff i j v t := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, MixedIndResKernel.evaluate_tensor,
    moduleMateLinear_tensor, kernelMateComponent_tensor, LinearMap.flip_apply,
    TensorProduct.mk_apply]
  change BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor
      ((append D Sc cutoff j).obj s) _ (N.map b m) =
    BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor v _ m
  exact (BalancedInduction.balance (append D Sc cutoff i) N.toFunctor b
    (crossComponent D Sc cutoff i j s ≫
      twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g)) m).symm

/-- Tensor the constructed ordinary-right kernel inverse with any old module. -/
def moduleMateUnderlyingEquiv (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) t ≃ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) :=
  (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t).symm |>.trans
    ((BalancedKernelTensor.equiv N.toFunctor (kernelMateIso D Sc cutoff i j hij t)).trans
      (BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) N.toFunctor
        ((append D Sc cutoff j).obj t)))

private theorem moduleMateUnderlyingEquiv_forward_tensor (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (v t : OldCategory D Sc cutoff)
    (x : MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) v t)
    (m : N.obj v) :
    moduleMateUnderlyingEquiv D Sc cutoff i j hij N t
      (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t
        (BalancedKernelTensor.tensor (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor v x m)) =
      BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor v
        (kernelMateComponent D Sc cutoff i j v t x) m := by
  change ((MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t).symm.trans
    ((BalancedKernelTensor.equiv N.toFunctor (kernelMateIso D Sc cutoff i j hij t)).trans
      (BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) N.toFunctor
        ((append D Sc cutoff j).obj t))))
    ((MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t)
      (BalancedKernelTensor.tensor (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor v x m)) = _
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
    BalancedKernelTensor.equiv_tensor, BalancedKernelTensor.inductionKernelEquiv_tensor]
  rfl

private theorem equiv_eq_on_kernel_tensors
    {C : Type u} [Category.{u} C] (K : Cᵒᵖ ⥤ ModuleCat k) (M : C ⥤ SVec k)
    {V W : Type u} [AddCommMonoid V] [Module k V] [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) (f : V →ₗ[k] W) (q : BalancedKernelTensor.Obj K M ≃ₗ[k] V)
    (h : ∀ v (x : K.obj (op v)) (m : M.obj v),
      e (q (BalancedKernelTensor.tensor K M v x m)) =
        f (q (BalancedKernelTensor.tensor K M v x m))) : e.toLinearMap = f := by
  apply LinearMap.cancel_right q.surjective |>.mp
  apply BalancedKernelTensor.hom_ext
  intro v x m
  exact h v x m

private theorem coend_left_apply
    {C B : Type u} [Category.{u} C] [Category.{u} B] [Preadditive B] [Linear k B]
    (J : C ⥤ B) (M : C ⥤ SVec k) (w : B) (v : C)
    {V : Type u} [AddCommMonoid V] [Module k V] (L : V →ₗ[k] (J.obj v ⟶ w))
    (m : M.obj v) (x : V) :
    (BalancedInduction.inclusion J M w v ∘ₗ (TensorProduct.mk k _ _).flip m ∘ₗ L) x =
      BalancedInduction.tensor J M v (L x) m := rfl

/-- The quotient-level inverse has exactly the prescribed categorical forward map. -/
theorem moduleMateUnderlyingEquiv_toLinearMap (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    (moduleMateUnderlyingEquiv D Sc cutoff i j hij N t).toLinearMap =
      moduleMateLinear D Sc cutoff i j N t := by
  apply equiv_eq_on_kernel_tensors (k := k)
    (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor
    (moduleMateUnderlyingEquiv D Sc cutoff i j hij N t) (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t)
  intro v x m
  have hL := moduleMateUnderlyingEquiv_forward_tensor D Sc cutoff i j hij N v t x m
  have hF := congrArg (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.equiv_tensor (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t v x m)
  have hA := LinearMap.congr_fun (moduleMate_evaluate D Sc cutoff i j N v t m) x
  have hA0 := (LinearMap.comp_apply (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.evaluate (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor v t m) x).symm.trans hA
  have hA1 := hA0.trans (coend_left_apply (k := k) (append D Sc cutoff i) N.toFunctor
    ((append D Sc cutoff j).obj t) v (kernelMateComponent D Sc cutoff i j v t) m x)
  exact hL.trans (hF.trans hA1).symm

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
end

end
