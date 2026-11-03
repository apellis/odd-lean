import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairDotComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTriplePairComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData

/-! # Components of the three prescribed weight dot positions

Brundan--Ellis (1.9), the repeated-outer correction. Retain the literal
three dot whiskerings and their selected predecessor-dispatch maps,
including full coefficient parity and arbitrary input modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem dot_total_whiskerRight
    {k : Type u} [CommRing k]
    {A B C : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (H : B ⟶ C) (M : A) :
    (f ▷ H).total M = H.map (f.total M) := by
  change H.map (f.app 0 M) + H.map (f.app 1 M) = H.map (f.app 0 M + f.app 1 M)
  exact H.toFunctor.map_add.symm
private theorem dot_first_total
    {k : Type u} [CommRing k]
    {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : End F) (M : A) :
    (x ▷ (G ≫ H)).total M = H.map ((x ▷ G).total M) := by
  rw [dot_total_whiskerRight, dot_total_whiskerRight]
  rfl
private theorem dot_middle_total
    {k : Type u} [CommRing k]
    {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : End G) (M : A) :
    (F ◁ (x ▷ H)).total M = H.map ((F ◁ x).total M) := by
  change (x ▷ H).total (F.obj M) = H.map (x.total (F.obj M))
  exact dot_total_whiskerRight x H (F.obj M)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b c d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
local notation "E₁" => elvE D Sc cutoff bound l Λ hal
local notation "E₂" => elvE D Sc cutoff bound j Λ hbj
local notation "E₃" => elvE D Sc cutoff bound i Λ hci

/-- The first literal dot position, whiskered by both following inductions. -/
abbrev elvWeightTripleFirstDot : End (E₁ ≫ E₂ ≫ E₃) :=
  elvActionDot D Sc cutoff bound l Λ hal ▷ (E₂ ≫ E₃)
/-- The middle literal dot position. -/
abbrev elvWeightTripleMiddleDot : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ (elvActionDot D Sc cutoff bound j Λ hbj ▷ E₃)
/-- The last literal dot position. -/
abbrev elvWeightTripleLastDot : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ E₂ ◁ elvActionDot D Sc cutoff bound i Λ hci

/-- The first literal dot is induced from its first-pair component. -/
theorem elvWeightTripleFirstDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M ε =
      (elvInductionComponent D Sc cutoff bound i Λ hci ε).map
        ((elvActionDot D Sc cutoff bound l Λ hal ▷ E₂).total M) :=
  congrFun (dot_first_total E₁ E₂ E₃ (elvActionDot D Sc cutoff bound l Λ hal) M) ε

/-- The middle literal dot is induced from its last first-pair component. -/
theorem elvWeightTripleMiddleDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M ε =
      (elvInductionComponent D Sc cutoff bound i Λ hci ε).map
        ((E₁ ◁ elvActionDot D Sc cutoff bound j Λ hbj).total M) :=
  congrFun (dot_middle_total E₁ E₂ E₃ (elvActionDot D Sc cutoff bound j Λ hbj) M) ε

/-- The last literal dot acts on the actual twice-induced product. -/
theorem elvWeightTripleLastDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M ε =
      elvWeightDotComponent D Sc cutoff bound i Λ hci (D.parity i)
        ((elvEFunctor D Sc cutoff bound j Λ hbj).obj
          ((elvEFunctor D Sc cutoff bound l Λ hal).obj M)) ε :=
  congrFun (supernatural_total_of_mem
    (elvActionDot_mem D Sc cutoff bound i Λ hci) ((E₂).obj ((E₁).obj M))) ε

private theorem pairFirstDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (δ : WeightBlocks D Λ c) :
    (elvActionDot D Sc cutoff bound l Λ hal ▷ E₂).total M δ =
      (elvInductionComponent D Sc cutoff bound j Λ hbj δ).map
        ((elvWeightDot D Sc cutoff bound l Λ hal).app (D.parity l) M) := by
  have h := congrFun (dot_total_whiskerRight (elvActionDot D Sc cutoff bound l Λ hal) E₂ M) δ
  rw [supernatural_total_of_mem (elvActionDot_mem D Sc cutoff bound l Λ hal) M] at h
  exact h
private theorem pairMiddleDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (δ : WeightBlocks D Λ c) :
    (E₁ ◁ elvActionDot D Sc cutoff bound j Λ hbj).total M δ =
      elvWeightDotComponent D Sc cutoff bound j Λ hbj (D.parity j)
        ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) δ :=
  congrFun (supernatural_total_of_mem (elvActionDot_mem D Sc cutoff bound j Λ hbj) ((E₁).obj M)) δ

section Supported
variable (β : WeightBlocks D Λ a)
local notation "β₂" => blockSucc₂ D j l Λ hal hbj β
local notation "β₃" => elvBlockSucc₃ D i j l Λ hal hbj hci β
local notation "U" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound i Λ hci β₂)
local notation "ds" => eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ hal hbj hci β)

/-- The supported first dot retains the outer dispatch and the independently
specified first-pair dot used by the selected pair comparison. -/
theorem elvWeightTripleFirstDot_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ =
      (ds).hom.app M ≫
        (U).map ((elvInductionComponent D Sc cutoff bound j Λ hbj β₂).map
          ((elvWeightDot D Sc cutoff bound l Λ hal).app (D.parity l) M)) ≫ (ds).inv.app M := by
  have h₀ := elvWeightTripleFirstDot_total D Sc cutoff bound i j l Λ hal hbj hci M β₃
  have hm := elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ hci β₂
    ((elvActionDot D Sc cutoff bound l Λ hal ▷ E₂).total M)
  have hx := pairFirstDot_total D Sc cutoff bound j l Λ hal hbj M β₂
  have hr := congrArg
    (fun (f : End ((E₁ ≫ E₂).obj M β₂)) =>
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ hci β₂).map f ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)).symm) hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app]
  exact h₀.trans (hm.trans hr)

/-- The supported middle dot retains the same outer dispatch and the
independently specified outer dot of the first pair. -/
theorem elvWeightTripleMiddleDot_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ =
      (ds).hom.app M ≫
        (U).map (elvWeightDotComponent D Sc cutoff bound j Λ hbj (D.parity j)
          ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) β₂) ≫ (ds).inv.app M := by
  have h₀ := elvWeightTripleMiddleDot_total D Sc cutoff bound i j l Λ hal hbj hci M β₃
  have hm := elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ hci β₂
    ((E₁ ◁ elvActionDot D Sc cutoff bound j Λ hbj).total M)
  have hx := pairMiddleDot_total D Sc cutoff bound j l Λ hal hbj M β₂
  have hr := congrArg
    (fun (f : End ((E₁ ≫ E₂).obj M β₂)) =>
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ hci β₂).map f ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)).symm) hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app]
  exact h₀.trans (hm.trans hr)

/-- The supported last dot retains the prescribed single-letter content dot
on the actual twice-induced input, with both dispatch directions. -/
theorem elvWeightTripleLastDot_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ =
      (ds).hom.app M ≫
        (elvBlockDot D Sc cutoff bound i Λ hci β₂).app (D.parity i)
          ((E₁ ≫ E₂).obj M β₂) ≫ (ds).inv.app M := by
  have h₀ := elvWeightTripleLastDot_total D Sc cutoff bound i j l Λ hal hbj hci M β₃
  have hd := elvWeightDotComponent_blockSucc D Sc cutoff bound i Λ hci (D.parity i)
    ((E₁ ≫ E₂).obj M) β₂
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app]
  exact h₀.trans hd
end Supported
end OddMath.QuiverHecke.ELVOld
