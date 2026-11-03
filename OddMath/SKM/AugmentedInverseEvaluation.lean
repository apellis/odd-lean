import OddMath.SKM.RouquierReflectedLocal
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # Evaluation of homogeneous augmented inverses

Brundan–Ellis (1.13)–(1.14): evaluate all five finite matrix identities
of a whole supernatural inverse at an input object. The forward principal
map is its prescribed homogeneous component; every inverse entry is its
total component, including entries outside the finite window.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory
universe r u v u' v'
variable {k : Type r} [CommRing k]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Supercategory k C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D] [Supercategory k D]

/-- Total evaluation retains arbitrary supernatural components. -/
def superfunctorTotalEvaluation (N : C) : Superfunctor k C D ⥤ D where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

instance superfunctorTotalEvaluation_additive (N : C) :
    (superfunctorTotalEvaluation (k := k) (D := D) N).Additive where
  map_add := by intros; change (_ + _) + (_ + _) = (_ + _) + (_ + _); abel

instance superfunctorTotalEvaluation_linear (N : C) :
    (superfunctorTotalEvaluation (k := k) (D := D) N).Linear k where
  map_smul := by intros; change _ • _ + _ • _ = _ • (_ + _); rw [smul_add]

instance superfunctorTotalEvaluation_super (N : C) :
    IsSuperfunctor k (superfunctorTotalEvaluation (k := k) (D := D) N) where
  map_mem := by
    intro F G p f hf
    change f.total N ∈ parity (R := k) _ _ p
    rw [HomogeneousSuperfunctorIso.total_eq_app f hf N]
    exact f.app_mem p N

section Inverses
variable {A B Z : Superfunctor k C D} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

private def SuperSumInvTo.atTotal {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) (N : C) :
    SuperSumInvTo (k := k) (f.total N) (fun m => (g m).total N) p q n where
  f' := J.f'.total N
  g' m := (J.g' m).total N
  f_mem := map_mem (superfunctorTotalEvaluation N) J.f_mem
  g_mem m := map_mem (superfunctorTotalEvaluation N) (J.g_mem m)
  f'_mem := map_mem (superfunctorTotalEvaluation N) J.f'_mem
  g'_mem m := map_mem (superfunctorTotalEvaluation N) (J.g'_mem m)
  total := by
    have h := congrArg (superfunctorTotalEvaluation N).map J.total
    rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id] at h
    simp only [CategoryTheory.Functor.map_comp] at h
    exact h
  ff := by
    have h := congrArg (superfunctorTotalEvaluation N).map J.ff
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h
  fg m hm := by
    have h := congrArg (superfunctorTotalEvaluation N).map (J.fg m hm)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
    exact h
  gf m hm := by
    have h := congrArg (superfunctorTotalEvaluation N).map (J.gf m hm)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
    exact h
  gg m l hm hl := by
    have h := congrArg (superfunctorTotalEvaluation N).map (J.gg m l hm hl)
    split_ifs at h ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
      exact h
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
      exact h

private def SuperSumInvFrom.atTotal {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) (N : C) :
    SuperSumInvFrom (k := k) (f.total N) (fun m => (g m).total N) p q n where
  f' := J.f'.total N
  g' m := (J.g' m).total N
  f_mem := map_mem (superfunctorTotalEvaluation N) J.f_mem
  g_mem m := map_mem (superfunctorTotalEvaluation N) (J.g_mem m)
  f'_mem := map_mem (superfunctorTotalEvaluation N) J.f'_mem
  g'_mem m := map_mem (superfunctorTotalEvaluation N) (J.g'_mem m)
  total := by
    have h := congrArg (superfunctorTotalEvaluation N).map J.total
    rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id] at h
    simp only [CategoryTheory.Functor.map_comp] at h
    exact h
  ff := by
    have h := congrArg (superfunctorTotalEvaluation N).map J.ff
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact h
  fg m hm := by
    have h := congrArg (superfunctorTotalEvaluation N).map (J.fg m hm)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
    exact h
  gf m hm := by
    have h := congrArg (superfunctorTotalEvaluation N).map (J.gf m hm)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
    exact h
  gg m l hm hl := by
    have h := congrArg (superfunctorTotalEvaluation N).map (J.gg m l hm hl)
    split_ifs at h ⊢
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
      exact h
    · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
      exact h

/-- Evaluate the row inverse with its homogeneous forward principal map. -/
def SuperSumInvTo.at {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) (N : C) :
    SuperSumInvTo (k := k) (f.app p N) (fun m => (g m).total N) p q n :=
  (J.atTotal N).copyMaps (f.app p N) (fun m => (g m).total N)
    (HomogeneousSuperfunctorIso.total_eq_app f J.f_mem N).symm rfl

/-- Evaluate the column inverse with its homogeneous forward principal map. -/
def SuperSumInvFrom.at {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) (N : C) :
    SuperSumInvFrom (k := k) (f.app p N) (fun m => (g m).total N) p q n :=
  (J.atTotal N).copyMaps (f.app p N) (fun m => (g m).total N)
    (HomogeneousSuperfunctorIso.total_eq_app f J.f_mem N).symm rfl

@[simp] theorem SuperSumInvTo.at_f' {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) (N : C) : (J.at N).f' = J.f'.total N := rfl
@[simp] theorem SuperSumInvTo.at_g' {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) (N : C) (m : ℕ) :
    (J.at N).g' m = (J.g' m).total N := rfl
@[simp] theorem SuperSumInvFrom.at_f' {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) (N : C) : (J.at N).f' = J.f'.total N := rfl
@[simp] theorem SuperSumInvFrom.at_g' {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) (N : C) (m : ℕ) :
    (J.at N).g' m = (J.g' m).total N := rfl
end Inverses
end OddMath.SKM
