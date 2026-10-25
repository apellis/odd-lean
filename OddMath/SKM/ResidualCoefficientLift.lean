import OddMath.SKM.MatchingChoiceTransition
import OddMath.SKM.MatchingCoefficientPlacement

/-! Finite residual lifts at the fixed global weight.
The zero-index column is prescribed formally, not recognized by equality
of evaluated morphisms. No coefficient independence is assumed. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace MatchingBasisChoice
variable (cs : CScalars Sc) (μ : X) {a b : List (Letter I)}
variable (F : MatchingBasisChoice a b)

/-- Choose each residual unit column once. Negative indices are zero and
index zero is the literal original label. Positive indices use only spanning. -/
def residualUnitColumn
    (R : ℤ → F.Labels → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (n : ℤ) (t : F.Labels) : F.Labels →₀ SYM D k :=
  if n < 0 then 0 else if n = 0 then Finsupp.single t 1
  else (F.expansion_surjective cs μ (R n t)).choose

@[simp] theorem residualUnitColumn_zero
    (R : ℤ → F.Labels → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (t : F.Labels) : F.residualUnitColumn cs μ R 0 t = Finsupp.single t 1 := by
  simp [residualUnitColumn]

theorem residualUnitColumn_neg
    (R : ℤ → F.Labels → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (n : ℤ) (hn : n < 0) (t : F.Labels) : F.residualUnitColumn cs μ R n t = 0 := by
  simp only [residualUnitColumn, ite_eq_left hn]

theorem residualUnitColumn_eval
    (R : ℤ → F.Labels → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (hneg : ∀ n, n < 0 → ∀ t, R n t = 0)
    (hzero : ∀ t, R 0 t = xev cs μ a b (F.layers t)) (n : ℤ) (t : F.Labels) :
    F.expansion cs μ (F.residualUnitColumn cs μ R n t) = R n t := by
  by_cases hn : n < 0
  · rw [F.residualUnitColumn_neg cs μ R n hn t, map_zero, hneg n hn t]
  · by_cases hz : n = 0
    · subst n
      rw [F.residualUnitColumn_zero, F.expansion_single, hzero]
      exact rightAction_one cs μ _
    · simp only [residualUnitColumn, ite_eq_right hn, ite_eq_right hz]
      exact (F.expansion_surjective cs μ (R n t)).choose_spec

/-- Extend the fixed unit column linearly in the input coefficient, optionally
using a prescribed full-SYM parity twist. No new choice depends on that input. -/
def residualCoefficientColumn
    (R : ℤ → F.Labels → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (n : ℤ) (t : F.Labels) (q : ZMod 2) : SYM D k →ₗ[k] (F.Labels →₀ SYM D k) :=
  (MatchingTransition.rightColumn (k := k) (F.residualUnitColumn cs μ R n t)).comp
    (SYM.parityTwist D k q)

theorem residualCoefficientColumn_eval
    (R : ℤ → F.Labels → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (hneg : ∀ n, n < 0 → ∀ t, R n t = 0)
    (hzero : ∀ t, R 0 t = xev cs μ a b (F.layers t))
    (n : ℤ) (t : F.Labels) (q : ZMod 2) (p : SYM D k) :
    F.expansion cs μ (F.residualCoefficientColumn cs μ R n t q p) =
      rightAction cs μ (R n t) (SYM.parityTwist D k q p) := by
  change F.expansion cs μ (MatchingTransition.rightColumn (k := k)
    (F.residualUnitColumn cs μ R n t) (SYM.parityTwist D k q p)) = _
  rw [F.expansion_rightColumn, F.residualUnitColumn_eval cs μ R hneg hzero]

@[simp] theorem residualCoefficientColumn_zero
    (R : ℤ → F.Labels → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)))
    (t : F.Labels) (q : ZMod 2) (p : SYM D k) :
    F.residualCoefficientColumn cs μ R 0 t q p =
      Finsupp.single t (SYM.parityTwist D k q p) := by
  simp [residualCoefficientColumn, LinearMap.comp_apply]

/-- Actual postcomposition by residual loops, still evaluated at the fixed
global external weight. No unwhiskered bubble formula is substituted. -/
theorem residualPostColumn_eval
    (q : ℤ → End ((pres D Sc).obj (ob D μ b)))
    (hqneg : ∀ n, n < 0 → q n = 0) (hqzero : q 0 = 𝟙 _)
    (n : ℤ) (t : F.Labels) (ε : ZMod 2) (p : SYM D k) :
    F.expansion cs μ (F.residualCoefficientColumn cs μ
      (fun n t => xev cs μ a b (F.layers t) ≫ q n) n t ε p) =
      rightAction cs μ (xev cs μ a b (F.layers t) ≫ q n)
        (SYM.parityTwist D k ε p) := by
  apply F.residualCoefficientColumn_eval
  · intro n hn t
    rw [hqneg n hn, Limits.comp_zero]
  · intro t
    rw [hqzero, Category.comp_id]

/-- Actual precomposition by residual loops, with the same global weight
and no independence hypothesis on the residual family. -/
theorem residualPreColumn_eval
    (q : ℤ → End ((pres D Sc).obj (ob D μ a)))
    (hqneg : ∀ n, n < 0 → q n = 0) (hqzero : q 0 = 𝟙 _)
    (n : ℤ) (t : F.Labels) (ε : ZMod 2) (p : SYM D k) :
    F.expansion cs μ (F.residualCoefficientColumn cs μ
      (fun n t => q n ≫ xev cs μ a b (F.layers t)) n t ε p) =
      rightAction cs μ (q n ≫ xev cs μ a b (F.layers t))
        (SYM.parityTwist D k ε p) := by
  apply F.residualCoefficientColumn_eval
  · intro n hn t
    rw [hqneg n hn, Limits.zero_comp]
  · intro t
    rw [hqzero, Category.id_comp]

/-- Insert a finite residual coefficient vector at one isolated-strand row. -/
def residualRow (m : ℕ) :
    (F.Labels →₀ SYM D k) →ₗ[k] ((F.Labels × ℕ) →₀ SYM D k) :=
  Finsupp.lmapDomain (SYM D k) k (fun t => (t, m))

@[simp] theorem residualRow_single (m : ℕ) (t : F.Labels) (p : SYM D k) :
    F.residualRow (D := D) (k := k) m (Finsupp.single t p) = Finsupp.single (t, m) p := by
  simp [residualRow]

/-- Expanding a residual morphism cannot change the isolated strand's row. -/
theorem residualRow_apply_ne (m n : ℕ) (hn : n ≠ m) (v : F.Labels →₀ SYM D k)
    (t : F.Labels) : F.residualRow (D := D) (k := k) m v (t, n) = 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw, add_zero]
  | single s p =>
    rw [F.residualRow_single, Finsupp.single_eq_of_ne]
    exact fun h => hn (congrArg Prod.snd h)

variable {c : List (Letter I)}

/-- Literal postcomposition of residual representatives with isolated cups. -/
def postRowsCoefficientMap (G : MatchingBasisChoice a c)
    (H : ℕ → ((pres D Sc).obj (ob D μ c) ⟶ (pres D Sc).obj (ob D μ b)))
    (t : G.Labels × ℕ) : SYM D k →ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) where
  toFun p := bubAt D Sc μ a (betaSYM cs μ p) ≫ xev cs μ a c (G.layers t.1) ≫ H t.2
  map_add' p q := by simp only [map_add, Preadditive.add_comp]
  map_smul' r p := by simp only [map_smul, Linear.smul_comp, RingHom.id_apply]

def postRowsExpansion (G : MatchingBasisChoice a c)
    (H : ℕ → ((pres D Sc).obj (ob D μ c) ⟶ (pres D Sc).obj (ob D μ b))) :
    ((G.Labels × ℕ) →₀ SYM D k) →ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Finsupp.lsum k (G.postRowsCoefficientMap cs μ H)

@[simp] theorem postRowsExpansion_single (G : MatchingBasisChoice a c)
    (H : ℕ → ((pres D Sc).obj (ob D μ c) ⟶ (pres D Sc).obj (ob D μ b)))
    (t : G.Labels) (m : ℕ) (p : SYM D k) :
    G.postRowsExpansion cs μ H (Finsupp.single (t, m) p) =
      bubAt D Sc μ a (betaSYM cs μ p) ≫ xev cs μ a c (G.layers t) ≫ H m :=
  Finsupp.lsum_single k _ _ _

theorem postRowsExpansion_residualRow (G : MatchingBasisChoice a c)
    (H : ℕ → ((pres D Sc).obj (ob D μ c) ⟶ (pres D Sc).obj (ob D μ b)))
    (m : ℕ) (v : G.Labels →₀ SYM D k) :
    G.postRowsExpansion cs μ H (G.residualRow m v) = G.expansion cs μ v ≫ H m := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, Preadditive.add_comp]
  | single t p =>
    rw [G.residualRow_single, G.postRowsExpansion_single, G.expansion_single, Category.assoc]

/-- Literal precomposition of residual representatives with isolated caps. -/
def preRowsCoefficientMap (G : MatchingBasisChoice c b)
    (E : ℕ → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ c)))
    (t : G.Labels × ℕ) : SYM D k →ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) where
  toFun p := bubAt D Sc μ a (betaSYM cs μ p) ≫ E t.2 ≫ xev cs μ c b (G.layers t.1)
  map_add' p q := by simp only [map_add, Preadditive.add_comp]
  map_smul' r p := by simp only [map_smul, Linear.smul_comp, RingHom.id_apply]

def preRowsExpansion (G : MatchingBasisChoice c b)
    (E : ℕ → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ c))) :
    ((G.Labels × ℕ) →₀ SYM D k) →ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Finsupp.lsum k (G.preRowsCoefficientMap cs μ E)

@[simp] theorem preRowsExpansion_single (G : MatchingBasisChoice c b)
    (E : ℕ → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ c)))
    (t : G.Labels) (m : ℕ) (p : SYM D k) :
    G.preRowsExpansion cs μ E (Finsupp.single (t, m) p) =
      bubAt D Sc μ a (betaSYM cs μ p) ≫ E m ≫ xev cs μ c b (G.layers t) :=
  Finsupp.lsum_single k _ _ _

/-- Source-side insertion twists each residual coefficient by the cap's
parity. This is separate from any twist of the original input coefficient. -/
theorem preRowsExpansion_residualRow (G : MatchingBasisChoice c b)
    (E : ℕ → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ c)))
    (m : ℕ) (q : ZMod 2) (hE : E m ∈ homPar D Sc μ a c q)
    (v : G.Labels →₀ SYM D k) :
    G.preRowsExpansion cs μ E (G.residualRow m (labelParityTwist (fun _ => q) v)) =
      E m ≫ G.expansion cs μ v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw, Preadditive.comp_add]
  | single t p =>
    rw [labelParityTwist_single, G.residualRow_single, G.preRowsExpansion_single,
      G.expansion_single, ← Category.assoc, source_target_twist cs μ hE p, Category.assoc]

theorem postRowsExpansion_rightColumn (G : MatchingBasisChoice a c)
    (H : ℕ → ((pres D Sc).obj (ob D μ c) ⟶ (pres D Sc).obj (ob D μ b)))
    (v : (G.Labels × ℕ) →₀ SYM D k) (p : SYM D k) :
    G.postRowsExpansion cs μ H (MatchingTransition.rightColumn (k := k) v p) =
      rightAction cs μ (G.postRowsExpansion cs μ H v) p := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [rightAction]
  | add v w hv hw =>
    rw [MatchingTransition.rightColumn_add, map_add, hv, hw, map_add]
    simp only [rightAction, Preadditive.comp_add]
  | single t d =>
    rcases t with ⟨t, m⟩
    rw [MatchingTransition.rightColumn_single, G.postRowsExpansion_single,
      G.postRowsExpansion_single]
    exact (rightAction_mul cs μ (xev cs μ a c (G.layers t) ≫ H m) d p).symm

theorem preRowsExpansion_rightColumn (G : MatchingBasisChoice c b)
    (E : ℕ → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ c)))
    (v : (G.Labels × ℕ) →₀ SYM D k) (p : SYM D k) :
    G.preRowsExpansion cs μ E (MatchingTransition.rightColumn (k := k) v p) =
      rightAction cs μ (G.preRowsExpansion cs μ E v) p := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp [rightAction]
  | add v w hv hw =>
    rw [MatchingTransition.rightColumn_add, map_add, hv, hw, map_add]
    simp only [rightAction, Preadditive.comp_add]
  | single t d =>
    rcases t with ⟨t, m⟩
    rw [MatchingTransition.rightColumn_single, G.preRowsExpansion_single,
      G.preRowsExpansion_single]
    exact (rightAction_mul cs μ (E m ≫ xev cs μ c b (G.layers t)) d p).symm

/-- The source column has two separate parity operations: the cap twists
the residual entries, and the comparison component twists the input. -/
theorem preRowsExpansion_twistedColumn (G : MatchingBasisChoice c b)
    (E : ℕ → ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ c)))
    (m : ℕ) (q : ZMod 2) (hE : E m ∈ homPar D Sc μ a c q)
    (v : G.Labels →₀ SYM D k) (ε : ZMod 2) (p : SYM D k) :
    G.preRowsExpansion cs μ E (MatchingTransition.rightColumn (k := k)
      (G.residualRow m (labelParityTwist (fun _ => q) v)) (SYM.parityTwist D k ε p)) =
      rightAction cs μ (E m ≫ G.expansion cs μ v) (SYM.parityTwist D k ε p) := by
  rw [G.preRowsExpansion_rightColumn, G.preRowsExpansion_residualRow cs μ E m q hE]

end MatchingBasisChoice
end OddMath.SKM
