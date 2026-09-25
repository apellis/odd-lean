import OddMath.Frontier.TableauStripBijection
import OddMath.Frontier.TableauStripSigns
import OddMath.Frontier.DegreeShapes
import OddMath.Frontier.TableauPolynomial
import OddMath.Frontier.FiniteCompleteElementary

/-! Ellis 1111.3932v1, Prop. 3.7 (3.8), in the raw tableau normalization.
Finite reindexing uses the genuine full-state insertion equivalence.
No complete-product expansion, kernel, Schur comparison or LR claim. -/
namespace OddMath.Frontier.TableauHorizontalPieri
open scoped BigOperators
open TableauStripSigns TableauStripBijection TableauStripCorners
open TableauSign TableauEvaluation TableauPolynomial DegreeShapes
open FiniteCompleteElementary PlacticEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable

def shapeExponent (μ : YoungDiagram) : ℕ := directNorth μ + north μ + northEast μ
def stripCount (μ ν : YoungDiagram) : ℕ := ∑ p ∈ ν.cells \ μ.cells, rightCount μ p.2
abbrev Tab (n : ℕ) (μ : YoungDiagram) := {T : PositiveTableau μ // InAlphabet n T}
abbrev Weak (n k : ℕ) := FiniteWords.Weak n k

instance tabFinite (n : ℕ) (μ : YoungDiagram) : Fintype (Tab n μ) :=
  (finite_inAlphabet n μ).fintype

def inputMap (n : ℕ) (μ : YoungDiagram) (k : ℕ) (x : Tab n μ × Weak n k) :
    Inputs n μ k :=
  ⟨(⟨μ,x.1⟩, List.ofFn x.2.val), rfl, x.2.property.ofFn_sorted, List.length_ofFn⟩

theorem inputMap_bijective (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    Function.Bijective (inputMap n μ k) := by
  constructor
  · intro x y h
    have hs := congrArg (fun z : Inputs n μ k => z.val.1) h
    have hw := congrArg (fun z : Inputs n μ k => z.val.2) h
    apply Prod.ext
    · exact eq_of_heq (Sigma.mk.inj hs).2
    · exact Subtype.ext (List.ofFn_injective hw)
  · rintro ⟨⟨⟨ν,T⟩,w⟩,hμ,hw,hk⟩
    dsimp only at hμ hk hw
    subst ν
    subst k
    let f : Weak n w.length := ⟨w.get, by
      apply List.sorted_le_ofFn_iff.mp
      simpa only [List.ofFn_get] using hw⟩
    refine ⟨(T,f), Subtype.ext ?_⟩
    change ((⟨μ,T⟩ : TableauWordInsertion.State n),List.ofFn w.get) = _
    rw [List.ofFn_get]

def inputEquiv (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    Tab n μ × Weak n k ≃ Inputs n μ k :=
  Equiv.ofBijective (inputMap n μ k) (inputMap_bijective n μ k)

abbrev Outer (μ : YoungDiagram) (k : ℕ) :=
  {ν : DegreeShape (μ.card + k) // Horizontal μ ν.val}
abbrev Indexed (n : ℕ) (μ : YoungDiagram) (k : ℕ) := Σ ν : Outer μ k, Tab n ν.val.val

def outputMap (n : ℕ) (μ : YoungDiagram) (k : ℕ) (y : Indexed n μ k) :
    Outputs n μ k :=
  ⟨⟨y.1.val.val,y.2⟩, y.1.property, by
    rw [Finset.card_sdiff y.1.property.1]
    change y.1.val.val.card - μ.card = k
    rw [y.1.val.property]; omega⟩

theorem outputMap_bijective (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    Function.Bijective (outputMap n μ k) := by
  constructor
  · rintro ⟨⟨⟨ν,hd⟩,hh⟩,T⟩ ⟨⟨⟨ν',hd'⟩,hh'⟩,T'⟩ h
    have he := congrArg Subtype.val h
    have hs := congrArg Sigma.fst he
    dsimp only [outputMap] at hs
    subst ν'
    have ht : T = T' := eq_of_heq (Sigma.mk.inj he).2
    subst T'
    rfl
  · rintro ⟨⟨ν,T⟩,hh,hk⟩
    change (ν.cells \ μ.cells).card = k at hk
    have hd : ν.card = μ.card + k := by
      have hc := Finset.card_sdiff_add_card_eq_card hh.1
      change (ν.cells \ μ.cells).card + μ.card = ν.card at hc
      omega
    exact ⟨⟨⟨⟨ν,hd⟩,hh⟩,T⟩,rfl⟩

def outputEquiv (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    Indexed n μ k ≃ Outputs n μ k :=
  Equiv.ofBijective (outputMap n μ k) (outputMap_bijective n μ k)

def aggregateEquiv (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    Tab n μ × Weak n k ≃ Indexed n μ k :=
  (inputEquiv n μ k).trans ((insertionEquiv n μ k).trans (outputEquiv n μ k).symm)

theorem run_stripCount (n : ℕ) (S : TableauWordInsertion.State n) (w : List (Fin n)) :
    stripRight S.1 (TableauWordInsertion.run n S w).2 =
      stripCount S.1 (TableauWordInsertion.run n S w).1.1 := by
  have hs := TableauWordInsertion.run_spec n S w
  unfold stripRight stripCount
  rw [← hs.2.2.2, List.sum_toFinset _ hs.2.1]

def inputValue (n : ℕ) (μ : YoungDiagram) (k : ℕ) (x : Tab n μ × Weak n k) :=
  (-1 : ℤ) ^ shapeExponent μ •
    (rowPolynomial n x.1.val x.1.property * toSkew n (OddPlactic.word n (List.ofFn x.2.val)))
def outputValue (n : ℕ) (μ : YoungDiagram) (S : TableauWordInsertion.State n) :=
  (-1 : ℤ) ^ (shapeExponent S.1 + stripCount μ S.1) •
    rowPolynomial n S.2.val S.2.property

theorem pointwise (n : ℕ) (μ : YoungDiagram) (k : ℕ) (x : Tab n μ × Weak n k) :
    inputValue n μ k x =
      outputValue n μ (outputMap n μ k (aggregateEquiv n μ k x)).val := by
  have he : outputMap n μ k (aggregateEquiv n μ k x) =
      insertionEquiv n μ k (inputMap n μ k x) :=
    (outputEquiv n μ k).apply_symm_apply _
  rw [he, insertionEquiv_apply]
  have h := run_polynomial n ⟨μ,x.1⟩ (List.ofFn x.2.val) x.2.property.ofFn_sorted
  dsimp only at h
  rw [run_stripCount n ⟨μ,x.1⟩ (List.ofFn x.2.val)] at h
  exact h

theorem tableau_sum (n : ℕ) (μ : YoungDiagram) :
    tableauPolynomial n μ = ∑ T : Tab n μ, rowPolynomial n T.val T.property := by
  classical
  unfold tableauPolynomial
  apply Fintype.sum_equiv
    (show {T // T ∈ tableauxInAlphabet n μ} ≃ Tab n μ from
      Equiv.subtypeEquivRight (fun T => mem_tableauxInAlphabet n T))
  intro T
  rfl

theorem complete_sum (n k : ℕ) :
    completePoly n k = ∑ w : Weak n k, toSkew n (OddPlactic.word n (List.ofFn w.val)) := by
  classical
  rw [show completePoly n k = FiniteWords.weakSum (tildeGenerator (n := n)) k from
    (FiniteWords.weakSum_eq _ _).symm]
  simp only [FiniteWords.weakSum, FiniteWords.word, toSkew_word, List.map_ofFn, Function.comp_def]

theorem input_sum (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    (-1 : ℤ) ^ shapeExponent μ • (tableauPolynomial n μ * completePoly n k) =
      ∑ x : Tab n μ × Weak n k, inputValue n μ k x := by
  classical
  rw [tableau_sum, complete_sum, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, inputValue]
  exact Finset.sum_comm

theorem output_sum (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (μ.card + k)
    ∑ y : Indexed n μ k, outputValue n μ (outputMap n μ k y).val =
      ∑ ν : DegreeShape (μ.card + k), if Horizontal μ ν.val then
        (-1 : ℤ) ^ (shapeExponent ν.val + stripCount μ ν.val) • tableauPolynomial n ν.val
      else 0 := by
  classical
  letI := degreeFintype (μ.card + k)
  rw [Fintype.sum_sigma]
  simp only [outputValue, outputMap]
  simp_rw [← Finset.smul_sum, ← tableau_sum]
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype _ (by simp) _

/-- Source-matched h-right horizontal Pieri on the literal all-degree family. -/
theorem horizontal_pieri (n : ℕ) (μ : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (μ.card + k)
    (-1 : ℤ) ^ shapeExponent μ • (tableauPolynomial n μ * completePoly n k) =
      ∑ ν : DegreeShape (μ.card + k), if Horizontal μ ν.val then
        (-1 : ℤ) ^ (shapeExponent ν.val + stripCount μ ν.val) • tableauPolynomial n ν.val
      else 0 := by
  classical
  letI := degreeFintype (μ.card + k)
  rw [input_sum, ← output_sum]
  exact Fintype.sum_equiv (aggregateEquiv n μ k) _ _ (pointwise n μ k)

end
end OddMath.Frontier.TableauHorizontalPieri
