import OddMath.QuiverHecke.ReservoirWeightParameters
import OddMath.SKM.MoreGenerators
import StringDiagrams.LayerMap.Generators
import StringDiagrams.Biadjunction.Zigzag

/-! # The SKM presentation map into the pairing extension

Brundan–Ellis Definition 1.5 and (2.6), as used in
`SwappedNondegeneracy.md` §2: embed each original region as `(μ,0)`.
Every signed strand, generator, inverse-entry label, height window and
supplied scalar is retained. The resulting presentation functor is the
pullback map needed for the combined swapped action; it is not a claim
that restricting either cyclotomic factor separately retains its vacuum.
-/
noncomputable section
namespace OddMath.SKM.PairingExtension
open CategoryTheory StringDiagrams OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
local notation "Dₑ" => ReservoirWeights.pairingExtension D

@[simp] theorem height (i : I) (μ : X) : (Dₑ).h i (μ, 0) = D.h i μ := by simp

@[simp] theorem shift (l : Letter I) : sh Dₑ l = (sh D l, 0) := by
  unfold sh
  split_ifs <;> rfl

@[simp] theorem weight (μ : X) (t : List (Letter I)) : wt Dₑ (μ, 0) t = (wt D μ t, 0) := by
  induction t with
  | nil => rfl
  | cons l t ih => simp only [wt_cons, shift, ih]; rfl

/-- Keep the strand and include its right region. -/
def colour (c : Col I X) : Col I (X × (I → ℤ)) := ⟨c.l, (c.r, 0)⟩

@[simp] theorem word (μ : X) (t : List (Letter I)) :
    wd Dₑ (μ, 0) t = (wd D μ t).map colour := by
  induction t with
  | nil => rfl
  | cons l t ih => simp only [wd_cons, weight, List.map_cons, ih]; rfl

/-- The original region embedding as a map of the complete SKM signature. -/
def inclusion : SigMap (sig D) (sig Dₑ) where
  region μ := (μ, 0)
  colour := colour
  colourSrc c := by change sh Dₑ c.l + (c.r, 0) = (sh D c.l + c.r, 0); rw [shift]; rfl
  colourTgt _ := rfl
  gen g := (g.1, (g.2, 0))
  dom g := word D g.2 g.1.dom
  cod g := word D g.2 g.1.cod
  left g := weight D g.2 g.1.dom
  right _ := rfl

theorem inclusion_odd (g : (sig D).Gen) : (sig Dₑ).odd ((inclusion D).gen g) = (sig D).odd g := by
  change decide (g.1.parity Dₑ = 1) = decide (g.1.parity D = 1)
  cases g.1 <;> rfl

@[simp] theorem inclusion_ob (μ : X) (t : List (Letter I)) :
    (inclusion D).obj (ob D μ t) = ob Dₑ (μ, 0) t := by
  apply Obj.ext
  · exact (weight D μ t).symm
  · exact (word D μ t).symm

@[simp] theorem inclusion_lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (inclusion D).layer (lay D μ u g v) = lay Dₑ (μ, 0) u g v := by
  simp [SigMap.layer, inclusion, lay, weight, word]

/-- The same free diagram with all regions embedded, at normal-form boundaries. -/
def diagram {μ : X} {t t' : List (Letter I)} (f : ob D μ t ⟶ ob D μ t') :
    ob Dₑ (μ, 0) t ⟶ ob Dₑ (μ, 0) t' :=
  Diagram.cast ((inclusion D).toLayerMap.map f) (inclusion_ob D μ t) (inclusion_ob D μ t')

@[simp] theorem diagram_mkD (μ : X) {t t' : List (Letter I)}
    (ls : List (LayerData I)) (h : SChain t ls t') :
    diagram D (mkD D μ ls h) = mkD Dₑ (μ, 0) ls h := by
  apply Diagram.ext
  change ((layList D μ ls).map (inclusion D).layer) = _
  simp only [layers_mkD, layList, List.map_map]
  apply List.map_congr_left
  intro x _
  exact inclusion_lay D μ x.1 x.2.1 x.2.2

@[simp] theorem diagram_id (μ : X) (t : List (Letter I)) :
    diagram D (𝟙 (ob D μ t)) = 𝟙 _ := rfl

variable {k : Type w} [CommRing k] (Sc : Scalars D k)
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

/-- Include the free linear Hom at its original signed boundary words. -/
def linear (μ : X) (t t' : List (Letter I)) :
    LinDiagram k (ob D μ t) (ob D μ t') →ₗ[k]
      LinDiagram k (ob Dₑ (μ, 0) t) (ob Dₑ (μ, 0) t') :=
  Finsupp.lmapDomain k k (diagram D)

@[simp] theorem linear_of (μ : X) {t t' : List (Letter I)} (f : ob D μ t ⟶ ob D μ t') :
    linear (k := k) D μ t t' (LinDiagram.of f) = LinDiagram.of (diagram D f) :=
  Finsupp.mapDomain_single

@[simp] theorem linear_sub (μ : X) (t t' : List (Letter I))
    (f g : LinDiagram k (ob D μ t) (ob D μ t')) :
    linear D μ t t' (f - g) = linear D μ t t' f - linear D μ t t' g :=
  (linear D μ t t').map_sub f g

@[simp] theorem linear_add (μ : X) (t t' : List (Letter I))
    (f g : LinDiagram k (ob D μ t) (ob D μ t')) :
    linear D μ t t' (f + g) = linear D μ t t' f + linear D μ t t' g :=
  (linear D μ t t').map_add f g

@[simp] theorem linear_neg (μ : X) (t t' : List (Letter I))
    (f : LinDiagram k (ob D μ t) (ob D μ t')) :
    linear D μ t t' (-f) = -linear D μ t t' f :=
  (linear D μ t t').map_neg f

@[simp] theorem linear_smul (μ : X) (t t' : List (Letter I)) (a : k)
    (f : LinDiagram k (ob D μ t) (ob D μ t')) :
    linear D μ t t' (a • f) = a • linear D μ t t' f :=
  (linear D μ t t').map_smul a f

@[simp] theorem linear_sum (μ : X) (t t' : List (Letter I)) {ι : Type*} (s : Finset ι)
    (f : ι → LinDiagram k (ob D μ t) (ob D μ t')) :
    linear D μ t t' (∑ i ∈ s, f i) = ∑ i ∈ s, linear D μ t t' (f i) :=
  map_sum (linear D μ t t') f s

@[simp] theorem linear_zero (μ : X) (t t' : List (Letter I)) :
    linear (k := k) D μ t t' 0 = 0 := (linear D μ t t').map_zero

@[simp] theorem linear_ite (μ : X) (t t' : List (Letter I)) (p : Prop) [Decidable p]
    (f g : LinDiagram k (ob D μ t) (ob D μ t')) :
    linear D μ t t' (if p then f else g) =
      if p then linear D μ t t' f else linear D μ t t' g := by
  split_ifs <;> rfl

/-- Include all relation labels, retaining both inverse products and finite windows. -/
def relationLabel : Rel D → Rel (ReservoirWeights.pairingExtension D)
  | .quadEq i ν => .quadEq i (ν, 0)
  | .quadZero i j ν hij hd => .quadZero i j (ν, 0) hij (by simpa using hd)
  | .quadNe i j ν hij hd => .quadNe i j (ν, 0) hij (by simpa using hd)
  | .slideL i j ν hij => .slideL i j (ν, 0) hij
  | .slideLEq i ν => .slideLEq i (ν, 0)
  | .slideR i j ν hij => .slideR i j (ν, 0) hij
  | .slideREq i ν => .slideREq i (ν, 0)
  | .braid i j l ν h => .braid i j l (ν, 0) h
  | .braidEq i j ν hij => .braidEq i j (ν, 0) hij
  | .zigE i ν => .zigE i (ν, 0)
  | .zigF i ν => .zigF i (ν, 0)
  | .invNe₁ i j ν hij => .invNe₁ i j (ν, 0) hij
  | .invNe₂ i j ν hij => .invNe₂ i j (ν, 0) hij
  | .invP₁ i ν hh => .invP₁ i (ν, 0) (by simpa using hh)
  | .invP₂ i ν hh => .invP₂ i (ν, 0) (by simpa using hh)
  | .invP₃ i ν m hm => .invP₃ i (ν, 0) m (by simpa using hm)
  | .invP₄ i ν n hn => .invP₄ i (ν, 0) n (by simpa using hn)
  | .invP₅ i ν m n hm hn => .invP₅ i (ν, 0) m n (by simpa using hm) (by simpa using hn)
  | .invM₁ i ν hh => .invM₁ i (ν, 0) (by simpa using hh)
  | .invM₂ i ν hh => .invM₂ i (ν, 0) (by simpa using hh)
  | .invM₃ i ν m hm => .invM₃ i (ν, 0) m (by simpa using hm)
  | .invM₄ i ν n hn => .invM₄ i (ν, 0) n (by simpa using hn)
  | .invM₅ i ν m n hm hn => .invM₅ i (ν, 0) m n (by simpa using hm) (by simpa using hn)
  | .dcupZero i ν n hn => .dcupZero i (ν, 0) n (by simpa using hn)
  | .dcapZero i ν n hn => .dcapZero i (ν, 0) n (by simpa using hn)
  | .zInt (.sq i ν) => .zInt (.sq i (ν, 0))
  | .zInt (.right i ν n hn) => .zInt (.right i (ν, 0) n (by simpa using hn))
  | .zInt (.left i ν n hn) => .zInt (.left i (ν, 0) n (by simpa using hn))

@[simp] theorem relationLabel_dom (r : Rel D) : (relationLabel D r).dom = r.dom := by
  cases r <;> (try cases ‹ZBase _›) <;> rfl
@[simp] theorem relationLabel_cod (r : Rel D) : (relationLabel D r).cod = r.cod := by
  cases r <;> (try cases ‹ZBase _›) <;> rfl
@[simp] theorem relationLabel_region (r : Rel D) : (relationLabel D r).ν = (r.ν, 0) := by
  cases r <;> (try cases ‹ZBase _›) <;> rfl

/-- Every defining linear relation is the identical relation at the embedded region. -/
theorem linear_relation (r : Rel D) :
    HEq (linear D r.ν r.dom r.cod (relation D Sc r)) (relation Dₑ Scₑ (relationLabel D r)) := by
  cases r
  case zInt b =>
    cases b <;> exact heq_of_eq (by
      simp only [relationLabel, Rel.ν, Rel.dom, Rel.cod, relation_zInt_of_scalars, linear_zero])
  all_goals apply heq_of_eq
  all_goals dsimp only [Rel.ν, Rel.dom, Rel.cod, relationLabel]
  all_goals
    simp [relation, dg, idg, linear_sub, linear_add, linear_neg,
      linear_ite, linear_zero, linear_of, diagram_mkD, diagram_id,
      ReservoirWeights.pairingExtensionScalars, ReservoirWeights.pairingExtension_dn,
      ReservoirWeights.pairingExtension_parity]

end OddMath.SKM.PairingExtension
