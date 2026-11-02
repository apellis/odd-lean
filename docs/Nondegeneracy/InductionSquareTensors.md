# Tensor generators through an induction square

For the scalar and weighted append comparisons in DeformedActionAssembly
§§5–6 and STATUS critical-chain items 2–3,
let `J : C → A`, `U : A → D`, `Q : C → B`, `T : B → D` be additive linear
superfunctors with a chosen equality `J ⋙ U = Q ⋙ T`. Given a module `R` on
`C`, a module `M` on `B`, and an even map `c : Ind_Q R → M`, the four canonical
maps flatten induction, transport through the chosen square, unflatten
induction, then induce `c`.

`BalancedInduction.squareComparison` retains this exact composite. Its
`squareComparison_mem` proves evenness from that of `c`.
`squareComparison_eq` identifies the functor-level equality map with the
component equality map in the already selected append comparisons.
`squareComparison_total_tensor` computes the composite on
`[id ⊗ [g ⊗ b]]` as
`[eqToHom(h_obj)⁻¹ ≫ U(g) ⊗ c([id ⊗ b])]`.
The literal equality transport is retained, so applications must identify
the chosen square's object component explicitly. Arrows and vectors need
not be homogeneous.

`squareLinear` exposes the same comparison as a linear map on the literal
underlying balanced coends. `squareLinear_apply` identifies its value with
the selected module map, and `squareLinear_tensor` gives the generator
formula on those carriers. The carrier conversion is performed with
abstract functors before specializing to scalar or weighted quotients.

`composition_total_linear` and `total_linear_congr` expose total-map
composition and equality as linear-map statements while the endpoint
supermodules are abstract. The scalar and weighted selected comparisons
use them before evaluating concrete coend generators.

The paired consumer uses the actual append/truncation square and a
restricted truncated mixed representable, the actual quotient-induction
counit, both moving parities and arbitrary old output arrows.
It checks the tensor formula, evenness and all owned axioms. The producer, fixture and paired consumer pass strict scoped compilation
with the pinned toolchain and compatibility settings; all owned source
axioms are allowed. Full CI is pending. These formulas do not themselves
identify any selected quotient/descent comparison.
