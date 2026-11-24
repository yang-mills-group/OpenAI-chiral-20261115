import YM.SU5.Selected.Sealing
/-! # Reynolds consumers on the physically continuous chart
In particular this computes same cap price for ungauged/averaged pair
and lands at many hosts. More general continuity from Borel costs is separate. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Tapestry (Swatch fabric render spread texture appear appear_inj)
open Set CF.Pannier.Chancel
section localChart
variable (S:Finset Cover)(K':Calibration) (m:Side)(f:Swatch S)
local notation "rx"=> render S K'
local notation "n"=> K'.c m
local notation "φ" => appear S K' m
variable (v:Hosp S (K'.c m))(p:Continuous (appear S K' m f))
noncomputable def orbitC (g:Zodiac (K'.c m)):= Tapestry.ocelli K' S (g∘wrap (More n)) f
lemma orbitC_apply (g:Zodiac (K'.c m)): φ (orbitC S K' m f g)=getBack (appear S K' m f) g:=by
  funext x; apply (twist (quantU (tradew (K'.c m) g))).injective
  exact (Tapestry.decorates K' S (g∘wrap (More n)) f m g (fun i _=>rfl) x).symm.trans (trueBack (φ f) g x)
include v p
lemma orbitC_cont : Continuous (orbitC S K' m f):=by
  let Q:= (⟨_,costsBack (φ f) p⟩ : ContinuousMap (Zodiac n × Fields n) (FC (Single n)))
  let U:= Q.curry
  refine continuous_iff_continuousAt.mpr fun x=> Metric.tendsto_nhds.mpr fun ε hp=> ?_
  filter_upwards [Metric.tendsto_nhds.mp (U.continuous.tendsto x) ε hp] with y hy
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ hy
  apply Tapestry.sampling S K' m v
  intro z
  rw [map_sub,orbitC_apply,orbitC_apply]
  change ‖U y z - U x z‖ ≤ dist (U y) (U x)
  rw [←dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist z

noncomputable def reynoldsC := ∫ g, orbitC S K' m f g ∂domeLaw (K'.c m)
include v p
lemma reynoldsC_apply : φ (reynoldsC S K' m f)=molasses (φ f):=by
  funext x
  let L:Swatch S→L[ℂ] FC (Single n):= ((LinearMap.proj x).comp (φ)).mkContinuous (spread S) fun g=> Tapestry.renderLe S K' m g x
  change L (∫ g,orbitC S K' m f g∂domeLaw (K'.c m))=_
  refine (ContinuousLinearMap.integral_comp_comm (𝕜:=ℂ) (E:=Swatch S) (Fₗ:= FC (Single n)) L («φ»:=orbitC S K' m f) (μ:=domeLaw n) ?_).symm.trans ?_
  · exact (orbitC_cont S K' m f v p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply integral_congr_ae
  apply Eventually.of_forall; intro g; exact congrFun (orbitC_apply S K' m f g) x
lemma neutralC : Tapestry.Neutral K' (render S K' (reynoldsC S K' m f)):=by
  have he: covariant (φ (reynoldsC S K' m f)) := by rw [reynoldsC_apply S K' m f v p]; exact preserves_s p
  exact Tapestry.onceNeutral (texture ..) (m:=m) v he
end localChart
section
variable (T : Arena Y H G.history.circuit j 0 false)
variable (S:Finset Cover)(s:ℕ)(m:Side) (f:Swatch S)
local notation "ϕ"=>allCap Y H V G j S s T
lemma reynolds_cap (v:Hosp S (tent Y H|>.c m))(p:Continuous (appear S K m f)): (ϕ) f=(ϕ) (reynoldsC S K m f):=by
  let ρ:= orbitC S K m f
  unfold reynoldsC
  refine Eq.trans ?_ (ContinuousLinearMap.integral_comp_comm (𝕜:=ℂ) (E:=Swatch S) (Fₗ:=↥(catalog Y H V G j false T)) (ϕ) (φ:=ρ) (μ:=domeLaw ((K).c m)) ?_); swap
  · exact (orbitC_cont S K m f v p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h(g):ϕ (ρ g)=ϕ f:=by
    exact Subtype.ext (cap_ward Y H V G j false T S s _ _ (texture S K f) (texture S K (ρ g)) (Tapestry.decorates K S _ f)).symm
  change (ϕ f)=∫ g, ϕ (ρ g)∂domeLaw _
  simp_rw [h]; simp
lemma reynolds_exact {u g:Family (tent Y H)}(v:Hosp S (tent Y H|>.c m))(p:InTest K true S false u)(h:InTest K true S false g)
    (t:Continuous (u m))(x:g m=molasses (u m)):
    seal₀ Y H V G j false T s (observe (aux_test h))=seal₀ Y H V G j false T s (observe (aux_test p)):=by
  let F':= fabric S K p
  let Q:= reynoldsC S K m F'
  have he: appear S K m F'=u m:= congrFun (Tapestry.render_fabric S K p) m
  have hu:Continuous (appear S K m F'):= he.symm ▸ t
  have hv: render S K Q=g:= Tapestry.looksLike (m:=m) v (texture ..) h ((reynoldsC_apply S K m F' v hu).trans ((congrArg molasses he).trans x.symm)) -- orientation tune
  rw [←capₐ Y H V G j S s T F' (observe (aux_test p)) (Tapestry.render_fabric S K p).symm, ←capₐ Y H V G j S s T Q _ hv.symm]; exact (reynolds_cap Y H V G j T S s m F' v hu).symm
end
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.reynolds_exact
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.neutralC
