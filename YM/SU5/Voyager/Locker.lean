import YM.SU5.Voyager.Harbor
import YM.SU5.Voyager.Moraine
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable {a j:Axis}{P: Spine} (x:P.Spectrum0 a)
open Aria Set TopologicalSpace Metric Casting
local notation "χ[" k "]"=> P.advocate a x k
local notation "H[" k "]"=> P.ManyF k χ[k]
local notation "Ω[" k "]"=> P.heaven k χ[k]
local notation "Ψ[" k "]"=> P.seasons k χ[k]
local notation "ω[" k "]"=> P.colorZero k χ[k]
local notation "W[" k "]"=>P.cartage k χ[k]
local notation "E[" k "]"=>(Ψ[k]).E
local notation "V[" k "]"=>P.tableau k χ[k]
variable (j) (J:P.Ellis a x) {I:Type*}[Fintype I][DecidableEq I][Nonempty I]
open Caino Spectral Orbit.Prairie
variable (A:I↪Axis)(h:∀ i, A i ≠ j)
local notation "Ψ₀"=> Ψ[j]
local notation "ξ"=> (Ψ[j]).ℚmeasure
local notation "U"=> bars A (Ψ[j]).unit
local notation "X"=> Terrain I
local notation "Y"=> H[j]
-- geometry
abbrev fleur (u:X): Vantage:= WithLp.ofLp (vast A u)
lemma fleur_here (p:ℝ)(k:I): fleur A (sight p k)= aislePt (A k) p:=by
 funext i; unfold fleur; rw [sole_column]; change (p • YM.basis (A k):E4) i = _; by_cases p:i=A k<;>simp [p,aislePt]
include h
lemma rtoc (z: X): P.cartage j χ[j] (fleur A z)= (U).translation z:=by
 unfold bars OS.Semigroup.unit; let y:=vast A z; have he:y j=0:=by rw [show y=vast A z from rfl,optic]; exact sum_eq_zero (fun i _=> by rw [if_neg (Ne.symm (h i)),mul_zero]);
 change W[j] (WithLp.ofLp y)=((Ψ₀).edge (y j)).comp ((Ψ₀).U _); rw [he,OS.Semigroup.birth,P.uses_cart]; let s:= OS.Semigroup.SEP j y
 rw [ContinuousLinearMap.id_comp]; change (Ψ₀).U _=(Ψ₀).U s; rw [eyes_toFace j s]; congr 1; refine congrArg _ (funext fun i:Trans j=>?_); change y i.val= (y-y j • YM.basis j) i.val; rw [he,zero_smul,sub_zero]
lemma bumped (p:ℝ≥0)(k:I): dart (U) (p:ℝ) k=deltaMove j x (aislePt (A k) p.val):=by unfold dart; rw [← rtoc j x A h,fleur_here]; rfl
abbrev notice : PVM (P.ManyF j χ[j]) (Terrain I):= Caino.sails A (Ψ[j]).ℚmeasure
local notation "Μ"=> notice j x A
omit h in
lemma sealOut : (U).Spectrum (Μ):= barSpecs A (Ψ[j]).unit (ξ) (Ψ₀).joint
include J
variable (F: P.Flicker)
local notation "φ"=> specY x j F
local notation "κ" k:max=> (F.1.realWidth P k+F.1.realWidth P k)
local notation "γ" k:max=> (‖glareY x (F.1.kiss P j) k‖*‖flashY x F.1 k‖)
lemma qualifies (g:ℝ)(y:0<g): ∃ b e:ℝ,Quilt (U) φ g b e:=by
 let V:Finset Axis:=Finset.univ; let b:= ∑ i∈V, κ i; let c:=∑ i∈V, γ i; have ht(i:Axis):0 ≤ κ i:= by linarith [F.1.real_width_pos P i] -- name
 have he(i:Axis):0 ≤ γ i:=by positivity
 have hp(i:Axis): (κ i)≤ b:= Finset.single_le_sum (f:=fun i:Axis=>κ i) (fun i _=> ht i) (mem_univ i)
 have hq(i:Axis): (γ i) ≤ c:= Finset.single_le_sum (f:=fun i:Axis=>γ i) (fun i _=> he i) (mem_univ i)
 refine ⟨b+1,c+1,by linarith [ht j,hp j],by linarith [he j,hq j],fun i n r a u e=>?_⟩
 let p:= (⟨g,y.le⟩:ℝ≥0); let k:= A i; have hv:k≠j:=h i
 have he':(fleur A u) k=u i:= reach ..; let v:= (fleur A u); change b+1+r ≤ u i at e
 have g':0< v k-(κ k):= by linarith [show v k=u i from he', hp k]
 have hb:= earn j x k v J 0 p n hv F F (show (κ k)<v k from sub_pos.mp g'); change ‖inner ℂ φ ( (U).translation u ((dart (U) (p:ℝ) i^n) φ))‖≤_; rw [←rtoc j x A h, show dart (U) (p:ℝ) i=deltaMove j x (aislePt k (p:ℝ)) from bumped j x A h p i]
 rw [show E[j] 0=1 from OS.Semigroup.eZero _,one_mul] at hb; refine hb.trans (mul_le_mul (by linarith [hq k]) ?_ ?_ ?_)
 · unfold quality; refine pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by positivity) a ?_) n; exact (show r ≤ v k-(κ k) from (by linarith [hp k, (show v k=u i from he')]))
 · unfold quality; positivity
 · linarith [he j,hq j]
lemma shine_route (σ:I→Bool): ((Μ).diagonal φ).restrict (alley σ)≪ volume.restrict (alley σ):=occupation (U) (Μ) σ φ (sealOut j x A) (qualifies j x J A h F)
lemma live_bands (σ:I→Bool)(h₁: (Μ).diagonal φ (alley σ)≠0): volume.restrict (alley σ) ≪((Μ).diagonal φ).restrict (alley σ):= Spectral.Orbit.Prairie.growth (U) (Μ) σ φ (sealOut j x A) (qualifies j x J A h F) h₁
-- the ABSOLUTE continuity extends to entire manyF!
lemma fluid_bill (v:P.ManyF j (P.advocate a x j))(σ:I→Bool): ((Μ).diagonal v).restrict (alley σ) ≪ volume.restrict (alley σ):=by
 refine Measure.AbsolutelyContinuous.mk (fun L hL hx=>?_); let Y':=L∩alley σ; have he: MeasurableSet Y':= hL.inter (alley_open σ|>.measurableSet)
 rw [Measure.restrict_apply hL]; apply ((Μ).null_pair he _).2; let K:= (Μ).region Y'; let Z:= LinearMap.ker K.toLinearMap
 have ht(F:Flicker P): specY x j F∈ Z:=by
    have hv: ((Μ).diagonal (specY x j F)).restrict (alley σ) L=0:=(shine_route j x J A h F σ) hx; rw [Measure.restrict_apply hL] at hv; exact ((Μ).null_pair he _).1 hv
 have hv: Submodule.span ℂ (Set.range (specY x j)) ≤ Z := Submodule.span_le.mpr (by rintro y ⟨F,rfl⟩; exact ht F)
 exact (show v∈Z from closure_minimal (SetLike.coe_mono hv) K.isClosed_ker (flash_grant x j v))
-- thus for any Borel null in these coords whole energy surface; not saying no singular correlation with energy values.
omit h J
lemma journal(T:Set X): (notice j x A).region T= (ξ).region (terrain A ⁻¹' T):=rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.live_bands
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.fluid_bill
