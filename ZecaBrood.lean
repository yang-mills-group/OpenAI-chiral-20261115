import ZecaSparrow
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster




section
-- loss
def downG (u:M): M:= u-Πγ (π u)
lemma downG_split (u v:M):
 inner ℂ u v-inner ℂ (π u) (π v)=inner ℂ (P.downG x u) (P.downG x v):=by
 have adj(p:G)(a:M):inner ℂ (Πγ p) a=inner ℂ p (π a):=by rw [←ContinuousLinearMap.adjoint_inner_left π,P.bank_star]; rfl
 have aj(p:G)(a:M):inner ℂ a (Πγ p)=inner ℂ (π a) p:=by rw [←inner_conj_symm,adj,inner_conj_symm]
 unfold downG; rw [inner_sub_left,inner_sub_right,inner_sub_right,
       (Πγ).inner_map_map,adj,aj]; ring
lemma downG_drip (u v:M)
 (h:inner ℂ u v=inner ℂ (π u) (π v)):
 ‖P.downG x u‖≤2*‖u-v‖:=by
 let c:=P.downG x
 have e: inner ℂ (c u) (c v)=0:=by rw [←P.downG_split,h,sub_self]
 have e': ‖c u‖^2 ≤‖c u‖*‖c (u-v)‖:=by
   have q:=norm_inner_le_norm (c u) (c (u-v)) (𝕜:=ℂ)
   have t:c (u-v)=c u - c v:=by unfold c downG; rw [map_sub,map_sub]; abel
   rw [t,inner_sub_right,e,sub_zero,inner_self_eq_norm_sq_to_K] at q
   rw [norm_pow,RCLike.norm_ofReal,abs_norm] at q
   rwa [t]
 have hv:‖c (u-v)‖≤2*‖u-v‖:=by
    apply le_trans (norm_sub_le ..)
    rw [(Πγ).norm_map]
    linarith only [show ‖π (u-v)‖≤ ‖u-v‖ from P.bank_cost ..]
 have h₁:= e'.trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
 nlinarith only [norm_nonneg (c u),norm_nonneg (u-v),h₁]
end

section
-- estimates for comparing vectors by limits
variable {A:Hilbert}{y z:ℕ→A} {s':ℂ}
lemma fam_gram_norm2 (h:Tendsto (fun i=>inner ℂ (y i) (y i)) atTop (𝓝 s')):
 Tendsto (fun i=>‖y i‖^2) atTop (𝓝 s'.re):=
    ((Complex.continuous_re.tendsto _).comp h).congr (fun _=>inner_self_eq_norm_sq (𝕜:=ℂ) _)

lemma fam_gramBound (h:Tendsto (fun i=>inner ℂ (y i) (y i)) atTop (𝓝 s')):
 ∃ C:ℝ,∀ᶠ i in atTop,‖y i‖≤C:=by
 refine ⟨s'.re+2,?_⟩
 filter_upwards [(fam_gram_norm2 h).eventually (ge_mem_nhds (lt_add_one _))] with i t
 nlinarith only [t]
lemma fam_dist
 (h:Tendsto (fun i=>inner ℂ (y i) (y i)) atTop (𝓝 s'))
 (k:Tendsto (fun i=>inner ℂ (y i) (z i)) atTop (𝓝 s'))
 (g:Tendsto (fun i=>inner ℂ (z i) (z i)) atTop (𝓝 s')):
 Tendsto (fun i=>‖y i-z i‖) atTop (𝓝 0):=by
 have he:=((fam_gram_norm2 h).sub (((Complex.continuous_re.tendsto _).comp k).const_mul 2)).add
     (fam_gram_norm2 g)
 rw [show _ - _ + s'.re=(0:ℝ) from by ring] at he -- holes??
 have s:=he.sqrt
 rw [Real.sqrt_zero] at s
 refine s.congr fun i=>?_
 exact (congrArg Real.sqrt (norm_sub_sq (𝕜:=ℂ) (y i) (z i)).symm).trans (Real.sqrt_sq (norm_nonneg _))

end

variable (f)(p q:Plume_LocalFieldBounds)(W₀:5∣P.par.R.L.val)(J:P.Ellis 3 x)
 {seq:ℕ→ℕ}(T:P.Nepenthe seq x)
include W₀ J T
lemma downG_flying :
 Tendsto (fun i=>‖P.downG x (P.finch x f p 0 (seq i))‖) atTop (𝓝 0):=by
 let a:Cover:=fun _=> P.charmF
 have e:=fam_dist (P.freed_gram (f:=f) x p p 0 0 W₀ T)
    (P.freed_gram (f:=f) x p p 0 a W₀ T)
    (P.freed_gram (f:=f) x p p a a W₀ T)
 have u:=e.const_mul 2
 rw [mul_zero] at u
 refine squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) ?_ u
 filter_upwards [T.sky.eventually (P.freed_clone (f:=f) x p W₀ J)] with i h
 exact P.downG_drip x _ _ h.symm

abbrev chick (f:ℕ) (p:Plume_LocalFieldBounds) (r:ℕ): G:=π (P.finch x f p 0 r)
lemma flying_gram :
 Tendsto (fun i=> inner ℂ (P.chick x f p (seq i)) (P.chick x f q (seq i))) atTop
   (𝓝 (lyric p q)):=by
 let y:= fun i=>P.finch x f p 0 (seq i)
 let z:= fun i=>P.finch x f q 0 (seq i)
 have hy:Tendsto (fun i=>P.downG x (y i)) atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr
   (P.downG_flying f x p W₀ J T)
 have hz:Tendsto (fun i=>P.downG x (z i)) atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr
   (P.downG_flying f x q W₀ J T)
 have h:= (P.freed_gram (f:=f) x p q 0 0 W₀ T).sub (hy.inner (𝕜:=ℂ) hz)
 simp only [inner_zero_left,sub_zero] at h
 refine h.congr fun i=>?_
 rw [←P.downG_split]
 exact sub_sub_cancel ..
#check norm_sub_sq
#print axioms Spine.flying_gram
