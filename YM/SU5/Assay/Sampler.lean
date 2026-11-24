import YM.SU5.Assay.GridMass
import YM.SU5.Assay.Rehearses
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 Sampler for imposing an undisplaced value at each grid point. Later the
 operator imposed at `P.meshPose t k` will be `rawBase` of the actual
 insertion in its own lags. But we allow **varying** unposed samples that
 may converge only in an alignment chamber.
-/
variable (t:ℕ)(F:SampleDose)
local notation "φ"=> P.charter j x
local notation "Z"=>P.vtile t
local notation "D"=>P.meshPose t
local notation "α"=>P.activation t F
local notation "Q"=>P.usedGrid t F
def sampler (u:Vantage→X):X:=∑i∈Q,α i • φ (Z i) (u (D i))
local notation "M"=>P.sampler j x
local notation "σ"=>P.sampler j x t F
lemma sampler_add (u v:Vantage→X):σ (u+v)=σ u+σ v:=by simp only [sampler,Pi.add_apply,P.charter_add,smul_add,sum_add_distrib]
lemma sampler_sub (u v:Vantage→X):σ (u-v)=σ u-σ v:=by simp only [sampler,Pi.sub_apply,P.charter_sub,smul_sub,sum_sub_distrib]
lemma sampler_star (u:Vantage→X): star (σ u)=σ (fun y=>star (u y)):=by
 simp only [sampler,star_sum,star_smul,P.activation_real,P.charter_star]
-- uniform comparison holds against function-valued estimates too, no
-- dependence on their behavior outside topological support
variable (u v:Vantage→(P.ColorHil j x).Op)
lemma sampler_cost {C:ℝ}(p:∀y∈tsupport F.val,‖u y‖≤C): ‖σ u‖≤P.gridMass F t*C:=by
 unfold gridMass sampler
 rw [sum_mul]
 refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i z=>?_)
 rw [norm_smul,P.charter_cost]
 exact mul_le_mul_of_nonneg_left (p _ ((P.usedPose t F i).1 z)) (norm_nonneg _)
lemma sampler_diff {C:ℝ}(p:∀y∈tsupport F.val, ‖u y - v y‖≤C): ‖σ u-σ v‖≤P.gridMass F t*C:=by
 rw [←P.sampler_sub];exact P.sampler_cost _ _ _ _ _ p
lemma sampler_cap {C:ℝ}(h:0≤C)(p:∀y∈tsupport F.val,‖u y‖≤C):
 ∃M':ℝ,0≤M'∧∀ᶠt in atTop, ‖P.sampler j x t F u‖≤M':=
 ⟨((∫y,‖F.val y‖)+1)*C,mul_nonneg (add_nonneg (integral_nonneg (fun y=>norm_nonneg (F.val y))) zero_le_one) h,(P.gridMass_cap F).mono fun t e=>
    (P.sampler_cost _ _ t _ _ p).trans (mul_le_mul_of_nonneg_right e h)⟩
variable {P j x F u v}
-- Suppose sampler for `u` rehearses successfully; then so does sampler
-- (to same chamber) with any varied values, uniformly close on support.
lemma sampler_transfers {I:Type*}{f:I→Vantage→(P.ColorHil j x).Op}{T:(P.ManyF j x).Op}{l:Filter I}{d:I→ℝ}{s:I→ℕ}
 (p:P.Rehearses j x (fun t=>M t F u) atTop T) (h:Tendsto s l atTop)
 (q:Tendsto d l (𝓝 0))(v:∀ᶠ i in l,∀y∈tsupport F.val, ‖f i y - u y‖≤d i):
 P.Rehearses j x (fun i=>M (s i) F (f i)) l T:=by
 have t:Tendsto (fun i=>P.gridMass F (s i)*d i) l (𝓝 0):=by
   have w:= ((P.gridMass_limit F).comp h).mul q;rw [mul_zero] at w;exact w
 exact (p.visit h).squeeze' t (v.mono fun i z=> P.sampler_diff j x (s i) F _ _ z)
-- For directly feeding in an aligned sample, shifted back *inside the
-- unprojected sum*, can conjugate input globally at that address
-- (even off sampling grid; poses transverse only).
lemma sampler_align (u:Vantage→X)(r:P.VMark): σ (fun y=>φ r (u y))=φ r (σ u):=by
 unfold sampler; rw [P.charter_list]
 refine Finset.sum_congr rfl fun i _=>?_
 rw [P.charter_smul,P.charter_sum,P.charter_sum,add_comm _ r]
lemma sampler_unwind (u:Vantage→X)(r:P.VMark): φ (-r) (σ (fun y=>φ r (u y)))=σ u:=by rw [sampler_align,P.charter_cancel]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
