import Mussel.Canvas
import Mussel.Cot
import GlazeS.Poll
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT
open Broker
variable (P:Spine)(F:ℕ)
local notation "T"=>timeMesh P.par
private theorem scaleRise:∃ D : ℝ,0 < D ∧ ∀ s:ℕ,(durationZ P s:ℝ) ≤ D*(1+(s:ℝ))^6:=by
 obtain ⟨D,h,w⟩:= polyRise P
 let u:= ((22:ℝ)+P.calibration.ℓ+1)
 refine ⟨D+u,(by unfold u; positivity),fun s=>?_⟩
 unfold durationZ; push_cast; have he:=w s; have hf:1 ≤ (1+(s:ℝ))^6:= one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
 nlinarith [Nat.cast_nonneg (α:=ℝ) P.calibration.ℓ]
private theorem step_down:Tendsto (fun s=>lane P s (durationZ P s)) atTop (𝓝 0):=by
 obtain ⟨D,h,t⟩:=scaleRise P
 let L':=P.par.R.L.val; have b₀:1<(L':ℝ):=by exact_mod_cast P.par.R.coarse.trans_lt' (by norm_num:1<3)
 let θ:ℝ:=(↑L')⁻¹; have e:0<θ∧θ<1:=⟨inv_pos.mpr (zero_lt_one.trans b₀),(inv_lt_one₀ (zero_lt_one.trans b₀)).2 b₀⟩
 have hf:‖θ‖<1:= by rw [Real.norm_of_nonneg e.1.le]; exact e.2
 have hg:Tendsto (fun s:ℕ=>(1+(s:ℝ))^6 * θ^s) atTop (𝓝 0):=by
    let f(n:ℕ):= (n:ℝ)^6*θ^n
    have H0:Summable f:= summable_pow_mul_geometric_of_norm_lt_one _ hf
    apply Summable.tendsto_atTop_zero
    apply Summable.congr ( ((summable_nat_add_iff 1).2 H0).mul_right θ⁻¹)
    intro n; unfold f; rw [Nat.cast_add,Nat.cast_one,pow_succ θ, mul_assoc _ _ θ⁻¹,mul_inv_cancel_right₀ e.1.ne',add_comm]
 let d:ℝ:=(T).base
 refine squeeze_zero (fun i:ℕ=> show 0 ≤ lane P i (durationZ P i) from NNReal.coe_nonneg _) (g:=fun s:ℕ=>D*d*((1+(s:ℝ))^6 * θ^s)) ?_ (by simpa using hg.const_mul (D*d))
 intro i; rw [lane_eq]
 apply (mul_le_mul_of_nonneg_right (t i) (NNReal.coe_nonneg _)).trans_eq
 change _ * (↑((T).base / ((T).L:ℝ≥0)^i):ℝ)=_
 rw [NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast]; unfold d θ L'; rw [inv_pow]; change _ * (_ / ((P.par.R.L.val:ℝ)^i))=_; ring
lemma radiusTiny:Tendsto (Hemlock.radius P F) atTop (𝓝 0):= by simpa only [add_zero] using (((step_down P).add (countMoney P)).add (recessVanish P F))

variable (C D:ℕ→ℕ→ℝ)
local notation "qz" s:max=>Hemlock.radius P F s
local notation "az" s:max=>canvas P F C D s
-- choose before all tests.
variable (s:ℕ)
-- B of old P.Spine using shadow explicit P and same scope implicit args? need explicit.
variable {x0:P.Spectrum0 3}{Kg:P.Register}{c0 r0:ℕ→ℕ}{J0:P.Ellis 3 x0}(hg:P.Experiment Kg c0 r0 x0 J0)(Zc:Lead.Clan)
#check sew
noncomputable def depute := sew hg Zc (az s) (central P F s) (qz s) (Calico.bands (cellar P F s) 22) (dressed P F C D s) (radius_pos P F s)
noncomputable def slotH:= (depute P F C D s hg Zc).choose
noncomputable abbrev offer_update:= c0 (slotH P F C D s hg Zc)
noncomputable abbrev offer_n:=r0 (slotH P F C D s hg Zc)
noncomputable def agent :FrameZ P Zc.2 (offer_update P F C D s hg Zc):=(depute P F C D s hg Zc).choose_spec.choose
-- proof w encoded
theorem agentBorn:P.birthF 3 (offer_update P F C D s hg Zc) (agent P F C D s hg Zc).question:=(depute P F C D s hg Zc).choose_spec.choose_spec.choose
theorem deputized:Sewed Zc (az s) (central P F s) (qz s) (offer_update P F C D s hg Zc) (offer_n P F C D s hg Zc) (agent P F C D s hg Zc) (agentBorn P F C D s hg Zc) x0:=(depute P F C D s hg Zc).choose_spec.choose_spec.choose_spec
#print axioms deputized
#print axioms radiusTiny
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
