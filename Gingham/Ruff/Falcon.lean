import Gingham.Ruff.Fuchsia

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)

namespace VoyageB
open Diary
open CF.Gingham.Ruff
variable (a c μ E:ℝ)(d l s i k:ℕ)
local notation "Y"=>P.run
local notation "~p~" s:max=>P.run.meter.a s
local notation "K"=>P.calibration
local notation "W"=>underlay P.par
local notation "R" s:max i:max k:max => RootBook Y i k s
local notation "Ω" s:max i:max => Journey.side Y i s



open VelourBoard
open Papyrus Papyrus.Franc Preparation Yoke
open Pressure.Worth
variable {P s i k} {C ρ v q :ℝ}
local notation "𝒳" s:max i:max => exhibit P.run P.large s i
set_option linter.unusedSectionVars false


open Pressure BProof
open GarlandBook Lander
open SectorNext.Remainder.Scales
local notation "𝓍" s:max=>hat P.par.R.L P.par.x s
def peak(P:Spine)(s:ℕ):ℝ:= Real.exp ((Real.log (Real.log (hat P.par.R.L P.par.x s)))^2/4)
def chi(P:Spine)(s:ℕ):ℝ:=(SectorNext.Remainder.Scales.g SU.group P.par.R.L (hat P.par.R.L P.par.x s))^2














lemma pkPos(P:Spine)(s:ℕ):1≤ (peak P s):=
 Real.one_le_exp (div_nonneg (sq_nonneg _) (by norm_num))
lemma pk(P:Spine)(s:ℕ):(peak P s)^4=(CF.Linen.notch ((hat P.par.R.L P.par.x s))):=by
 unfold peak Linen.notch;rw [←Real.exp_nat_mul]; push_cast; congr 1; ring

lemma tallCC (P:Spine):∀ᶠ s in atTop, 0<chi P s ∧
      chi P s ≤ 2/((hat P.par.R.L P.par.x s)):=by
 let L:= P.par.R.L
 let u:= SU.group.slopeConstant * Real.log L.val
 filter_upwards [(turnover P.par).eventually (eventually_gt_atTop 0),
                 (turnover P.par).eventually (eventually_gt_atTop (-2*u))]
     with s h t
 let z:=SectorNext.Remainder.Scales.y SU.group L ((hat P.par.R.L P.par.x s))
 have hz: (hat P.par.R.L P.par.x s) + u = z:= rfl
 have hp: (hat P.par.R.L P.par.x s)< 2*z:=by rw [←hz];linarith only [t]
 have zp:0<z:=by nlinarith only [lt_trans h hp]
 unfold chi
 constructor
 · exact pow_pos (SectorNext.Remainder.Scales.gauge SU.group L zp) _
 rw [ (show _ = z⁻¹ from eq_inv_of_mul_eq_one_left
     ((mul_comm ..).trans (yg2 SU.group L zp)))]
 rw [le_div_iff₀ h, ←div_eq_inv_mul,div_le_iff₀ zp]
 exact hp.le







variable {a c μ d}{F:ℕ→Fleece P.calibration}{ν:ℕ→ℕ}
variable (β:Lander P a c μ d ν F)
include β in
lemma cauldron:∀ᶠ s in atTop, Location.Boot ((hat P.par.R.L P.par.x s)) (~p~ s) :=by
 filter_upwards [β.clearFor 1 zero_le_one 2 le_rfl] with s h
 obtain ⟨n,t⟩:=h.1.exists
 rw [show ~p~ s=(RootBook Y (irr P (ν n)) (uvv P (ν n)) s).p from
      (((P.run.voyage _).X (P.run.uv _)).pull.owns s t.ok.le).width]
 exact t.gears.boot
include β in
lemma giltS: ∀ᶠ s in atTop, 0<chi P s ∧
     0<(~p~ s).threshold ∧ (~p~ s).threshold≤1 ∧
     (chi P s)/(~p~ s).threshold^2≤2/(peak P s)^8:=by
 have z:Tendsto temp atTop (𝓝 (0:ℝ)):=by simpa using Work.E09.radiusB_temp 0
 filter_upwards [tallCC P, cauldron β, (turnover P.par).eventually
          (eventually_gt_atTop (0:ℝ)), (z.comp (turnover P.par)).eventually (ge_mem_nhds zero_lt_one)] with s h u t v
 let d':=peak P s; let x:=(hat P.par.R.L P.par.x s)
 rw [u.threshold]
 have a:0<d':=zero_lt_one.trans_le (pkPos P s)
 have b:0<temp x:=by unfold x temp; positivity
 refine ⟨h.1,b,v,div_le_iff₀ (pow_pos b 2)|>.2 ?_⟩
 apply h.2.trans_eq
 change 2/x=2/d'^8*(temp x)^2
 have e:temp x=(Real.sqrt x)⁻¹*d'^4:=by rw [show d'=peak P s from rfl,pk];rfl
 rw [e,mul_pow,←pow_mul,inv_pow,Real.sq_sqrt t.le]
 norm_num
 field_simp
 exact div_self t.ne'

