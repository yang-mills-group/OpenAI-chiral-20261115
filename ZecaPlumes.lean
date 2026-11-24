import ZecaRose
import SatinThinHighness
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
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
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


structure Plume_LocalFieldBounds where
 k:ℕ
 num:Cover
 u:0 < num 3

instance : Countable Plume_LocalFieldBounds :=
 Function.Injective.countable (f:= fun p:Plume_LocalFieldBounds=>(p.k,p.num))
    (fun x y h=>by cases x; cases y; obtain ⟨rfl,rfl⟩:=Prod.mk.inj h; rfl)
def Plume_LocalFieldBounds.pose (u:Plume_LocalFieldBounds) : Vantage:=fun j=> (u.num j:ℝ)/5^u.k
abbrev Plume_LocalFieldBounds.tar (u:Plume_LocalFieldBounds) := u.pose 3
lemma Plume_LocalFieldBounds.hot(u:Plume_LocalFieldBounds): 0 < u.tar:= div_pos (by exact_mod_cast u.u) (by positivity)
abbrev tendril(u v:Plume_LocalFieldBounds): Gaia:=
 WithLp.toLp 2 fun j:Axis=> v.pose j - (if j=3 then -(u.pose j) else u.pose j)
lemma tendril_live(u v:Plume_LocalFieldBounds): tendril u v ≠ 0:=by
  intro h
  have hx:= congrArg (fun p:Gaia=>p 3) h
  have h' : ∀ x:Axis, x=3 → 0<u.pose x∧0<v.pose x:=by intro x p; subst x; exact ⟨u.hot,v.hot⟩
  change v.pose 3 - (if 3=(3:Axis) then -u.pose 3 else u.pose 3)=0 at hx
  rw [if_pos rfl] at hx
  linarith only [h' 3 rfl,hx]

-- units - UV scale r. δ (macro) and native.
def jetR(r:ℕ):ℝ:=κ*(P.plannedK r)
lemma jetR_pos(r:ℕ):0<P.jetR r := mul_pos (Nat.cast_pos.mpr P.sides_pos)
 (Nat.cast_pos.mpr (P.pointK_pos _ _))
lemma jetR_go:Tendsto P.jetR atTop atTop:=
 Filter.Tendsto.const_mul_atTop (Nat.cast_pos.mpr P.sides_pos) P.planned_grows

def jetS(r:ℕ):ℝ:=P.macroStep r*P.plannedK r
lemma jetS_pos(r:ℕ):0<P.jetS r:=mul_pos (P.macroStep_pos _)
 (Nat.cast_pos.mpr (P.pointK_pos _ _))
lemma jetS_base(r:ℕ):
 P.jetS r=P.macroStep (P.pointEra r)*P.baseK (P.pointEra r):=by
 let m:=P.pointEra r
 have hp:m≤r:= Nat.sub_le ..
 rw [jetS,plannedK,megaK,Nat.cast_mul,←mul_assoc,Nat.cast_pow,
       mul_comm _ _ |>.trans (P.daysF r m hp)]
lemma jetS_go:Tendsto P.jetS atTop (𝓝 0):=by
 have ht:= (P.flight_soon.comp P.future_payment).const_mul (κ:ℝ)
 rw [mul_zero] at ht
 have eq:(fun x=> (κ:ℝ) * P.flightCap (P.pointEra x))=P.jetS:=by
   funext x; rw [P.jetS_base,flightCap]
   have hκ:0<(κ:ℝ):=by exact_mod_cast P.sides_pos
   field_simp
 rw [←eq]; exact ht

variable (W₀:5 ∣ P.par.R.L.val)
include W₀
lemma fifths(k:ℕ): ∀ᶠ r:ℕ in atTop,5^k ∣ P.plannedK r:=by
 have he:Tendsto (fun r:ℕ=>r-P.pointEra r) atTop atTop:= (tendsto_natCast_atTop_iff.mp P.decades_go).congr' (P.payment_late.mono fun r h=> h.2.2.symm)
 filter_upwards [he.eventually_ge_atTop k] with r h
 exact ((pow_dvd_pow_of_dvd W₀ k).trans (pow_dvd_pow P.par.R.L.val h)).mul_right _

omit W₀
abbrev spacedPitch(r:ℕ)(p:Plume_LocalFieldBounds):Cover:= fun j=> (P.plannedK r/5^p.k:ℕ)*(p.num j)
include W₀
lemma spaced_prepare (p:Plume_LocalFieldBounds):
 ∀ᶠ r:ℕ in atTop,∀ j:Axis,(P.spacedPitch r p j:ℝ)=p.pose j*P.plannedK r:=by
 filter_upwards [P.fifths W₀ p.k] with r h j
 let Z₁:=P.plannedK r
 let d:ℕ:= 5^p.k
 have q:Z₁=(Z₁/d:ℕ)*d:= (Nat.div_mul_cancel h).symm
 have q':(Z₁:ℝ)=((Z₁/d:ℕ):ℝ)*d:=by exact_mod_cast q
 change (↑((↑(Z₁/d:ℕ):ℤ)*p.num j):ℝ)=_* (Z₁:ℝ)
 rw [Int.cast_mul,Int.cast_natCast]
 rw [q']
 unfold Plume_LocalFieldBounds.pose
 rw [show (d:ℝ)=(5:ℝ)^p.k by exact_mod_cast (rfl:d=5^p.k)]
 field_simp

lemma spaced_poses (p:Plume_LocalFieldBounds):
 ∀ᶠ r:ℕ in atTop, P.meshPose r (P.spacedPitch r p)= P.jetS r • p.pose:=by
 filter_upwards [P.spaced_prepare W₀ p] with r h
 funext j
 rw [pose_w,h]
 simp only [jetS, Pi.smul_apply,smul_eq_mul]; ring

lemma spaced_cover (p:Plume_LocalFieldBounds):
 ∀ᶠ r:ℕ in atTop,(P.roomy:ℤ) ≤ P.spacedPitch r p 3:=by
 have h:=Filter.Tendsto.const_mul_atTop p.hot P.planned_grows
 filter_upwards [P.spaced_prepare W₀ p,h.eventually_ge_atTop (P.roomy:ℝ)] with r q v
 have d: (P.roomy:ℝ) ≤ (P.spacedPitch r p 3 :ℝ):=(v.trans_eq (q 3).symm)
 exact_mod_cast d
