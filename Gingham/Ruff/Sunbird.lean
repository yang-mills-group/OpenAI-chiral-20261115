import Gingham.Ruff.Prismatic
import Gingham.Ruff.Featherbed
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
open Papyrus Papyrus.Franc Yoke
open Pressure.Worth
#check amulet

/-- retains drawbill during same commission -/
structure Radiant (P:Spine)(C ρ:ℝ):Prop where
 pos:1 ≤ ρ
 view : Drawbill P.par C
 late: ∀ᶠ s:ℕ in atTop, ∀ᶠ n:ℕ in atTop,∀k:ℕ, (P.run.voyage n).kick ≤ k→s≤P.run.uv k→
     ShelterCost C P.run s n k ∧ GlowCost C ρ P.run s n k

variable (C ρ:ℝ)
def Atmosphere (P:Spine):=
   ∃C ρ:ℝ,Radiant P C ρ
variable {P s C}

lemma atmosphere {C:ℝ}(g:Drawbill P.par C)(p:∀ᶠ s:ℕ in atTop, ∀ᶠ n:ℕ in atTop,∀k:ℕ, (P.run.voyage n).kick ≤ k→s≤P.run.uv k→ShelterCost C P.run s n k):
    Atmosphere P:=by
  obtain ⟨r,pos,u⟩:= Yoke.glowing P.run g
  exact ⟨C,r,pos,g, p.mono fun s t=>(t.and (u s)).mono fun i v k z h=>⟨v.1 k z h,v.2 k⟩⟩


local notation "λ₀" s:max => meterC (hat P.par.R.L P.par.x s)

def Patina (P:Spine)(ρ:ℝ)(s i k:ℕ):=
 ∀{S:Finset Cover}(f:Family P.calibration)(_t:InTest P.calibration true S false f)(q:ℝ),
   0<q→ Shines ρ (exhibit P.run P.large s i f) q→
   ‖Journey.sharp P.run P.large s i k f‖≤ Real.exp (14*meterC (hat P.par.R.L P.par.x s)*sites (Journey.side P.run i s))*q

#print Journey.listen

variable {ρ}
lemma Radiant.hum (h:Radiant P C ρ):
 ∀ᶠ s:ℕ in atTop,∀ᶠ e:ℕ in atTop,Patina P ρ s (irr P e) (uvv P e) :=by
 filter_upwards [h.late] with s qs
 filter_upwards [(rising_i P).tendsto_atTop.eventually qs,atHeight P s] with e qh u
 intro S f t q qp g
 specialize qh (uvv P e) u.depth u.enters
 have a:=amulet P.run s (irr P e) (uvv P e) (z:=Real.log q)
    qh.1 qh.2 u.depth (exhibited _ _ _ _ _ t).env
    ((Real.exp_log qp).symm ▸ g : Shines ρ _ (Real.exp (Real.log q))) -- avoid motive dependent
 rw [Real.exp_add,Real.exp_log qp,present_send,mul_comm] at a
 exact a


def Fee (P:Spine)(s w:ℕ) :ℝ :=
    14*meterC (hat P.par.R.L P.par.x s) * (2*(16*P.par.block.val*w:ℝ))^4

local notation "𝒳" s:max i:max => exhibit P.run P.large s i
variable {w m :ℕ} {q:ℝ} {i k :ℕ}
set_option linter.unusedSectionVars false

lemma Patina.earn {S:Finset Cover}
    (p:Patina P ρ s i k)
    (v:(Ω s i).val^4 ≤ (pitch K w)^4*m)
    (f:Family P.calibration)(t:InTest P.calibration true S false f)
    (g:Shines ρ ((𝒳 s i) f) q)
    (a:0<q):
    ‖Journey.sharp Y P.large s i k f‖ ≤ (Real.exp (Fee P s w))^m * q := by
 apply (p f t q a g).trans
 apply mul_le_mul_of_nonneg_right _ a.le
 rw [←Real.exp_nat_mul]
 have h:
   sites (Ω s i)≤ (2*(16*P.par.block.val*w:ℝ))^4*m:=by


    have x : ((Ω s i).val:ℝ)^4 ≤ (16*P.par.block.val*w:ℝ)^4*m:= by change _ ≤ (16*P.par.block.val*w)^4*m at v; exact_mod_cast v
    change (((Ω s i).val * 2:ℕ):ℝ)^4≤ _
    rw [Nat.cast_mul,Nat.cast_ofNat,mul_comm _ (2:ℝ),mul_pow,mul_pow (2:ℝ) (_ * w:ℝ)]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left x (by positivity)
 apply Real.exp_monotone
 unfold Fee
 rw [mul_comm (m:ℝ),mul_assoc (14*meterC _)]
 exact mul_le_mul_of_nonneg_left h (mul_nonneg (show (0:ℝ) ≤ 14 from by norm_num) (BProof.coin_pos ..).le)

