import ZecaNimbus
import ZecaBlenny
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





open _root_.YM.ZecaSky


def collegia(p q:Vantage): Gaia:=
 WithLp.toLp 2 fun j:Axis=> q j - (if j=3 then -(p j) else p j)
def reecho(p d:Vantage)(t:ℕ)(l:ℤ):Vantage:=
 fun a=> if a=3 then p a + (t:ℝ) else p a + d a*l
def heartscale(d:Vantage):ℝ:= ‖(WithLp.toLp 2 d:Gaia)‖
lemma hpos{d:Vantage}(n:d≠0):0<heartscale d:=
 norm_pos_iff.mpr (fun e=>n (WithLp.toLp_injective 2 e))

def heartside(d:Vantage):Gaia:= (heartscale d)⁻¹ • WithLp.toLp 2 d
lemma hunit{d:Vantage}(n:d≠0):‖heartside d‖=1:=by
 have y:=hpos n
 rw [heartside,norm_smul, Real.norm_of_nonneg (inv_nonneg_of_nonneg y.le)]
 exact inv_mul_cancel₀ y.ne' -- match heartscale
lemma hflip{d:Vantage}(n:d 3=0):heartside d 3=0:=by
 simp [heartside,n]

lemma rewakes (p:Vantage){d:Vantage}(n:d≠0) (t:ℕ) (i j:ℤ):
 collegia (reecho p d t i) (reecho p d t j)=
   ZecaSky.wake (heartside d) (2*p 3+2*t) (((j:ℝ)-i)*heartscale d):=by
 unfold ZecaSky.wake collegia
 congr 1; funext a
 have y:=hpos n
 simp only [reecho]
 by_cases b:a=3
 · subst a
   simp; ring
 rw [if_neg b,if_neg b,if_neg b,if_neg b]
 simp [heartside]
 field_simp
lemma echo3(p d:Vantage)(t:ℕ)(i:ℤ):
 reecho p d t i 3 = p 3+t:=if_pos rfl
lemma echoM(p:Vantage){d:Vantage}(n:d 3=0) (t:ℕ)(i:ℤ):
 reecho p d t (i+1)=d+ reecho p d t i:=by
 funext a; by_cases m:a=3
 · subst a; simp [n,echo3]
 simp [reecho,m]; ring
lemma echoT(p d:Vantage)(t:ℕ){j:Axis}(q:j≠3):
 reecho p d (t+1) 0 j= reecho p d t 0 j:=by simp [q,reecho]
lemma echoZero(p d:Vantage):reecho p d 0 0=p:=by
 funext a
 simp [reecho]
#check @of_slideP
