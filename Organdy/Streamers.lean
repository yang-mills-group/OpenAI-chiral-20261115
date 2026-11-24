import Organdy.Beads
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell


open Roots
variable {P:Spine}{s q k:ℕ}{c:Cuts}{d:Stores}
local notation "N'" =>kitGap P s q
local notation "Y'" => guineas P s
local notation "ι'" => (hueW P.par.R.L Y' * yInvoice c.b)
local notation "W✽" => prismPan P.par.R d.v Y'
local notation "R✽" => shaft P s

local notation "H" => P.calibration
local notation "Λ" => P.par
local notation "w✤" => walkF Y'
abbrev bauble (P:Spine)(s v:ℕ):=
 2*Real.log (2/prismPan P.par.R v (guineas P s)) + 6
local notation "T✽" => bauble P s d.v

variable (t:Seating P c d s q k)
def crowning(P:Spine)(c:Cuts)(s:ℕ):ℝ:=(1+|hueW P.par.R.L (guineas P s)*yInvoice c.b|)^2

lemma descending
 (g:1 ≤ d.M) (p:14*meterC Y'*(4*((walkF Y':ℝ)+addgap H))^4 ≤ 1) :
 Sustained H w✤ (wireG R✽) (drew t) (take P s q k)
   (Real.exp (bauble P s d.v)) (crowning P c s):=by
 refine ⟨?_,?_⟩
 · intro A e x
   obtain ⟨a,b,u,v,_,w,_⟩:=e
   rw [w, Pi.mul_apply]
   refine (norm_mul_le ..).trans ?_
   have E:ι' ≤ 1+|ι'|:=le_trans (le_abs_self _) (by linarith)
   unfold crowning;rw [pow_two]
   exact mul_le_mul (((u.paid t).2 _).trans E) (((v.paid t).2 _).trans E) (by positivity)
     (by positivity)
 intro L w z
 obtain ⟨J,v,u,a,b⟩:=feathers t w
 rw [a]; refine le_trans (garland t g v (fun x h=>(b x h).1)) ?_

 rw [u,laserRent,←Real.exp_nat_mul]
 have x:0<W✽:=lt_of_lt_of_le two_pos t.reef.crystal.width
 have e:Real.exp (((2*L.length:ℕ):ℝ)*Real.log (2/W✽)) = (2/W✽)^(2*L.length) :=by
   rw [Real.exp_nat_mul,Real.exp_log (div_pos two_pos x)]

 rw [←e,←Real.exp_add]
 apply Real.exp_monotone
 have j: sites (N') ≤ (L.length:ℝ)*(4*((walkF Y':ℝ)+addgap H))^4:=by unfold sites; exact_mod_cast z.2
 have a:=mul_le_mul_of_nonneg_left j (show 0≤14*meterC Y' from mul_nonneg (by norm_num) (coin_pos ..).le)
 have b:=mul_le_mul_of_nonneg_left p (Nat.cast_nonneg (α:=ℝ) L.length)
 push_cast
 unfold bauble
 linarith only [a,b,Nat.cast_nonneg (α:=ℝ) L.length]
#print axioms descending
