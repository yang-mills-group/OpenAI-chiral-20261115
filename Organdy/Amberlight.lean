import Organdy.Dolce
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



def Blazing (P:Spine)(c:Cuts)(s:ℕ)(f:Buffered.Family P.calibration):Prop:=
 ∃ z:P.Test,z.val=f∧
   ∀ r,reach (guineas P s) r→
    ∀ j,∀h:P.Spectrum0 j,∀ a β:ℝ, guineas P s/2 ≤ β →
      gleamδ c.γ * (a/(β* distanceP r^4))^2≤
       glitz P z h s r a

variable {P:Spine}{s:ℕ}{c:Cuts}
local notation "H" => P.calibration
local notation "gu" => guineas P s
local notation "w✽" => webX (gu)
local notation "g'" => (shaft P s+6)
local notation "A'" => premium argent c.γ
local notation "ℰ"=> meterC (gu)
local notation "h'"=> knock (gu)
local notation "S'"=> station P s

local notation "w✤" => walkF (gu)
local notation "ε₁" => yieldt (gu)


variable {I:Type}{u:Ultrafilter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "uf" => (↑u:Filter I)
local notation "W" => raw P s i k X
local notation "G'" => (∀v,Treasure (tunnel P s i v))

abbrev planted(r:ℕ):=4*distanceP r

variable (p:Parade (↑u:Filter I) P c d s i k X F x)
 (m:AmberMood P c s)

lemma planted_eq(r:ℕ):planted r=((2*r:ℕ):ℝ):=by unfold planted distanceP;push_cast; ring

include m in
lemma planted_plait (r:ℕ)(q:reach gu r):
  0<distanceP r∧ Plait w✽ (2*r):=by

 have w:0<w✽:=(show (0:ℝ)<8 from by norm_num).trans_le m.aisle.gw
 have t:0<distanceP r := (half_pos (pow_pos w _)).trans_le q.1
 obtain ⟨q1,q2⟩:=q
 refine ⟨t,?_,?_⟩
 · rw [←planted_eq,planted];linarith only [t,q1]
 rw [←planted_eq,planted,show (102:ℕ)=1+101 from rfl,pow_add,pow_one]
 linarith only [q2, mul_le_mul_of_nonneg_right m.aisle.gw (pow_pos w 101).le]


include m p
lemma beaconR (Z:P.Register)(z:P.Test)(h:z.val=x .horn)(r:ℕ)(e:Plait w✽ (2*r))(j:Axis)(w:P.Spectrum0 j):
   A'/2 ≤ (planted r)^8 * glitz P z w s r gu:=by
 obtain ⟨A,q⟩:=p.review
 obtain ⟨J,t⟩:=highs (u:=u) q

 rw [planted_eq]
 obtain ⟨v,b⟩:=t (2*r)
 have p1:=hallmark m p q e b
 have p2:=sees_light m p q Z z h w e b v
 have p3:=m.ocean _ e
 let d:=((2*r:ℕ):ℝ)
 have p4:=mul_le_mul_of_nonneg_left (abs_le.mp p2).1 (by positivity:0≤d^8)
 linarith only [p1,p4,p3]

theorem amberlight(Z:P.Register):
 Blazing P c s (x .horn):=by
 let z:P.Test:= ⟨_, broadCompile _ _ (p.pins .horn).1.queue.toBe⟩
 refine ⟨z,rfl,?_⟩
 intro r e j w a β b
 obtain ⟨v,n⟩:=planted_plait m r e
 have h:=beaconR p m Z z rfl r n j w
 have y:=m.plus
 rw [show a=a/gu*gu from (div_mul_cancel₀ a y.ne').symm, fraction_glitz,
    div_mul_cancel₀ a y.ne']
 have g:0<planted r:=by unfold planted;positivity
 apply (mul_le_mul_iff_left₀ (pow_pos g 8)).mp
 exact (equalBudget y m.γpos b v).trans ((mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq
    (by ring))
#print axioms amberlight
