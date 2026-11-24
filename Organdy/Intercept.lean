import Organdy.Piety
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




-- Wide credit inclusive. Kℓ? K(P) fixed.
def widthR(P:Spine):=8*P.calibration.B.val
def LimitB(P:Spine):ℝ:=100 * (1+widthR P+P.calibration.ℓ :ℕ)
structure Grand(P:Spine)(c:Cuts)(s:ℕ):Prop where
 price:Pied P c s
 wide:Aisle (guineas P s) (LimitB P)
lemma grandiose {v:ℝ}{P:Spine}{c:Cuts} (y:c.legacy P)
 (Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s≤P.run.uv k→ ShelterCost v P.run s i k):
 ∀ᶠ s in atTop,Grand P c s:=
 ((piety y Z).and ((turnover P.par).eventually (aisleWide (LimitB P)))).mono fun _ z=>⟨z.1,z.2⟩

def NextTick(P:Spine)(r:ℕ):=widthR P*r

-- final public part
def afterimage (P:Spine)(s r:ℕ)(z:P.Test)(h:P.Spectrum0 timeAxis)(a:ℝ):ℝ:=
 ‖P.singleState timeAxis s h ((a:ℂ) • z)‖^2 -- squared vac
def LoneBeacon(P:Spine)(c:Cuts)(s:ℕ)(z:P.Test):Prop:=
 ∀ r,reach (guineas P s) r→
    ∀h:P.Spectrum0 timeAxis,∀ a β:ℝ, guineas P s/2 ≤ β →

      gleamδ c.γ * (a/(β* distanceP r^4))^2 ≤
        glitz P z h s r a - afterimage P s r z h a

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

local notation "w₁" => (widthR P)
lemma Grand.path (g:Grand P c s) (r:ℕ)(h:reach gu r):
  2*r ≤ NextTick P r ∧ Plait w✽ (2*NextTick P r) ∧
  (H).ℓ+4*(shaft P s)+6 ≤ r :=by
 have w:=g.wide
 have v:8≤w₁:=Nat.le_mul_of_pos_right 8 P.calibration.B.property
 have h₁ := w.gw
 unfold LimitB at h₁; push_cast at h₁
 have w0:0≤ w✽:=by linarith only [h₁,Nat.cast_nonneg (α:=ℝ) w₁,
    Nat.cast_nonneg (α:=ℝ) P.calibration.ℓ]
 have t:=planted_plait g.price.mood r h
 obtain ⟨p,q⟩:=h
 unfold NextTick
 have n:2*r≤w₁*r:=by gcongr;omega
 have i:8*(w₁:ℝ)≤w✽:=by
   linarith only [h₁,Nat.cast_nonneg (α:=ℝ) w₁,Nat.cast_nonneg (α:=ℝ) P.calibration.ℓ]
 refine ⟨n,⟨t.2.1.trans (Nat.cast_le.mpr (by omega)),?_⟩,?_⟩

 · push_cast
   rw [show (102:ℕ)=1+101 from rfl,pow_add,pow_one]
   unfold distanceP at q
   linarith only [mul_le_mul_of_nonneg_left q (Nat.cast_nonneg (α:=ℝ) w₁),
            mul_le_mul_of_nonneg_right i (pow_nonneg w0 101)]

 · unfold distanceP at p
   have y:w✽^2 ≤ w✽^99:=pow_le_pow_right₀
     (le_trans (by norm_num: (1:ℝ)≤8) g.price.mood.aisle.gw) (by norm_num)
   have a:=g.price.mood.aisle -- stronger depth too
   have b:(shaft P s:ℝ)+20≤w✽:=a.depth
   apply (Nat.cast_le (α:=ℝ)).mp; push_cast
   linarith only [b,h₁,Nat.cast_nonneg (α:=ℝ) w₁,
       mul_le_mul_of_nonneg_right a.gw w0, p, y]

lemma inRegion(r:ℕ)(h:(H).ℓ+4*(shaft P s)+6 ≤ r) :
 Tower.region timeAxis (-(r:ℤ)) (H).ℓ S':=by
 intro k l
 have v:= (box_test.mp l).1 timeAxis
 change -((4*(shaft P s)+6:ℕ):ℤ) ≤ k _ at v
 omega

variable (m:Grand P c s) (p:Parade (↑u:Filter I) P c d s i k X F x)
include m p
theorem intercepted(Z:P.Register) (z:P.Test)(e:z.val = x .horn) :
 LoneBeacon P c s z:=by
 intro r t w a β y
 obtain ⟨h,v,rh⟩:=m.path r t
 let r':=NextTick P r
 let k':ℤ:= -((2*r:ℕ):ℤ)
 have eq:Heat.gaugeShift P.par.block k'= -(r':ℤ):=by
    change 4*((H).B.val:ℤ) * -(↑(2*r:ℕ):ℤ)= -↑((8*(H).B.val)*r:ℕ)
    push_cast
    ring

 have h1:(H).ℓ+4*(shaft P s)+6 ≤ r':=rh.trans ((by omega:r≤2*r).trans h)
 have u:Tower.region timeAxis (Heat.gaugeShift P.par.block k') (H).ℓ S':=by rw [eq];exact inRegion _ h1

 have c0:=biplanar p m.price Z z e _ _ t v h timeAxis w a β y
 have zM:z∈ bay H S' true:=by
    change InTest H true S' false z.val
    rw [e];exact (p.pins .horn).1.queue.toBe

 have i:=prestissimo P s timeAxis w S' k' ((a:ℂ) • z) ((bay H S' true).smul_mem zM (a:ℂ)) u
 rw [eq] at i
 exact c0.trans (sub_le_sub le_rfl i)
#print axioms intercepted
