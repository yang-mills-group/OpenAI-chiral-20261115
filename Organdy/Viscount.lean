import Organdy.Busby
import Organdy.Sparklers

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

open Hive Levier Urn


variable {P:Spine}{c:Cuts}{s:ℕ}
 {I:Type}{l:Filter I}{d:Stores}{i k:I→ℕ}
 {X:Suits P s i}{F:PackE I P}{x:Lot P}
local notation "Hp"=> P.calibration
local notation "B"=> shaft P s
local notation "Hₛ"=>station P s
variable (p:Parade l P c d s i k X F x)

abbrev labeled (j:Pin):P.Test:=⟨x j, broadCompile _ _ (p.pins j).1.queue.toBe⟩

lemma paidStar [l.NeBot]:
  pauldron Hp (labeled p .stone)= labeled p .horn:=by
  apply Subtype.ext;rw [collarVal]
  have a: (fun v=>hatP (modal P c s (i v) (k v) (X v) .stone)) =
      (fun v=>modal P c s (i v) (k v) (X v) .horn):=funext fun _=> hatReads ..
  have b:= (p.pins .stone).1.spangled
  rw [a] at b
  exact b.accord (p.pins .horn).1 (Eventually.of_forall fun v=>(p.vintage v).stock.hosp)

open Salt
local notation "hue'"=> (hue P s:ℂ)
local notation "Yᵐ"=> (hue' • untreated P c s i k X)
include p

lemma soldSpangles
  (z:P.Test)(e:z.val=sparkle P s x)
  (u:Signed):
  Bought l P c s i k
   (fun r=>hmMark (incX u) (Yᵐ r))
   (fun r=>flick (incX u) ((hue' • yStart F) r)) (flounce Hp (incX u) z):=by
 constructor
 · exact (bought p z e).tagged.tangled _
 apply Eventually.of_forall
 intro r
 let N:=tunnel P s i r
 let f:=fast P s (i r) (k r)
 let S:= Porch f (0:Site N)
 let j:= polestar N u
 let y:= Yᵐ r
 let t:= occupant j (0:Site N)
 have g:node t=boxA j (node 0):=Shape.nodex ..
 have a:node t ∈ actY j⁻¹ S:=by
    rw [g,actY, sitU]
    apply mem_map_of_mem _ (halo_subset _ _ (mem_singleton_self _))
 let l0:Blush N:=⟨t, voltaM j⁻¹ y, actY j⁻¹ S,node t⟩
 refine ⟨l0, ⟨a,_,_,Boarding.moved (p.slot r) _ (by change boxA j⁻¹ (node t)=_;rw [g,sitU, Equiv.symm_apply_apply])⟩,?_,?_⟩
 swap
 · rw [hmMark,polished]
 intro v h
 change v ∈ actY j⁻¹ S at h
 rw [actY,sitU] at h

 obtain ⟨w,l,rfl⟩:=mem_map.mp h
 have t₀:=pole_zero (N:=N) u
 change separation _ (boxA j w)≤_
 rw [show (0:Seat N)=boxA j 0 from t₀.symm, sitT]
 obtain ⟨z,h,g⟩:=halo_spec.mp l
 rw [mem_singleton.mp h,home0] at g
 apply (separation_triangle 0 1 w).trans ((add_le_add sep1 g).trans _)
 have f₀:f.B=shaft P s:=(p.vintage r).reef.clearing.radius
 change 1+2*f.B≤_
 omega

omit p

lemma tracedHat {K:Calibration}{r:ℝ}(f:Dome K)
 (A:Dome K→ℂ)
 (m:∀c:ℂ,∀ x,‖A (c • x)‖=‖c‖*‖A x‖)
 (s:∀ x y,A (x+y)=A x + A y)
 (t:∀ u:Signed,‖A (flounce K (incX u) f)‖≤ r):
 ‖A (pauldron K f)‖≤ r:=by
 let a:Dome K →+ ℂ:=AddMonoidHom.mk' A s
 rw [showtime,m]
 have e:‖A (∑ u:Signed,ebony u • flounce K (incX u) f)‖≤ ∑ _u:Signed, r:=by
   change ‖a (∑ u:Signed,ebony u • flounce K (incX u) f)‖≤ _
   rw [map_sum]
   apply le_trans (norm_sum_le ..)
   apply sum_le_sum
   intro u _
   change ‖A (ebony u • _)‖≤_
   rw [m,norm_ebony,one_mul];exact t u
 refine (mul_le_mul_of_nonneg_left e (norm_nonneg _)).trans ?_
 rw [sum_const,card_univ,nsmul_eq_mul]
 unfold feeD
 rw [norm_inv, Complex.norm_natCast,inv_mul_cancel_left₀ (by exact_mod_cast Fintype.card_ne_zero)]

include p
theorem shooting (Z:P.Register) [l.NeBot]
 (m:AmberMood P c s)(t:yieldt (guineas P s)≤1)(b:1≤d.M)
 (f:P.Test)(e:f.val=sparkle P s x): Orchid P s d.v (pauldron Hp f):=by
 intro r a j w
 let A:=P.singleState j s w
 let V:=aureole Hp timeAxis (-(r:ℤ))
 let f':=pauldron Hp f
 refine tracedHat f (fun x=>A (V x * f')) (fun u x=>?_) (fun x y=>?_) (fun g=>?_)

 · rw [map_smulₛₗ,smul_mul_assoc,map_smul,norm_smul, starRingEnd_apply, norm_star]
 · rw [map_add,add_mul,map_add]
 let y:=flounce Hp (incX g) f
 refine tracedHat f (fun x=> A (V y * x)) (fun u x=>?_) (fun x y'=>?_) (fun v=>?_)
 · rw [mul_smul_comm, map_smul, norm_smul]
 · rw [mul_add,map_add]
 obtain ⟨u⟩:= nonempty_of_neBot l
 rw [←curtains _ (two_pos.trans_le (p.vintage u).reef.crystal.width)]
 exact controlled p.vintage p.rate (soldSpangles p f e g)
        (soldSpangles p f e v) (accessible m a).1 (accessible m a).2 m t b Z w

#print axioms shooting
#print axioms paidStar
