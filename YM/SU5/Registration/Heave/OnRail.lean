import YM.SU5.Registration.Heave.StillFront
import SatinThinFusionSales
import YM.SU5.Registration.Rise.AtFull
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six

/-!
# Through the actual narrow seam
Exact operator formula at width V of stitch purchase (slightly broader than either test).
Use additional pad DURING real comparison of the front factor. Do the step all on H
because of the P-operator `linked` (do not pass to G on general products).
-/
namespace Spine
variable (P:Spine)(x:P.Spectrum0 3)(A:P.Apron)(Z:Lead.Clan)(s n:ℕ)
local notation "j"=>(3:Axis)
local notation "B"=> P.stitchApron Z A s n
local notation "c"=> A.allowance P 3
local notation "u"=> A.zoom P s j
local notation "L"=> timeMesh P.par
local notation "M" s:max u0:max=> whenly (timeMesh P.par) s u0
local notation "F"=> P.thinMat Z s n
local notation "xQ"=> (B).u j
local notation "ξ" => P.advocate 3 x 3
-- BELOW take just Spectrum0 x (same as ξ defeq? actually not!). Reserve xvar = any character on 3 in this file.
local notation "V"=>P.ColorHil j x
local notation "E"=> (P.physicalEnergy 3 x).E
local notation "xW"=>(B).allowance P 3
lemma stitch_quote : (B).u j=u+3*u+ (F).u j :=rfl
variable (g:A.s≤ s) (U:(P.thinMat Z s n).allowance P 3 ≤ A.allowance P 3)
local notation "v"=> xQ-(u+u+(u+u))
local notation "Δ"=> (xW - (c+c+(c+c)))
local notation "A'"=> A.engine P j x
local notation "F'"=> P.stageH 3 x (P.thinMat Z s n) c c
include g
private lemma paid_room : xW=(c+c+(c+c))+(F).allowance P 3:=by rw [← P.zoomMoney j A s g]; change M s xQ= _; rw [P.stitch_quote A Z s n]; rw [show (u)+3*u+(F).u j=u+u+(u+u)+(F).u j from by omega]; simp only [when_add]; rfl
lemma held_width : c+c+(c+c) ≤ (P.stitchApron Z A s n).allowance P 3:= by rw [P.paid_room A Z s n g]; exact le_add_of_nonneg_right (by positivity)
-- exact multiplication at integer ticks
local notation "A₀"=> P.shifts j ((u:ℕ):ℤ) (A.full P s)
local notation "F₀"=> P.shifts j ((u:ℕ):ℤ) ((F).full P s)
include U
private lemma seam_base : ∃ f:P.InCase 3 s (u+u+(u+u)) (B).F, f.charges x (by have he:= A.zoomP P j s; omega)= A'* F':=by
 let ℓ:=u; let h₁:= A.zoomP P j s; let h₂:= add_pos h₁ h₁
 have h:(F).zoom P s j ≤ ℓ:=by
    rw [← P.zoomMoney j A s g] at U; exact ((F).zoom_at P j).trans_le ((when_le (timeMesh P.par) ..).1 U) -- notation
 let i:= A.anchored P j s g; let p:= (F).entrusted P j s le_rfl ℓ ℓ h h
 have he:p.charges x h₂= F':=by rw [←P.zoomMoney j A s g]; exact (F).entrusted_pays P j x s le_rfl _ _ h h _
 let f:= i.linked p; have ht:A₀ * P.shifts j ((↑(ℓ+ℓ:ℕ)):ℤ) F₀=(B).F:=by
    rw [show (F).full P s=(F).F from (F).full_at P,P.shifts_sum]; change _= A₀ * P.shifts 3 (P.fusionFare A s:ℤ) (F).F; rw [show (((ℓ+ℓ:ℕ):ℤ)+((u:ℕ):ℤ))=(↑(P.fusionFare A s):ℤ) from (by unfold fusionFare ℓ; omega)]
 let k:P.InCase 3 s (ℓ+ℓ+(ℓ+ℓ)) (B).F:=by rw [←ht]; exact f
 exact ⟨k,(k.charges_eq x f rfl rfl ht.symm _).trans ((i.charges_linked x p h₂ h₂).trans (congrArg₂ (· * ·) (A.retains P j x s g) he))⟩
lemma stitch_engine : (P.stitchApron Z A s n).engine P 3 x= E xW * (A'* F') * E Δ:=by
 have hV:= stitch_quote P A Z s n; have h:= P.held_width A Z s n g; let p:=(B).anchored P j s le_rfl; let z:=(B).zoom P s j; let fp:=(B).zoomP P j s; let hp:=add_pos fp fp
 have h₀:z=xQ:= (B).zoom_at P j
 obtain ⟨f,ht⟩:= seam_base P x A Z s n g U; let i:= f.padIn xQ (v)
 let y:= u+u+(u+u); let fV:= v
 have hq:fV+y=xQ:=by unfold fV y; omega
 have hz: ((B).allowance P 3) = M s z:= h₀.symm ▸ rfl -- try rw
 have he:p.charges x hp = i.charges x (by omega):= p.charges_eq x i rfl (by change z+z=xQ+(u+u+(u+u))+(v); omega) (by rw [show ((B).full P s)=(B).F from (B).full_at P, show ((B).zoom P s j)=xQ from h₀]) _
 have ha: M s fV= Δ:=by
    rw [← P.zoomMoney j A s g]; change _=(M s xQ)-_; have he:(M s fV)+(M s y)= M s xQ:=by rw [←when_add,hq]
    rw [← show M s y=(M s u)+(M s u)+((M s u)+(M s u)) from by unfold y; simp [when_add],←he,add_tsub_cancel_right]
 exact (B).retains P j x s le_rfl|>.symm.trans (he.trans ((f.charges_pad x xQ fV _).trans (by rw [ht,ha]; rfl)))
local notation "ζ"=> (purePrice Z:ℂ)
local notation "θ!" => P.stitchApron Z A s n
local notation "k!" => c+c+(c+c)
lemma unseam (w:ℝ≥0)(e:(P.stitchApron Z A s n).allowance P 3 ≤ w) :
    ‖P.stageH 3 x (P.stitchApron Z A s n) w w-ζ • P.stageH 3 x A (w+c) (w-c)‖ ≤ ‖A'‖*‖P.printGaps 3 x Z s n c c‖:=by
 let δ:=c; have ht:0 < δ:= A.width_p P 3; have he:= (P.held_width A Z s n g).trans e; change k!≤ w at he
 have hg: xW- (k!)+(w-xW)=w-k!:= by rw [add_comm]; exact tsub_add_tsub_cancel e (P.held_width A Z s n g)
 have hx: ∀ (t t':ℝ≥0), E t* E t'= E (t+t'):= fun t t'=>((P.physicalEnergy 3 x).time ..).symm
 have hp:P.stageH 3 x (θ!) w w= E w * (A' * F') * E (w-k!):=by
    change E (w-xW) * (B).engine P 3 x * E (w-xW)= _; rw [stitch_engine P x A Z s n g U,← P.heater_both,tsub_add_cancel_of_le e,hg]
 -- collapse center by shift δ. rr - 4δ remainder + 2δ.
 have h1: c+c ≤ w:=(le_add_of_nonneg_right (show 0≤c+c by positivity)|>.trans he)
 have h:P.stageH 3 x A (w+c) (w-c) = E w * (A' * E (c+c)) * E (w-k!):=by
    unfold stageH; rw [add_tsub_cancel_right,tsub_tsub,← mul_assoc (E w),mul_assoc (E w*_),hx,show c+c+(w-k!)=w-(c+c) from ?_]
    exact (by
       rw [add_comm, show w-(k!)= w-(c+c)-(c+c) from (tsub_tsub ..).symm,tsub_add_cancel_of_le ?_];
       exact (le_tsub_iff_right h1).mpr he)
 rw [hp,h]
 rw [peelH V (E w) A' F' (E (c+c)) (E (w-k!)) ζ]
 exact (P.heater_norm ..).trans (norm_mul_le _ (P.printGaps j x Z s n δ δ))
where peelH (G_:Hilbert) (e f b d y:G_.Op)(ζ':ℂ) : e*(f*b)*y- ζ' • (e*(f*d)*y)=e*(f*(b-ζ' • d))*y:=by rw [mul_sub,mul_sub,_root_.sub_mul]; rw [Algebra.mul_smul_comm ζ' f,Algebra.mul_smul_comm ζ' e,Algebra.smul_mul_assoc]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.stitch_engine
#print axioms Spine.unseam
