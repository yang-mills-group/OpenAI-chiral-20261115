import YM.SU5.WakeFields.Honorarium
import YM.SU5.WakeFields.SpinTable
--! Covariance, mixed V-V with sum of link-independent q, in tangent at four positions (before pure force identification)
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.CrossMoment
open Filter Metric Function MeasureTheory Finset
open Lat Cube Lattice Wilson Fock Satin Py Rate LocalLimit Preparation Yoke
open Jewel.Program Ballad EmberWind
open Hiro (ColorL)
open Onyx (riseX)
open YM.Stationary (Gaia)
open Regis.Circuit Regis.Head.Brecht
open EmberWind.MixedCards MixedCards.Receipt Twah
open Emu -- maybe use SpinTable qualify
open SpinTable (rentBoth rentOne total total2 entry spinPlane body2 body4)
open Window (colors family)
open YM.WakeFields
open scoped Topology BigOperators Matrix MatrixOrder Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

local notation "Ω" => SU.group.ColorIndex
local notation "ϰ" => SU.Slot
local notation "Holo" => Lead.Clan
variable {J:Type*} [Fintype J] (L:List J)(F:J→PlaqAxes)(K:J→DirSpin)(U z:J→Gaia)(D:J→ Ticket)
-- relation D,S covers p and q = staff; m,n = Clan. disjoint implicit. CP2 precursor µ prices.
variable (p q m n:J)(A B: Holo)
variable (h:D p=none) (v:D q=none) (t:D m=some A) (r:D n=some B)
local notation "Y₀" => valueHue F U
local notation "Y₁" => valueSpin K z
abbrev orbit : ℂ:= specter (F p) (F q) (U p-U q)
-- Kernel κ for Position ver. arbitrary K spin, billX self price=0 for K all
abbrev pen (i j:J) := (8:ℂ)*Cordial.billX (z∘Prod.fst) K i j
lemma pen_self(i:J): pen K z i i=0:=by unfold pen Cordial.billX; simp [Onyx.pencil]
lemma story_t : valueSpin K z = SpinTable.germ (V:=SU.Slot) (pen K z) := by
 funext ⟨i,a,u⟩ ⟨j,b,v⟩; unfold valueSpin; unfold SpinTable.germ; cases u <;> cases v
 · rw [Cordial.dcash]; simp
 · rw [Cordial.funds_neg, Cordial.funds]; simp [pen,entry,mul_ite,ite_mul]
 · rw [Cordial.funds]; simp [pen,entry,mul_ite,ite_mul]
 · rw [Cordial.dcash]; simp

lemma veloG (a b:Ω): Ferro.ledger (valueHue F U) [(p,a),(q,b)]=if a=b then orbit F U p q else 0:=by
 rw [Ferro.audit,Ferro.bills_cons,Ferro.dnil,show ([]++[]:Receipt.Deck J)=[] from rfl, Ferro.ledger_nil,mul_one,add_zero]
 unfold valueHue orbit sch; split_ifs <;> simp_all

-- sum bookkeeping generically.
abbrev bothAZ (H:Finset SU.Slot)(W:Finset SU.Slot) (G: SU.Slot → SU.Slot → ℂ) := ∑ i∈H, ∑ j∈ W,G i j
lemma countFold (f:SU.Slot → ℂ) : (∑ A : Holo,∑ i∈colors A, f i)=∑ i,f i:=by
 unfold colors; simp_rw [sum_filter]; rw [sum_comm]; simp
lemma countAll (f:SU.Slot → SU.Slot → ℂ) : (∑ A:Holo,∑ B:Holo,bothAZ (colors A) (colors B) f)= bothAZ univ univ f := by
 have here(A:Holo) : (∑ B:Holo,bothAZ (colors A) (colors B) f) = ∑ i∈colors A, ∑ j:SU.Slot,f i j:=by unfold bothAZ; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [countFold]
 simp_rw [here]; exact countFold _

def pureSum (W W': Finset SU.Slot):ℂ:= 1/16*(1/16)*(bothAZ W W' (fun a b=>body2 (pen K z) m n a a b b))
abbrev paysMatter : ℂ:= pureSum K z m n (colors A) (colors B)
abbrev allMatter:= pureSum K z m n univ univ
lemma pure_combine : (∑ A:Holo, ∑ B:Holo, paysMatter K z m n A B)=allMatter K z m n:=by
 unfold paysMatter allMatter pureSum; simp_rw [←mul_sum]; rw [countAll] -- simp_rw loops select? tune
include t r in
lemma qprice : tariff [m,n] D F K U z= paysMatter K z m n A B:=by
 unfold tariff bus; rw [payPure [n] D [] [] t]; simp_rw [payPure [] D _ _ r]; unfold paysMatter pureSum bothAZ
 simp only [Receipt.cue,Ferro.ledger_nil, story_t,one_mul,mul_sum,mul_assoc]
 rfl
abbrev payColor (ℓ:Ω):ℂ:= total2 (dyeC ℓ) (dyeC ℓ) (body2 (pen K z) p q)
def payStaff : ℂ := orbit F U p q *∑ i:Ω,payColor K z p q i

-- sum-of-summands generic selection of repeated color to get orbit. prog reduce q row first.
include h v in
lemma twinPay (W:Receipt.Deck J→Hiro.Crossing.Story J→ℂ) (H:Hiro.Crossing.Story J) (l:List J) :
    Receipt.cue D W (p::q::l) [] H = ∑ a:Ω,∑ s:Ω,total2 (dyeC a) (dyeC s) (fun i j x y=> Receipt.cue D W l [(p,a),(q,s)] (with2 (with2 H p i j) q x y)) := by
 rw [payMix (q::l) D [] H h]; unfold total2
 apply sum_congr rfl; intro a _; simp_rw [payMix l D _ _ v, mul_sum,←mul_assoc]
 let B (u v w x:SU.Slot) (s:Ω) := dyeC a u v*dyeC s w x*Receipt.cue D W l [(p,a),(q,s)] (with2 (with2 H p u v) q w x)
 let F (i j:SU.Slot)(s:Ω):= ∑ k:SU.Slot,∑ v:SU.Slot,B i j k v s
 change ∑ i:ϰ,∑ j:ϰ,∑ k:Ω,F i j k=∑ k:Ω,∑ i:ϰ,∑ j:ϰ,F i j k
 rw [sum_comm (s:=(univ:Finset Ω))]; apply sum_congr rfl; intro i _; rw [sum_comm]

include h v in
lemma mixPrice : tariff [p,q] D F K U z = payStaff F K U z p q:=by
 unfold tariff bus; rw [twinPay D p q h v] -- maybe `twinPay` arg D before H
 unfold payStaff; rw [mul_sum]; apply sum_congr rfl; intro i _
 rw [sum_eq_single_of_mem i (mem_univ _)]; swap; · intro j _ p; unfold total2; simp [Receipt.cue,veloG,p.symm]
 unfold total2 payColor; simp only [Receipt.cue,veloG,ite_true,total2,mul_sum,story_t]; refine sum_congr rfl fun a _=> sum_congr rfl fun b _=> sum_congr rfl fun k _=> sum_congr rfl fun t _=>?_ ; rw [mul_left_comm (dyeC _ _ _ * dyeC _ _ _)]; rfl
-- four factors fixed A B. keep total-like.
abbrev subtotal (S T: Finset SU.Slot)(ℓ:Ω) := total2 (dyeC ℓ) (dyeC ℓ) (fun a b i j=> bothAZ S T (body4 (pen K z) p q m n a b i j))
lemma sub_bill (ℓ:Ω): subtotal K z p q m n univ univ ℓ= SpinTable.total (dyeC ℓ) (dyeC ℓ) (body4 (pen K z) p q m n):=by unfold subtotal total2 bothAZ SpinTable.total; simp only [mul_sum]
lemma sub_sum (ℓ:Ω) : (∑ A:Holo,∑ B:Holo,subtotal K z p q m n (colors A) (colors B) ℓ) = subtotal K z p q m n univ univ ℓ:=by
 -- general total2 linearity
 let R (a b i j:ϰ):=(body4 (pen K z) p q m n a b i j); unfold subtotal
 let v:=dyeC ℓ; let S (f:ϰ→ ϰ→ ϰ→ ϰ→ℂ):= total2 v v f
 have η (Q:Holo→ϰ→ ϰ→ ϰ→ ϰ→ℂ) : ∑ i:Holo, S (Q i)= S (fun i j k l=> ∑ a:Holo,Q a i j k l):=by
    -- iterate finite num with add rule easier
    suffices h : ∀ f:Finset Holo, ∑ i∈f,S (Q i)=S (fun i j k l=> ∑ a∈f,Q a i j k l) from h _
    intro f; induction f using Finset.induction_on with|empty=> unfold S total2; simp|@insert a f W ih=> rw [sum_insert W]; simp_rw [sum_insert W]; rw [ih]; unfold S total2; simp only [mul_add,sum_add_distrib]
 have he(A:Holo): ∑ B:Holo, S (fun a b i j => bothAZ (colors A) (colors B) (R a b i j)) = S (fun a b i j=> ∑ B:Holo,bothAZ (colors A) (colors B) (R a b i j)) := η _ -- tune inference
 change ∑ A:Holo,∑ B:Holo,S (fun a b i j=> bothAZ (colors A) (colors B) (R a b i j)) = S (fun a b i j=> bothAZ univ univ (R a b i j))
 simp_rw [he]
 calc
   _=S (fun a b i j=> ∑ A:Holo,∑ B:Holo,bothAZ (colors A) (colors B) (R a b i j)):= η _
   _ = _ := by simp_rw [countAll]

def vastBill (S T: Finset SU.Slot): ℂ:= orbit F U p q * (1/16 * (1/16)) * ∑ i:Ω, subtotal K z p q m n S T i
abbrev finalV : ℂ:= vastBill F K U z p q m n univ univ
abbrev duetPrice : ℂ:= vastBill F K U z p q m n (colors A) (colors B)
lemma fleet_price : ∑ A:Holo, ∑ B:Holo, duetPrice F K U z p q m n A B = finalV F K U z p q m n:=by
 unfold duetPrice finalV vastBill; simp_rw [←mul_sum]
 congr 1
 have X(A:Holo): ∑ i:Holo,∑ j:Ω,subtotal K z p q m n (colors A) (colors i) j=∑ j:Ω,∑ i:Holo,subtotal K z p q m n (colors A) (colors i) j:= sum_comm
 simp_rw [X]; rw [sum_comm]; simp_rw [sub_sum]

include h v t r
lemma bothPrice : tariff [p,q,m,n] D F K U z = duetPrice F K U z p q m n A B := by
 unfold tariff bus; rw [twinPay D p q h v];
 unfold duetPrice vastBill; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [sum_eq_single_of_mem i (mem_univ _)]
 · unfold subtotal total2; simp_rw [payPure [n] D _ _ t,payPure [] D _ _ r]; unfold bothAZ; simp only [Receipt.cue,mul_sum,story_t,veloG,ite_true]
   refine sum_congr rfl fun a _=> sum_congr rfl fun b _=> sum_congr rfl fun k _=> sum_congr rfl fun w _=> sum_congr rfl fun x _=> sum_congr rfl fun y _=> ?_
   change _ * (_ * (_ *(orbit F U p q*body4 (pen K z) p q m n a b k w x y)))=_; ring
 intro j _ V; unfold total2; simp_rw [payPure [n] D _ _ t,payPure [] D _ _ r]; simp [Receipt.cue, veloG,V.symm]
omit h v t r
lemma breeze (ℓ:Ω) : rentBoth (dyeC ℓ) (dyeC ℓ)=60:=by
 have he : rentBoth (dyeC ℓ) (dyeC ℓ)= _ := show _= Matrix.trace (Hiro.walkC (Receipt.pad ℓ)*Hiro.walkC (Receipt.pad ℓ)) from sum_congr rfl fun i _=> (Matrix.mul_apply ..).symm
 rw [he,Hiro.walk_square]; simp [Receipt.pad]
lemma plainVoid (ℓ:Ω) : rentOne (dyeC ℓ) = 0:= Hiro.walk_trace (Receipt.pad ℓ)
def interference := -(orbit F U p q) * (1/16*(1/16))* (60*(Fintype.card Ω:ℂ)) * SpinTable.realPlane (pen K z) p q m n
lemma interference_bill : finalV F K U z p q m n - payStaff F K U z p q*allMatter K z m n = interference F K U z p q m n:=by
 let O:=orbit F U p q; let Z(ℓ:Ω) := payColor K z p q ℓ; let A':=pen K z
 let V:= (∑ u:ϰ,∑ v:ϰ,body2 A' m n u u v v); let R:= SpinTable.realPlane A' p q m n; let X (ℓ:Ω):= subtotal K z p q m n univ univ ℓ
 let c:ℂ:=1/16*(1/16)
 have W(ℓ:Ω): X ℓ = Z ℓ * V - 60 * R := by
    have h:= spinPlane (pen K z) (dyeC ℓ) (dyeC ℓ) p q m n (pen_self K z) (plainVoid ℓ); rw [breeze] at h; unfold X; rw [sub_bill]; apply Eq.trans (eq_add_of_sub_eq h); ring -- ring fails Z,V definitions
 change O*c* (∑ i:Ω,X i)-(O*∑ i:Ω,Z i)*(c*V) = -O*c*(60*↑(Fintype.card Ω))*R
 simp_rw [W, sum_sub_distrib,←sum_mul,sum_const,card_univ,nsmul_eq_mul]; ring
#print axioms interference_bill
#print axioms bothPrice
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.CrossMoment
