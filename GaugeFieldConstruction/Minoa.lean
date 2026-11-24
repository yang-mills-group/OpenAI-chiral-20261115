import GaugeFieldConstruction.Canna
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Esther
import GaugeFieldConstruction.Polder
import GaugeFieldConstruction.Sotto
import GaugeFieldConstruction.Soapstone
set_option autoImplicit false
set_option maxRecDepth 1300
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 180000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {k:Side}{d:ℕ}{x y:Cover}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
-- θ.Ship manifestation $pR`. Tick frame transport from **fixed** Reifier to any actual $l$.
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts YM.GaugeFieldConstruction
local notation "Sp"=>Cauchy.Spin
open scoped Kronecker
namespace Violets
open ArtCart Simmer Py.Rate.LocalLimit.Papal.FrameP
variable (n k x)
abbrev HumpW (j:ArcK x):ℂ:= tagR k j.1.val
lemma humpQ (j:ArcK x): HumpW k x j* HumpW k x j=1:=fee_one _
lemma feesA (t:Bool)(i j:ArcK x): feeV k (bet0 _ t i j)= HumpW k x i*HumpW k x j:=by cases t; exact mul_comm ..; rfl
abbrev Γpay (i j:ArcK x):= HumpW k x i*HumpW k x j
abbrev νTune (F:Paper n)(φ: Confab (Θk n x))(i:crestCard x)(U:Genre):ℂ :=crownx U F (hereV n i) (Θk n x) φ
def FoldD (F:Paper n)(i j:ArcK x)(U:Genre)(φ:Confab (Θk n x)):= Γpay n x i j*(νTune n x F φ (bet0 _ true i j) U-νTune n x F φ (bet0 _ false i j) U)
abbrev σV (b:Bool)(j:ArcK x) := hereF k (Mct b j)
lemma σΨ (b:Bool)(i:ArcK x): σV k x b i ∈ Tset k ↔ b=false:=by
 rw [κv]; change Cauchy.band b i.2.1∈plusHalf ↔ _; cases b; exact iff_of_true (slotA _).1 rfl; exact iff_of_false (slotA _).2 (by decide : true ≠ false)
def grantR (i j:ArcK x): Seated (Tset k) := ⟨σV k x false i,σV k x true j,(σΨ k x false i).2 rfl,(fun h=>(by decide : true ≠ false) ((σΨ k x true j).1 h))⟩
lemma crestSum (F: Paper n)(T: Tuned F)(i j:ArcK x) (U:Genre)(φ:Confab (Θk n x))(b:Bool) : let X:= bet0 _ b i j; let L:=grantR k x i j; dot_Q (hereV k X) = if b then surge L else - surge L:=by
 intro X L; let c:=L.cv; let r:= L.rv; have he: c ≠ r:=fun h=> L.rvB ((congrArg (· ∈ Tset k) h).mp L.cvB)
 cases b
 · change takeF r*put c = -surge L; rw [surge,(Root_hi k L.cv).1,(Root_hi k L.rv).2]; apply eq_neg_of_add_eq_zero_left; change antiB (takeF r) (put c)=0; rw [antiB,mixed r c,if_neg (Ne.symm he)]
 change put c*takeF r=surge L; rw [surge,(Root_hi k L.cv).1,(Root_hi k L.rv).2]
lemma trivial_w (F:Paper n)(i: crestCard x)(h:F (hereV n i)=0) (U:Genre)(φ:Confab (Θk n x)):crownx U F (hereV n i) (Θk n x) φ=0:=by
 rw [crownx, entry_H,h,show PressAt (0:Lit n)=fun _=>0 from rfl, iteratedFDeriv_fun_zero]; change (↑U.orderB.factorial:ℝ)⁻¹ • (0:ℂ) =0; simp
abbrev bindR (F:Paper n)(k:Side)(φ:Confab (Θk n x))(U:Genre): FC (Single k):=∑ i,∑ j,(Γpay k x i j*FoldD n x F i j U φ) • surge (grantR k x i j)
lemma carobi (F:Paper n)(T:Tuned F)(U:Genre)(φ: Confab (Θk n x)): LarkD k x F U φ = νTune n x F φ none U • (1:FC (Single k)) + bindR n x F k φ U:=by
 let V:= fun i: crestCard x=> (Keyfee n k x i*νTune n x F φ i U) • dot_Q (hereV k i); change ∑ i,V i=_; rw [sortIQ x V ?_]; swap
 · intro i p; unfold V Keyfee; rw [show νTune n x F φ i U= _ from trivial_w n x F i (Classical.byContradiction fun u=> p (mapStem F T _ _ u)) U φ, mul_zero,zero_smul]
 rw [show V none=νTune n x F φ none U • (1:FC (Single k)) from ?_]; swap; · unfold V; change (((1:ℂ)*1)*_) • _=_; rw [one_mul,one_mul]; rfl
 congr 1; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>by
    unfold V FoldD; rw [show dot_Q (hereV k (bet0 x true i j)) =_ from crestSum n k x F T i j U φ true,show dot_Q (hereV k (bet0 x false i j))=_ from crestSum n k x F T i j U φ false,if_pos rfl,if_neg (by decide:false≠true), Keyfee,Keyfee,feesA, feesA, feesA, feesA,smul_neg,←neg_smul,←add_smul]; congr 1; unfold Γpay; ring -- tune arg order
lemma gauge_lark (F:Paper n)(φ:Confab (Θk n x))(T:Tuned F)(p:Solon Genre.gauge F):LarkD k x F .gauge φ= νTune n x F φ none .gauge • (1:FC (Single k)):=by
 rw [carobi n k x F T]; unfold bindR; rw [sum_eq_zero, add_zero]; intro i _; apply sum_eq_zero; intro j _; unfold FoldD νTune; rw [trivial_w n x F (bet0 x true i j) (p.1 _) .gauge φ,trivial_w n x F (bet0 x false i j) (p.1 _) .gauge φ,sub_self,mul_zero,mul_zero,zero_smul]
lemma ferm_lark (F:Paper n)(φ:Confab (Θk n x))(T:Tuned F)(u: F none=0)(U:Genre):LarkD k x F U φ= bindR n x F k φ U:=by
 rw [carobi n k x F T, show νTune n x F φ none U= 0 from trivial_w n x _ _ u U φ,zero_smul,zero_add]
abbrev AngleP (t:Bool)(i:ArcK x):= hereF n (Mct t i)
abbrev SipF (F:Paper n)(v w:ArcK x):ℂ:= Γpay n x v w* orbitPH (AlphaY F 1) (AngleP n x false v) (AngleP n x true w)
lemma νP (F:Paper n)(φ: Confab (Θk n x))(i:crestCard x):νTune n x F φ i .pure= F (hereV n i) 1:=by
 unfold νTune crownx; rw [Genre.orderB, entry_H, iteratedFDeriv_zero_apply]; unfold PressAt; rw [G07.at_zero_increment]; simp
lemma FoldF (F:Paper n)(φ: Confab (Θk n x))(i j:ArcK x):FoldD n x F i j .pure φ= SipF n x F i j:=by
 unfold FoldD SipF; rw [νP,νP,show orbitPH (AlphaY F 1) = _ from (bpu_T ..).1]; change _*(F _ _-F _ _)= _*(thrustA F _ _ _+- F _ _); rw [sub_eq_add_neg]; rfl
abbrev SipM (F:Paper n)(φ:Confab (Θk n x))(v w:ArcK x):ℂ:= Γpay n x v w* Paint (AlphaY F) (caster (Θk n x) φ) (AngleP n x false v) (AngleP n x true w)
lemma νM (F:Paper n)(φ: Confab (Θk n x))(i:crestCard x):νTune n x F φ i .mixed= fderiv ℝ (PressAt (F (hereV n i))) 0 (caster (Θk n x) φ):=by unfold νTune crownx; rw [Genre.orderB, entry_H, iteratedFDeriv_one_apply]; simp
lemma Oscar_P (F:Paper n)(i j:ArcK x): portE (AlphaY F) (AngleP n x false i) (AngleP n x true j) = PressAt (F (hereV n (bet0 _ true i j)))-PressAt (F (hereV n (bet0 _ false i j))):=funext fun A=>by rw [ModuleB.portE,(bpu_T ..).1]; change _+ -_= (_:ℂ)-_; rw [sub_eq_add_neg]; rfl
lemma FoldM (F:Paper n)(φ: Confab (Θk n x))(i j:ArcK x)(p:ready_D F):FoldD n x F i j .mixed φ= SipM n x F φ i j:=by
 unfold FoldD SipM; rw [νM,νM,Paint, Matrix.of_apply, Oscar_P n x F]; rw [fderiv_sub (p _ |>.differentiableAt (by simp)) (p _ |>.differentiableAt (by simp))]; rfl
-- papaya θ Slot cancellation at arbitrary Φ *** after projection/support cT from reference***
lemma diagonalM (F:Paper n)(φ:Confab (Θk n x))(t:F∈Glamor (Θk n x) .mixed v)(w:300<n.val)(K: Kea.Pad 4 k)(M':Male):
 ∑ i:ArcK x,∑ j:ArcK x,(Γpay k x i j*SipM n x F φ i j)* Pacts.QueenP (boardC k 4 M') (pinShift k 4 M') (pinBack k 4 M') (grantR k x i j) (grantR k x i j) = 0 :=by
 let X:=caster _ φ; let P:=AlphaY F; let V:=Paint P X; let CY(a b:Cover)(i j:Sp):ℂ:= (Next.Free.stageVolume k)⁻¹* ∑ u:Site k,tellerP a b i j k M' u
 have hp (i j:ArcK x): (Γpay k x i j*SipM n x F φ i j)* Pacts.QueenP (boardC k 4 M') (pinShift k 4 M') (pinBack k 4 M') (grantR k x i j) (grantR k x i j)= if j.2.2=i.2.2 then CY i.1.val j.1.val i.2.1 j.2.1*SipM n x F φ i j else 0:=by
    rw [mul_right_comm, show Γpay k x i j* Pacts.QueenP (boardC k 4 M') (pinShift k 4 M') (pinBack k 4 M') (grantR k x i j) (grantR k x i j)=if j.2.2=i.2.2 then CY i.1.val j.1.val i.2.1 j.2.1 else 0 from matΘ (M:=M') K i.1.val j.1.val i.2.1 j.2.1 j.2.2 i.2.2, ite_mul,zero_mul] -- tune arguments meta hp
 simp_rw [hp]; rw [Fintype.sum_prod_type]; apply sum_eq_zero; intro a _; rw [Fintype.sum_prod_type]; apply sum_eq_zero; intro i _; let q(a:ArcK x)(j:ArcK x):ℂ:= (if j.2.2=a.2.2 then CY a.1.val j.1.val a.2.1 j.2.1* SipM n x F φ a j else 0); change ∑ s:SU.Slot, ∑ j:ArcK x,q (a,i,s) j=0
 simp_rw [Fintype.sum_prod_type (fun j:ArcK x =>_), Fintype.sum_prod_type (α₁:=Sp) (α₂:=SU.Slot)]; rw [sum_comm]; apply sum_eq_zero; intro b _; rw [sum_comm]; apply sum_eq_zero; intro j _
 have hx := traced_E F _ _ t w (wrap n a.val) (wrap n b.val) (Cauchy.band false i) (Cauchy.band true j) X; dsimp only [q]; simp_rw [Finset.sum_ite_eq',mem_univ,ite_true,SipM]; change ∑ s:SU.Slot,CY a.val b.val i j*( (tagR n a.val*tagR n b.val) * (V (αslot _ _ s) (αslot _ _ s)))=0; rw [←Finset.mul_sum,←Finset.mul_sum]; change CY a.val b.val i j*( (tagR n a.val*tagR n b.val) * ∑ l:SU.Slot, Paint (AlphaY F) X (αslot (wrap n a.val) (Cauchy.band false i) l) (αslot (wrap n b.val) (Cauchy.band true j) l) )= _; rw [hx,mul_zero,mul_zero] -- tune
#print axioms carobi
#print axioms diagonalM
end Violets
end ArtCart
end MastTin
end YM.CF.XGarden
end
