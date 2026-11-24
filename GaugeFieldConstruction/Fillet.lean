import GaugeFieldConstruction.Muffins
import YM.CF.Moto.Slate
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Work.F03
open Housing ModuleB Flot
namespace HushP
-- No clover necessary for GE ranks. may average orientations (later).
abbrev GateI:= PlaqAxes × Option Axis
def stab(i:GateI): Slot := ⟨(i.2.map Lattice.posDir).toList,i.1⟩
def rock(i:GateI):Cover:=i.2.elim 0 step
def fanP (n:Side)(o:Site n)(i:GateI): Site n:= o+ wrap n (rock i)
lemma rockU(i:GateI): lateral (rock i) ≤1:=by obtain ⟨i,_|i⟩:=i; simp [rock,lateral_zero]; change lateral (step (S:=ℤ) _)≤1; exact (lateral_single _ _).le -- tune
lemma rock_v(o:Skye.Seat n)(i:GateI) : slotFace (stab i) o=(fanP _ o i,i.1):=by
 obtain ⟨a,b|b⟩:=i; · simp [slotFace,stab,fanP,Slot.offset,Lattice.stop,rock];
 simp [slotFace,stab,fanP,Slot.offset,Lattice.stop,rock, add_comm]
lemma feet_v(o:Skye.Seat n)(i:GateI): separation (fanP _ o i) o ≤1:=by
 obtain ⟨a,b|b⟩:=i; · simp [fanP,rock]
 rw [separation_comm]; simpa [fanP,rock] using ((Extra.Iteration.Shapes.visits_dist o (o+step b) [Lattice.posDir b] (by simp [visits])): separation o (o+step b)≤1)
lemma net_v(o:Skye.Seat n)(i: GateI)(t:10<(More n).val) : stem o (fanP _ o i)=rock i:= lift_path (by unfold fanP; abel) (by have h:=rockU i; omega)
lemma stabL (i:GateI): (stab i).length≤10:=by
 obtain ⟨a,b|b⟩:=i <;> simp [Slot.length,stab]
abbrev axy₁(i:GateI):= i.1.val.1
abbrev axy₂(i:GateI):= i.1.val.2
structure Lay where
 f : Gem
 t : Sut
abbrev rowS:= Gem×Sut
def acCue (a: Gem)(i:GateI):ℝ:= a.val (axy₁ i) (axy₂ i)
def veCue (t: Sut)(i:GateI):ℝ:= faceT t (axy₁ i) (axy₂ i) (rock i)
def cue : rowS→ₗ[ℝ] (GateI→ℝ) where
 toFun x i:= acCue x.1 i + veCue x.2 i
 map_add' x y:=by funext i; change x.1.val _ _ + y.1.val _ _ + veCue (x.2+y.2) i= _; unfold veCue faceT; simp only [Submodule.coe_add,Pi.add_apply,Prod.fst_add,Prod.snd_add,smul_add,sum_add_distrib]; unfold acCue; abel
 map_smul' a x:=by funext i; change a • (x.1.val _ _ ) + veCue (a • x.2) i=a • (acCue _ _+veCue _ _); rw [smul_add]; unfold acCue veCue faceT; simp only [Submodule.coe_smul,Pi.smul_apply,smul_sum]; congr 1; apply sum_congr rfl; intro j _; exact smul_comm ..
theorem cue_victory : Injective cue:=by
 suffices h: LinearMap.ker cue=⊥ from LinearMap.ker_eq_bot.mp h; apply le_antisymm _ bot_le; intro x hx; change x=0
 let s:= x.1; let k:= x.2; have hv' := show cue x=0 from hx; have hx(p:PlaqAxes)(i: Option Axis) : s.val p.val.1 p.val.2+ veCue k (p,i)=0:= congrFun hv' (p,i)
 have ht(q:PlaqAxes)(l:Axis): k.val l q.val.1 q.val.2=0:=by
     have he: FlightFlux.advance l (faceT k q.val.1 q.val.2) 0= k.val l _ _ :=congrFun (face_stepT ..) _; rw [←he]; unfold FlightFlux.advance; rw [zero_add]; apply sub_eq_zero.mpr; apply add_left_cancel (show s.val q.val.1 q.val.2+ _=_ from (hx q (some l)).trans (hx q none).symm)
 have hw:k=0:=by
    apply Subtype.ext; funext i j k'; change k.val i j k'=0; rcases lt_trichotomy j k' with h|rfl|h; · exact ht ⟨(j,k'),h⟩ i
    · exact F_slot0 k i j
    rw [F_neg k i j k',show k.val i k' j=0 from ht ⟨(k',j),h⟩ i, neg_zero]
 have hg(q:PlaqAxes):s.val q.val.1 q.val.2=0:=by have hh:=hx q none; rw [hw,show veCue 0 (q,none)=0 from (by simp [veCue,faceT]),add_zero] at hh; exact hh
 apply Prod.ext _ hw; change s=0; apply Subtype.ext; funext i j; change s.val i j=0; rcases lt_trichotomy i j with h|rfl|h
 · exact hg ⟨(i,j),h⟩
 · exact fluxZ s i
 rw [flux_neg s,show s.val j i=0 from hg ⟨(j,i),h⟩,neg_zero]
def creditCue: (GateI→ℝ) →ₗ[ℝ] rowS:= (cue.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr cue_victory)).choose
lemma b_fact(x:rowS): creditCue (cue x)=x:=congr(($((cue.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr cue_victory)).choose_spec)) x)
lemma ac_pack(x:Gem)(i): cue (x,0) i=acCue x i:=by change _+veCue 0 _=_; rw [show veCue 0 i=0 by simp [veCue,faceT],add_zero]
lemma ve_pack(x:Sut)(i): cue (0,x) i=veCue x i:=by change 0+veCue _ _=_; rw [zero_add]
abbrev πon (o:Skye.Seat n)(i:GateI)(t: BudgetPoint)(U:Pane n): SU.group.Color:= (t.threshold)⁻¹ • (stab i).atSite U o
lemma πGauge (i:GateI)(t:BudgetPoint)(U:Pane n)(g:Skye.Seat n → SU.E): πon o i t (Lattice.gauge g U)= SU.group.adjoint (g o) (πon o i t U):=by unfold πon; rw [map_smul]; congr 1; rw [Slot.atSite, Lattice.expandAt_gauge, Work.G06.slot_gauge]; simp [Slot.atSite] -- tune
lemma π_flat (i:GateI)(t:BudgetPoint): πon o i t 1=0:=by
 unfold πon; rw [Work.F02.atSite_curvature]
 have he(o:Site (More n))(w:Walk) : travel (1:Pane n) o w=1:=by
    induction w generalizing o with | nil=>rfl|cons i l ih=> simp only [travel,ih,mul_one]; simp [Step.read]
 rw [he,SU.group.curvature_unit,smul_zero]
lemma F_grade : ∃ H:ℝ,1≤H ∧∀ (n:Side)(o:Skye.Seat n)(i:GateI)(p:BudgetPoint),p.power≤3 → p.order≤6 →Haw p o (Pax o) (πon o i p) H:=by
 obtain ⟨C,h,H⟩:=pearl 6; refine ⟨C,h,fun n o i p z w=>?_⟩; convert sprue (H _ o (stab i) p (stabL _) z w) p.threshold⁻¹ using 1; have ht:= p.threshold_pos; rw [abs_of_pos (by positivity)]; field_simp
lemma π_sun (u:10 < (More n).val)(v:Gem)(b:SU.group.Color)(p:BudgetPoint)(i:GateI): HasDerivAt (fun x:ℝ=> πon o i p (increment 1 (x • gateC o p.threshold (hem v b)))) (acCue v i • b) 0:=by
 let T:=p.threshold; let j:=stab i; apply ((linkage (gateC o T (hem v b)) j o).const_smul T⁻¹).congr_deriv; let V:= fanP _ o i; let F:=hem v b; change T⁻¹ • faceCurl (slotFace (stab i) o) _=_; rw [rock_v o i]; change T⁻¹ • faceCurl (V,i.1) (mapCo (plot o (formC F) T))=_; rw [liaison_h (formC F) o V i.1 (by have ht:=feet_v o i; unfold V; omega) u.le T]; -- tune unfold gateC
 change T⁻¹ • (T • CurlMap (formC F) _ _ _)= _; rw [inv_smul_smul₀ p.threshold_pos.ne',formC_flux]; rfl
lemma π_shadow (u:10<(More n).val)(v:Sut)(b:SU.group.Color)(p:BudgetPoint)(i:GateI): HasDerivAt (fun x:ℝ=> πon o i p (increment 1 (x • gateT o p.threshold (loomH v b)))) (veCue v i • b) 0:=by
 let T:=p.threshold; let j:=stab i; apply ((linkage (gateT o T (loomH v b)) j o).const_smul T⁻¹).congr_deriv; let V:=fanP _ o i; let F:=loomH v b; change T⁻¹ • faceCurl (slotFace (stab i) o) _=_; rw [rock_v o i]; change T⁻¹ • faceCurl (V,i.1) (mapCo (plot o (formT F) T))=_; rw [liaison_h (formT F) o V i.1 (by have ht:=feet_v o i; unfold V; omega) u.le T]
 change T⁻¹ • (T • CurlMap (formT F) _ _ (stem o (fanP _ o i)))=_; rw [inv_smul_smul₀ p.threshold_pos.ne', formT_flux, net_v o i u]; unfold faceT veCue; rw [faceT, sum_smul]; apply sum_congr rfl; intro k _; exact (mul_smul ..).symm
end HushP
end Lenten
end YM.CF.TableF
end
