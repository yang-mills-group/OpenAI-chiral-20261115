import YM.CF.Esti.Lyce
import YM.Push.ABSOLUTE_SUMS.Delay
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){A B:Stores S}{r v:ℕ}
open Push Push.AbsoluteSums Push.AbsoluteSums.Packets Push.AbsoluteSums.Delay
abbrev shootV : AnalyticBridge.Annulus1AD.Mark S ≃ Packets.Seed S := Equiv.sumAssoc ..
lemma shotV(m): Packets.points S (shootV S m) = spotting S m:=by rcases m with (x|x)|x <;> rfl
lemma shotsV (B:Stores S)(m): shootV S m∈ seeds S B ↔ m∈ plots B:=by
 rw [vase_a]; rcases m with (i|i)|i <;> simp [Packets.seeds,shootV]
lemma rideB (r v:ℕ)(X: Hos S (r*v)): Packets.connected S r v X.val:=by
 let s:= plots X.val; let t:=seeds S X.val
 have he{i j}(h:Ac.chain (Palm S (r*v)) s i j): Ac.chain (skin S r v) t (shootV S i) (shootV S j):=by
    induction h with | refl=>exact .refl| tail _ v ih =>
      obtain ⟨l,h,x,hx,ht⟩:=v; exact Relation.ReflTransGen.tail ih ⟨(shotsV ..).mpr l,(shotsV ..).mpr h,x,by unfold skin; rw [shotV]; exact hx,by unfold skin; rw [shotV]; exact ht⟩
 obtain ⟨⟨z,hz⟩,hl⟩:=X.property; refine ⟨⟨_,(shotsV S X.val z).mpr hz⟩,fun i p j q=>?_⟩; obtain ⟨u,rfl⟩:=(shootV S).surjective i; obtain ⟨w,rfl⟩:=(shootV S).surjective j; exact he (hl _ ((shotsV ..).mp p) _ ((shotsV ..).mp q))
variable {L:Side}
def scaleM (G:Gauge)(L:Side)(r x:ℝ):= r*(Scales.p G L x)^2
lemma hatV(G:Gauge)(L:Side)(x r:ℝ): hatWin G L r 1 x=scaleM G L r x:=by unfold scaleM hatWin Scales.p; rw [mul_one,Scheduling.Clock.watch_two]; rfl -- tune
lemma seaT (G:Gauge)(L:Side)(d a:ℝ)(hp:0<d)(ha:0 ≤ a)(l:ℕ):∀ᶠ x in atTop, ∀ {c f:Side}(S:StepData c f),S.patch.L=L → Ac.Hit (stem S (r:=l*radiusB x)) (radiusB x) (fun i=>Real.exp (-scaleM G L d x*i.val.shares)) a (Real.exp (-scaleM G L d x/4)):=by
 filter_upwards [Delay.fits G L l hp zero_lt_one ha (show (0:ℝ) ≤ 0 by norm_num) 0 (show (0:ℝ)<2 by norm_num)] with x hx c f S hb; subst L
 obtain ⟨hv,hQ⟩:= hx 0 (scaleM G S.patch.L d x) 1 (by simp) (le_of_eq (hatV ..)) zero_le_one (by simp)
 let w(X : Stores S):= Real.exp (-scaleM G S.patch.L d x*X.shares); intro i
 have hp:= packet_variants S l (radiusB x) (fun x: Hos S (l*radiusB x)=>x.val) (stem S) (fun x=>w x.val) zero_le_one hv (fun _=> (Real.exp_pos _).le) (fun i p=> ⟨rideB S _ _ i,Subset.refl _⟩) (fun A h s v=> ?_) i
 exact budget_loosen hp ((hQ 0).trans_eq (by rw [hatV]; simp)); -- tune
 unfold Packets.income; simp_rw [one_mul,zero_sub]; by_cases l:s.Nonempty; swap; simp [not_nonempty_iff_eq_empty.mp l,(Real.exp_pos _).le]
 obtain ⟨i,t⟩:=l; rw [show s={i} from Finset.eq_singleton_iff_unique_mem.mpr ⟨t,fun a h=>Subtype.ext ((v a h).trans (v i t).symm)⟩,sum_singleton]; change w i.val ≤ _; rw [v i t]
-- Numeric dictionaries calibrate x^- arbitrary vs scaleM wins & seam Permit. Post L.
open Next.Fluctuations
local notation "G"=> SU.group
variable {u a b θ p:ℝ}{X:tangD c}
lemma cash_q(K:Teller G):∃ N:ℕ,∀ P:Patch,N ≤ P.L.val →∀ H:ℝ,∃ W θ:ℝ,H ≤ W∧0<W∧0<θ∧∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S),Cert P K S T x→ PointCharge T x W θ:=by
 obtain ⟨N,H⟩:= (grants K).precedes; refine ⟨N,fun P hx v=>?_⟩; obtain ⟨Q,h⟩:= eventually_atTop.mp (H _ hx); let W:=max 1 (max Q v); have hx:0<W:= zero_lt_one.trans_le (le_max_left ..); obtain ⟨θ,ht,hθ⟩:=h W ((le_max_left ..).trans (le_max_right ..)); refine ⟨W,θ,(le_max_right ..).trans (le_max_right ..),hx,ht,?_⟩; filter_upwards [hθ.late] with x h c f S T e
 let hp:=congrArg RG.Patch.L e.got; intro I U V W Y p v; -- tune PointCharge args
 rw [hp]; exact h _ _ S hp e.size T e.funds.1 _ _ _ _ _ p v
end YM.CF.Esti
