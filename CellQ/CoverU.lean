import CellQ.Keel
import CellQ.Circuit
import Taffeta.Quote
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered Dyad Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
namespace Kona
open Drift Grain
open CF.Neon
variable {I:Type}[LinearOrder I][Fintype I]{m B:Side}
local notation "Sα"=>mid m B
local notation "QK"=>Mew.Key (PairKey I)
local notation "ΠZ"=>Log I Sα
variable (T:Dyad.Log I (mid m B))(o:I→ Site (mid m B))(R:GramM (mid m B))(h a b:ℝ) (L0:Side)(F:Bool→ArcΦ)(H:Clinic o T 1 h a b R L0 F)
local notation "X"=>R.p
open Graph
include H
lemma first_sky (i:PairKey I)(x:Pane Sα)(hx:0≤h): let v:=pulse (yard i) (altQ i) 1; ∑ j:Scree.Hub Sα, torque h (Graph_N X (T.earn v) j x) ≤ a:=by
 intro v
 let Y:= νTip T.earn i; obtain ⟨A,C,V⟩:=H.taste i;
 let y:=node (o (yard i)); let p(j:Scree.Hub Sα):= j.val.1=y
 have he(j:Scree.Hub Sα): (Y j) x=T.earn v j x:=by unfold Y νTip; exact (H.age.1 j x).horn i
 have hf(j:Scree.Hub Sα): numbE R.p.threshold j.val.2 (Y j) x=numbE R.p.threshold j.val.2 (T.earn v j) x:=by
    unfold numbE; by_cases h:pingS R.p.threshold j.val.2 x; · rw [Set.indicator_of_mem (show x∈_ from h),Set.indicator_of_mem (show x∈_ from h),he]
    rw [Set.indicator_of_notMem (show x∉_ from h),Set.indicator_of_notMem (show x∉_ from h)]
 obtain ⟨f,u,W⟩:=A.weight
 apply le_trans _ (W y)
 apply Finset.sum_le_sum; intro j _; unfold Graph_N; rw [←hf]; have hp:= Graph.sky (u j) hx x
 split_ifs with k
 · exact hp.trans (R.p.loMass _ _ (((torque_ok (Β:=Sα) hx).low _).trans hp))
 have hk: j.val.1≠ y:= Ne.symm k
 rw [show Y j=0 from C j hk]; unfold torque numbE; by_cases h: x∈ {U| pingS R.p.threshold j.val.2 U}; · rw [Set.indicator_of_mem h]; exact (chaff _).le
 rw [Set.indicator_of_notMem h]; exact (chaff _).le
lemma first_pad (i:PairKey I)(x:Orbit Sα)(hx:0≤h): let v:=pulse (yard i) (altQ i) 1; ∑ j:Scree.Force Sα, torque h (clamp X j (T.wake v j) x) ≤ b:=by
 intro v; obtain ⟨f,u,W⟩:= (H.span v (pulse_bounds _)).2.weight
 let y:=node (o (yard i)); apply le_trans _ (W y); apply sum_le_sum; intro j _
 have hp:= Graph.pad (u j) hx x
 split_ifs with k
 · exact hp.trans (R.p.loMass _ _ (((torque_ok (Β:=Sα) hx).low _).trans hp))
 have he:T.wake v j x=0:=by
    let g(w:QK):= T.wake w j x; have h0:=H.age.2 j x
    refine Eq.trans (b:=g 0) (h0.sill ?_) (h0.dawnQ)
    intro a hf b
    have he:a≠yard i:=fun s=> k (show node (o (yard i)) ∈_ from (s ▸ (mem_filter.mp hf).2)) -- rewrite? 
    exact update_of_ne (fun v:pick a b=i=>he (congrArg yard v)) ..
 unfold clamp; split; rw [he]; exact (chaff _).le; exact (chaff _).le
/-- weight exemption from larger-root extra.H.Scope deal implicit.X. -/
def dustbit (A:ℝ)(k:ℕ):= Real.exp (-(A*(k:ℝ)^2/24))
lemma stars (t:Very_Ψ o R.p.B)(D:Scree.Hub Sα)(k:ℕ)(p:2≤k)(q:k≤(grainD o D.val.2).card)(hc:4≤R.p.B): 1≤ dustbit R.p.supportExponent R.p.B ^ k * hub_r (V:=Sα) R.p D.val.2:=by
 let b:= R.p.B; let v:= grainD o D.val.2
 have he:= Corona.separated_read (A:=D.val.2) (Q:=v) (fun i h=>(show Cube.node (o i) ∈ _ from (mem_filter.mp h).2)) hc (fun i _ j _ h=> ?_)
 swap
 · let u:=Cube.node ∘ o; have hh:b^3+b^3+b+b < separation (u i) (u j):= t.2 i j (fun e':u i=u j=> h (t.1 e')); exact (Nat.le_add_right ..|>.trans ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans hh.le))) -- tune
 have hq:k*b^2≤ 24*coverNumber R.p.B D.val.2:=by
    have hg: k ≤2*(v.card-1):=by change k≤v.card at q; omega
    apply le_trans (Nat.mul_le_mul_right (b^2) hg); rw [Nat.mul_assoc]; exact (Nat.mul_le_mul_left 2 he).trans_eq (by ring)
 unfold dustbit hub_r; rw [←Real.exp_nat_mul,←Real.exp_add]; apply Real.one_le_exp
 have hz:= Nat.cast_le (α:=ℝ).mpr hq; push_cast at hz; unfold b at *; nlinarith only [mul_le_mul_of_nonneg_left hz R.p.exponent_pos.le]
end Kona
end YM.CF.Py.Rate
end
