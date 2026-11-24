import CellQ.CoverU
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
open Drift Grain Graph -- tune
open CF.Neon
variable {I:Type}[LinearOrder I][Fintype I]{m B:Side}
local notation "Sα"=>mid m B
local notation "QK"=>Mew.Key (PairKey I)
variable (T:Dyad.Log I (mid m B))(o:I→ Site (mid m B))(R:GramM (mid m B))(h a b:ℝ) (L0:Side)(F:Bool→ArcΦ)(H:Clinic o T 1 h a b R L0 F)(t:Very_Ψ o R.p.B)(k:4 ≤R.p.B)
local notation "X"=>R.p
include H t k
abbrev roofPrice (I:Type)[Fintype I](n:Side)(Ra:BudgetPoint)(a b:ℝ)(r:ℂ):ℝ:= (Fintype.card (PairKey I):ℝ)*(‖r‖*a)+sites n*b*∑ i∈ Ico 2 (Fintype.card (PairKey I)+1), (‖r‖*dustbit Ra.supportExponent Ra.B)^i
lemma reg_price(hh:0≤h)(z:QK)(p:∀ i,‖z i‖ ≤1)(r:ℂ) (V: Pane Sα):
 ∑ j:Scree.Hub Sα,torque h (Graph_N X (T.earn (r • z)) j V) ≤ roofPrice I Sα X a b r:=by
 let g(j:Scree.Hub Sα)(v:QK):=Graph_N X (T.earn v) j V
 refine crest_all (S:=univ) (w:=fun j:Scree.Hub Sα=>hub_r (V:=Sα) X j.val.2) (D:=fun j=>grainD o j.val.2) g (torque_ok (Β:=Sα) hh) (fun i _=> ?_) z p (fun i _=> (Real.exp_pos _).le) (first_sky T o R h a b L0 F H · V hh) ?_ (dustbit R.p.supportExponent R.p.B) r (Real.exp_pos _).le (fun j v i _ e=> stars T o R h a b L0 F H t i _ (mem_Ico.mp v).1 e k)
 · by_cases hv: pingS R.p.threshold i.val.2 V
   · unfold g Graph_N numbE; simp_rw [Set.indicator_of_mem (show V∈ ({w:Pane Sα|pingS R.p.threshold i.val.2 w}:Set (Pane Sα)) from hv)]; exact H.age.1 i V
   unfold g Graph_N numbE; simp_rw [Set.indicator_of_notMem (show V∉ ({w:Pane Sα|pingS R.p.threshold i.val.2 w}:Set (Pane Sα)) from hv)]; exact Grain.zero
 intro l e; have he (i:PairKey I): ‖(l • z) i‖ ≤1:=by change ‖l*z i‖ ≤ _; rw [norm_mul]; exact (mul_le_mul e (p i) (norm_nonneg _) zero_le_one).trans (by norm_num)
 obtain ⟨w,v,k⟩:= (H.span (l • z) he).1.weight
 exact maskE_total w _ _ V _ v k hh
lemma force_price(hh:0≤h)(z:QK)(p:∀ i,‖z i‖ ≤1)(r:ℂ) (V: Orbit Sα):
 ∑ j:Scree.Force Sα,torque h (clamp X j (T.wake (r • z) j) V) ≤ roofPrice I Sα X b b r:=by
 let g(j:Scree.Force Sα)(v:QK):=clamp X j (T.wake v j) V
 refine crest_all (S:=univ) (w:=fun j:Scree.Force Sα=>hub_r (V:=Sα) X j.val.1.val.2) (D:=fun j=>grainD o j.val.1.val.2) g (torque_ok (Β:=Sα) hh) (fun i _=> ?_) z p (fun i _=> (Real.exp_pos _).le) (first_pad T o R h a b L0 F H · V hh) ?_ (dustbit R.p.supportExponent R.p.B) r (Real.exp_pos _).le (fun j v i _ e=>stars T o R h a b L0 F H t i.val.1 _ (mem_Ico.mp v).1 e k)
 · unfold g clamp; split_ifs; exact H.age.2 i V; exact Grain.zero
 intro l e; have he (i:PairKey I): ‖(l • z) i‖ ≤1:=by change ‖l*z i‖ ≤ _; rw [norm_mul]; exact (mul_le_mul e (p i) (norm_nonneg _) zero_le_one).trans (by norm_num)
 obtain ⟨w,v,k⟩:= (H.span (l • z) he).2.weight
 exact maskW_total w _ _ V _ v k hh

end Kona
end YM.CF.Py.Rate
end
