import YM.CF.DPress.Motto.Farms
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Larch Ione Taxi Bake Salt
namespace WagesC
namespace Blend
variable {n:Side}{k L:ℕ}(P:BudgetPoint){a h b:ℝ}
local notation "Sx"=> Point n
variable (B:Blend n k) (w: Wings k P a n)(t:1≤h)(z:ℝ)
variable (i:Point n × Point n) (p:i∈κN n k)
abbrev ρl (P:BudgetPoint)(k:ℕ)(a z:ℝ):=2 * (|z| * (grade P k a*P.threshold^2))
include w p t
private lemma beatP : PressB P (χΩ i) (fund i.2-fund i.1) h (grade P k a*P.threshold^2+grade P k a*P.threshold^2):= (capE P h _ t).sub (budgetPump P w _ _ subset_union_right ((separation_comm ..).trans_le (mem_filter.mp p).2)) (budgetPump P w _ _ subset_union_left (separation_self _|>.trans_le (Nat.zero_le k)))
lemma rentS : PressB P (χΩ i) (B.fA z i) h (φΩ B i * ρl P k a z):=by
 refine (capE (n:=n) P h _ t).toReceipt.relax (scale_E P (beatP P w t i p) _) (le_of_eq ?_); change |z*φΩ B i| * _=_; rw [abs_mul,abs_of_nonneg (weight ..)]; unfold ρl; ring -- tune
lemma Ion_p : spark (χΩ i).val.1 (B.fA z i):=by
 let x:= i.2; let v:= i.1; let V:=χΩ i; let F:=feeW x-feeW v
 have hx:P.Regular V.val.2 (feeW x):= reg_larger (Plaque.grants P x) Finset.subset_union_right; have hu:P.Regular V.val.2 (feeW v):= reg_larger (Plaque.grants P v) Finset.subset_union_left; have hv:=reg_sub hx hu; let hpG(y:LinearJet SU.group): logHessian F (y.field v) (y.field v)=0:=by
    rw [show F=feeW x-feeW v from rfl,hessian_sub hx hu,Plaque.hessian P x y w.hn ((separation_comm x v).trans_le (mem_filter.mp p).2),Plaque.hessian P v y w.hn (by rw [separation_self]; omega : separation v v≤k),sub_self] -- tune
 have ht: spark V.val.1 (fund x-fund v):=by rw [show fund x-fund v=moldV n ∘ F from funext fun i=> (map_sub ..).symm]; exact spark_H (X':=V) hv (by simp [F,Plaque.fee_one]) (affine_zero hv v hpG) -- tune x order
 exact spark_g (X₀:=V) ht (Beau.profit (beatP P w t i p) (zero_le_one.trans t)) _
omit p
lemma working : Ionic P L (B.Sα z):=by
 intro X _ _; exact Beau.add_Z (X₀:=X) _ (fA B z) (fun i=> φΩ B i *ρl P k a z) (fun i p=>(mem_filter.mp p).2 ▸ Ion_p P B w t z i (mem_filter.mp p).1) (fun i p=>(mem_filter.mp p).2 ▸ rentS P B w t z i (mem_filter.mp p).1) (zero_le_one.trans t)
lemma priceS : IncX B.even (B.Sα z) P h ((2*ρtax a k P)*|z| *P.threshold^2):=by
 constructor; swap; exact suitS B z
 apply IncX.weight (Q:=primeU); apply Larch.feat_v _ χΩ _ (fun i=>φΩ B i * ρl P k a z) _ _ (fun i p=> rentS P B w t z i p) -- tune arg order
 intro i; have hb:0 ≤ ρl P k a z:=by have he:0≤grade P k a*P.threshold^2:=(capE P h _ t).priceQ _ (budgetPump P w i (hup i) (Subset.refl _) (separation_self i|>.trans_le (Nat.zero_le k))); unfold ρl; positivity
 let L:= Real.exp P.supportExponent * ρl P k a z; let V:= (κN n k).filter (fun j=> j.1=i); refine le_trans (b:=∑ j∈V,L*φΩ B j) ?_ ?_; swap; · rw [← mul_sum,money]; unfold L ρl ρtax; exact le_of_eq (by ring)
 apply sum_le_sum; intro j p; unfold BudgetPoint.mass; refine (mul_le_mul_of_nonneg_right (Real.exp_monotone (b:=P.supportExponent) ?_) (mul_nonneg (weight ..) hb)).trans_eq ?_
 · apply mul_le_of_le_one_right P.exponent_pos.le; have hm: coverNumber P.B (χΩ j).val.2≤1:=wraps P w _ _ (mem_filter.mp ((mem_filter.mp p).1)).2; exact_mod_cast hm
 unfold L; ring
end Blend
end WagesC
end YM.CF.Py.Kay
