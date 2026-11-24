import YM.CF.Vp929.Canon.Galley
import YM.CF.Vp929.Stage.Thatch
import YM.CF.Sere.Cogn
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
open AnalyticBridge.VerifiedReset.Collection
variable {v:ℝ}
namespace QuiltB
open Lor Oath Feu Siete Ione AnalyticBridge.VerifiedReset.Geo Pitching.Focus
variable {Q': BudgetPoint}{x z y:ℝ}
section
local notation "P'"=> HI
-- Returns price coefficients with parameters set strictly pre-L. Works with the same epoch as manufacture. Does not require projection teller for threshold.
def subA (b:Clip)(σ C α:ℝ):= |scoreH HI α|+|rate_b HI b σ C α (-1)|+|rate_h HI b σ C α (-1)|
def earlyA (b:Clip)(σ C α:ℝ):= |cone_D 6 2| * subA b σ C α
variable (b:Clip)(σ C α:ℝ) (Q:BudgetPoint)(h: Q.order=6)(t:Q.power=2)(e:Q.supportExponent=1)
local notation "Z"=> Q.threshold
include h t e
private lemma identP : Q.order =HI.order ∧ Q.power = HI.power∧ Q.supportExponent=HI.supportExponent := ⟨h,t,e⟩
private lemma scored : volH Q=volH HI * Q.threshold^2:=by
 unfold volH; rw [mul_assoc, Finset.sum_mul]; apply congrArg; refine sum_congr rfl (fun i _=> ?_); rw [sum_mul]; apply sum_congr rfl; intro j _; unfold pairBill; obtain ⟨h,h',-⟩:= identP Q h t e; rw [h,h', show HI.threshold=(1:ℝ) from rfl]; ring
private lemma corner : trimH Q v= trimH HI v * Q.threshold^2:=by
 obtain ⟨i,j,k⟩:=identP Q h t e; unfold trimH heightH liteV composeCost Cash.prominence; rw [scored Q h t e,i,k]; ring
include b σ C α
private lemma ratepair : rate_b Q b σ C α (-1)=rate_b HI b σ C α (-1)* Q.threshold^2 ∧ rate_h Q b σ C α (-1)=rate_h HI b σ C α (-1)* Q.threshold^3:=by
 obtain ⟨h,h',e⟩:=identP Q h t e; unfold rate_b rate_h Quotes.lowBase Quotes.highBase Quotes.anchoredFee lowFee AnalyticBridge.VerifiedReset.Geo.both lowCost rowCost faceCost highFee turnFee rowDegree pairBill; rw [h,h',e,show HI.threshold=(1:ℝ) from rfl]; constructor <;> ring
lemma accountEarly : |accountR Q b α σ C| ≤ subA b σ C α*Z^2:=by
 have hh:scoreH Q α=scoreH HI α * Z^2:=by unfold scoreH; rw [scored Q h t e,(identP Q h t e).2.2]; ring
 have hs:= Q.threshold_pos; unfold accountR subA; obtain ⟨h,h'⟩:= ratepair b σ C α Q h t e; rw [hh,h,h']; apply (abs_add_le ..).trans; simp_rw [add_mul]; have he:|Z^2|=Z^2:=abs_of_nonneg (sq_nonneg _); refine add_le_add ((abs_add_le ..).trans_eq (by simp_rw [abs_mul,he])) ?_; rw [abs_mul,abs_of_pos (pow_pos hs 3)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le Q.threshold_le (by decide)) (abs_nonneg _)
variable (L:ℕ)
lemma kit_early: |shipA Q L b σ C α| ≤ Real.exp (mstar L:ℝ)*(earlyA b σ C α*Q.threshold^2):=by
 let x:=cone_D 6 2; let m:=mstar L
 unfold shipA earlyA; rw [h,t,e,one_mul,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
 exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (accountEarly b σ C α Q h t e) (Real.exp_pos _).le) (abs_nonneg _)).trans_eq (by ring)
omit h t e
private lemma μsame : rate_μ Q b σ C v (-1)=rate_μ Q b σ C v 1:=by unfold rate_μ; rw [abs_neg]

lemma earlyA_pos : 0 ≤ earlyA b σ C α:=by unfold earlyA subA; positivity
lemma mist (d:ℝ)(L:ℕ): BoreP (fun x=>tet_B (Extension.yard L) (epoch x).B * d):=by
 let k:=Extension.yard L; let V(x:ℝ):=(radiusB x:ℝ); let W:= (BoreP.still (k:ℝ)).grip BoreP.radius_c; refine ((((W.join W).join (BoreP.still 1)).self 4).grip (BoreP.still d)).tune ?_
 filter_upwards [hall_l HI] with x p; unfold Pitching.Focus.epoch tet_B; rw [p]; simp only [Nat.cast_add,Nat.cast_pow,Nat.cast_mul,Nat.cast_one]; simp [k,Extension.yard]

lemma accountBore (L:ℕ)(v:ℝ) : BoreP (fun x=>shipT (epoch x) L b σ C α v):=by
 let A(x:ℝ):= epoch x; let D:=b;
 let X:= Extension.yard L; have hk(x:ℝ): (A x).order=6 ∧(A x).power=2∧(A x).supportExponent=1:= let_X HI x
 have ht:BoreP fun i=> (A i).threshold:= (BoreP.still 1).tune (Eventually.of_forall fun i=> by rw [abs_one,abs_of_pos (A i).threshold_pos]; exact (A i).threshold_le)
 have ha:BoreP fun i=> trimH (A i) v:= ((BoreP.still (trimH HI v)).grip (ht.self 2)).tune (Eventually.of_forall fun i=>by rw [corner _ (hk i).1 (hk i).2.1 (hk i).2.2])
 have hz:BoreP fun i=>accountT (A i) b v σ C:=by unfold accountT; exact ha.join ((μK_Bore HI v b σ C).tune (Eventually.of_forall fun i=> by rw [μsame b σ C α (A i)]))
 let u:=subA b σ C α; have hp:0 ≤ u:=by unfold u subA; positivity
 have he:BoreP fun i=> accountR (A i) b α σ C:=(BoreP.still u |>.grip (ht.self 2)).tune (Eventually.of_forall fun i=> ((accountEarly b σ C α _ (hk i).1 (hk i).2.1 (hk i).2.2).trans (le_abs_self _)))
 have hi:BoreP fun i=> Larch.tet_B X (A i).B:=by simpa only [mul_one] using mist (b:=b) (σ:=σ) (C:=C) (α:=α) 1 L
 let F(i:ℝ):= Extension.wagon L (A i).order (Cash.prominence (A i)) (A i).B (accountR (A i) b α σ C)+accountT (A i) b v σ C; have hg: BoreP F:=by
    have hu:BoreP fun i=>Larch.tet_B X (A i).B:=hi
    apply BoreP.join _ hz; apply BoreP.tune ((BoreP.still (Larch.shine_C X ((1:ℝ)+1+1))).grip (hu.grip ((BoreP.still (Vow.chi_f 6)).grip he))); filter_upwards with i; unfold Extension.wagon Cash.prominence; rw [(hk i).1,(hk i).2.2]
 apply BoreP.tune (hg.join ((BoreP.still (tray_H 6)).grip hg)); filter_upwards with i; unfold shipT; change |F i + tray_H (A i).order*F i| ≤ _; rw [(hk i).1]
end
end QuiltB
end Test
end YM.CF.Py.Rate
