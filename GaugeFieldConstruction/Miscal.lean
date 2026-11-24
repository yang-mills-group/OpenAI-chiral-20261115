import YM.CF.Oath.Suit
import YM.CF.Oath.Gloria
import GaugeFieldConstruction.Bisley
import GaugeFieldConstruction.Butane
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
variable {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{G:Ratio (mid N B) (mid P B)}
-- oath cZ at 0 avoids pay etc
variable
  {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {d A s:ℝ} {j k m n l:ℕ}
  (V:Grace K R L)
  {x:ℝ}
  {r:ℕ}
  (F:Pilot)
  {q:Chi}
  (Z:Pluck R)(U:Grasp V.U B d)(W:GivenX V U){Xs: GramM (mid N B)}{Y: GramM (mid P B)}{M:Sheep V U W G Y.J Xs.J (k+2) n A}(H:Muster G S x d T)
  {γ α:ℝ} (uF:Fend V H M Z F q Y.p Xs.p γ α j l r)
  (i:Roc (mid P B))(LC:Support (Domain N B))(hLC:LC=(hostX (l:= (H.post+90)*radiusB x) S i).val)
  (Qx:TailB→Support (Domain P B)→Toll (Iota G))(Qv: Grave→Support (Domain P B)→Toll (Iota G))(X00:RoofT V (M_:=M) Qx Qv)
  (u:Finset ((Support (Domain P B)) × Support (Domain P B)))(Y0:∀ p∈ u,m ≤ p.1.card+p.2.card)
  (oθ:Find Xs.p Y.p k n x R.L)(F':Raid (Dwell (mid P B)))(CC h:ℝ)(fP:∀ i,0≤ F' i)(vQ:0≤h) (T_:∑ i':Finset (Dwell (mid P B)), Scree.tariff Y.p i.1.val.1 h i'*F' i'≤CC)
-- we use `broomK` entry uniformly across fields/z; bill at third support power.Adf
include hLC fP oθ uF T_ X00 vQ Y0
open Trees
lemma TotalAff (K':ℝ)(p:0≤K') : let Z:= fun a b=>broomK (S:=S) Qx (K'*crack F' a b) u LC ((H.post+90)*radiusB x) a b; let V:=∑ a∈ hue_I i.1.val.2,∑ b∈hue_I i.1.val.2,Z a b; 0≤ V∧ joinV (Scree.tariff Xs.p (S.ratio.parent i.1.val.1) h) V ≤ (Real.exp (-(M.r0/2)*m)*lorp 0 (l+90) Xs.p.power (population*(A*followV [] G.count))*K')*CC:=by
 intro P_ V'
 let T:=Scree.tariff Xs.p (S.ratio.parent i.1.val.1) h
 let I:= hue_I i.1.val.2
 let dQ:= lorp 0 (l+90) Xs.p.power (population*(A*followV [] G.count))
 let P':= Real.exp (-(M.r0/2)*m)*dQ*K'; have hd:0≤ dQ:=by unfold dQ lorp; rw [mul_assoc _ (flavor*_) _,←sq]; unfold flavor; positivity
 have he:0≤P':=by unfold P'; positivity
 let C (a b):= Haro.amt Y.p.power i.1.val.1 a b*h^2*(crack F' a b)
 have ht(a b): 0≤ C a b:= mul_nonneg (mul_nonneg (by unfold Haro.amt; positivity) (sq_nonneg h)) (sum_nonneg fun i _=>sum_nonneg fun j _=>fP _)
 let B':=(H.post+90)*radiusB x
 have hv(a b:Rock (mid P B))(z:a∈I)(w:b∈I):0 ≤ P_ a b ∧ joinV T (P_ a b) ≤ P'*C a b:=by
    have hx:S.ratio.parent (Cube.node a.1)∈ LC:= by rw [hLC]; exact halo_subset _ _ (mem_image_of_mem _ (show _∈ inspected i.1.val.2 from mem_union_left _ (mem_filter.mp z).2));
    have hy:S.ratio.parent (Cube.node b.1)∈ LC:=by rw [hLC]; exact halo_subset _ _ (mem_image_of_mem _ (show _∈ inspected i.1.val.2 from mem_union_left _ (mem_filter.mp w).2));
    have hh:=uF.fireK.blade; have hp: B' ≤ (l+90)*radiusB x:=by unfold B'; rw [uF.pal.page];
    have hpre_b:(0:ℝ)*2*Yaw.χ (l+90) ≤ radiusB x*(M.r0/2):=by have hp:=M.ramp; simp only [zero_mul]; positivity
    let pz:=K'*crack F' a b; have hP:0≤ pz:= mul_nonneg p (sum_nonneg fun i _=>sum_nonneg fun j _=>fP _)
    have hL(j) : incline (hall G d) Xs.p.power (G.count.val:ℝ)⁻¹ (fun _=>population*(A*followV [] G.count)) (M.r0/2+M.r0/2) (Qx j):=by rw [add_halves,oθ.hK]; exact X00.pace j
    let hg:= (roll_v M.X M.oddP B' Qx X00.tax i.1.val.1 Xs.p (M.r0/2) 0 h (radiusB x) _ hpre_b le_rfl (by omega) hp (half_pos M.ramp).le vQ a b uF.head.scaleP LC pz hP hx hy u).1
    have he:= spendL M.X M.oddP B' Qx X00.tax i.1.val.1 Xs.p (M.r0/2) 0 h (radiusB x) _ hpre_b le_rfl (by omega) hp (half_pos M.ramp).le vQ a b uF.head.scaleP LC pz hP hx hy u Y0 (half_pos M.ramp).le hL
    refine ⟨sum_nonneg (fun i _=>hg i), le_trans (cleanPrice Xs.p _ h Qx pz u LC _ a b 1 (radiusB x) _ Xs.p.threshold_pos.le he) (le_of_eq ?_)⟩
    rw [show Xs.p.power=Y.p.power from oθ.hK.trans oθ.hL.symm]
    unfold P' pz C dQ; rw [show Xs.p.power = Y.p.power from oθ.hK.trans oθ.hL.symm]; simp only [Trees.currency,zero_mul,Real.exp_zero,one_mul]; ring
 have hu :∑ a∈I,∑ b∈I,C a b ≤ CC:=by
    apply le_trans _ ((pay_j _ _ _ fP vQ).trans T_); apply le_trans _ (sum_le_sum_of_subset_of_nonneg (f:=fun i=> ∑ j: Rock (mid P B),C i j) (subset_univ I) fun i _ _=>sum_nonneg fun j _=> ht i j); apply sum_le_sum; intro i _; exact sum_le_sum_of_subset_of_nonneg (subset_univ I) fun j _ _=> ht i j
 refine ⟨sum_nonneg fun i v=> sum_nonneg fun j w=> (hv i j v w).1,le_trans ?_ (mul_le_mul_of_nonneg_left hu he)⟩
 unfold V'; simp_rw [joinVsum,Finset.mul_sum]; exact sum_le_sum fun i a=>sum_le_sum fun j w=>(hv i j a w).2
end YM.CF.Oath
end
