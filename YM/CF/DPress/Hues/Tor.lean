import YM.CF.DPress.Hues.Heart
import YM.CF.Pso.Cay
/- contextual linear formulas. only fixed beta for hol checks. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
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
open Corne
open Girt Eire
open Oath Feu Feu.Corset Haro Larch Vow Salt Ione Py Bake
open PhysicalNext.JointLoad.Heir Yaw Nor Pig Wray Jade Iva
namespace Quality
open DPress DPress.Analytic DPress.Fees Prism
open scoped YM.CF.Mew
variable
 {N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
 {d pK' x A:ℝ}{κ0:ℝ}{j k n r:ℕ}{q':Chi}
 (V:Grace K R L){U: Grasp V.U B d}{W:GivenX V U}
 {X:GramM (mid N B)}{Y:GramM (mid P B)}{H:Muster G S x d T}
 (M: Sheep V U W G Y.J X.J (k+2) n A)
 (D_: Corset d q' pK' (k+2) n)(Q:Rill.Arch G d)(C':ℝ)(Xp₀:SuitP k C') (Jp:PactH d pK' (Xp₀.C*(R.L.val:ℝ)⁻¹^2) κ0 q' (k+2) n D_)
-- fix continuity & linearity via exposing stencil (one top-mode value at identity). gen by taking synthetic top with repeated constants.Press constraint not relevant. -/
local notation "N0"=> (mid N B)
local notation "N1"=> (mid P B)
abbrev xG (Y:GramM N1)(ξ:Cipher N1):GramM N1:=color_b Y 0 (fun _ _=>ξ) (fun _ _=>ξ) 0 0
abbrev Film (ξ:Cipher N1):= glasp (H:=H) (Y:=xG Y ξ) (X:=X) V M D_ Q C' Xp₀ Jp
local notation "𝓗"=> Film (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp
abbrev seatZ(ξ:Cipher N1):InkD N1:=fun _=>ξ
lemma act(o:Roc N1)(ξ:Cipher N1): actionZ (xG Y ξ) o=seatZ ξ:=by funext i; unfold actionZ; split <;> rfl
lemma bothH(y:Youth N P B): glasp (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp y= Film (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp (actionZ Y y.1 (1:Pane N1)) y:=by
 unfold Film glasp beam_C; simp only [act]
-- avoid notation problem
lemma char_plus(y v:Prism.Rock (mid P B))(p q:InkD (mid P B)): Haro.CharM (p+q) y v 1= Haro.CharM p y v 1+ Haro.CharM q y v 1:=by ext i j; unfold Haro.CharM Prism.mileT; simp only [Matrix.add_apply,Matrix.of_apply, Prism.port_eq]; split; simp; apply Eq.trans (mul_add ..) ?_; rfl -- tune ext real complex norms
lemma char_s (y v:Prism.Rock (mid P B))(p:InkD (mid P B))(h:ℂ): Haro.CharM (h • p) y v 1=h • Haro.CharM p y v 1:=by ext i j; unfold Haro.CharM Prism.mileT; simp only [Matrix.smul_apply,Matrix.of_apply,Prism.port_eq]; split; simp; exact mul_left_comm ..
include H
private lemma plusH (y:Youth N P B) (a b:Cipher (mid P B)) : Film (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp (a+b) y= Film (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp a y+ Film (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp b y:=by
 unfold Film glasp beam_C; split
 next h=>
    unfold wavy Oath.turnB; rw [← sum_add_distrib]; refine sum_congr rfl (fun i p=>?_); rw [←sum_add_distrib]; refine sum_congr rfl (fun j p=>?_); rw [← sum_add_distrib]; apply sum_congr rfl; intro k l; unfold heat_K; split; next h=> unfold Haro.lyric; simp_rw [act]; rw [show seatZ (a+b)=seatZ a+seatZ b from rfl,char_plus,mul_add,add_mul] -- tune simp.act
    next h=>simp
 next h=> simp
private lemma scaleH (y:Youth N P B) (a:ℂ) (b:Cipher (mid P B)) : Film (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp (a • b) y= a • Film (H:=H) (Y:=Y) (X:=X) V M D_ Q C' Xp₀ Jp b y:=by
 unfold Film glasp beam_C; split
 next h=>
    unfold wavy Oath.turnB; rw [Finset.smul_sum]; refine sum_congr rfl (fun i p=>?_); rw [Finset.smul_sum]; refine sum_congr rfl (fun j p=>?_); rw [Finset.smul_sum]; apply sum_congr rfl; intro k l; unfold heat_K; split; next h=> unfold Haro.lyric; simp_rw [act]; rw [show seatZ (a • b)=a • seatZ b from rfl,char_s,mul_smul_comm,smul_mul_assoc] -- tune simp.act
    next h=>simp
 next h=> simp
abbrev σFilm(y:Youth N P B): Cipher (mid P B) →L[ℂ] Op SU.Slot:= LinearMap.toContinuousLinearMap
 { toFun:=fun ξ=> (𝓗) ξ y, map_add':=fun a b=> plusH V M D_ Q C' Xp₀ Jp y a b, map_smul':=fun a b=> scaleH V M D_ Q C' Xp₀ Jp y a b }
omit H
abbrev FloatQ(X Y: Prism.Rock N0) (U: Pane N0): Op SU.Slot →L[ℂ] FC (Dwell N0):= LinearMap.toContinuousLinearMap
 { toFun := cars_P X Y U, map_add':=fun x y=> by unfold cars_P lineY Haro.taxi; simp only [add_mul,Matrix.add_apply,add_smul,sum_add_distrib], map_smul':= fun a b=> by unfold cars_P lineY Haro.taxi; simp only [smul_mul_assoc,Matrix.smul_apply,RingHom.id_apply,Finset.smul_sum,smul_eq_mul,mul_smul] }
-- end later. 
end Quality
end YM.CF.Oise
