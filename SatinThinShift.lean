import SatinThinStitch

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


-- identity without fleet side conditions; use this in startup and gap opening
variable {N B:Side} (X:GramM (mid N B)) {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}(V:Grace K R L){e:ℝ}(p:Grasp V.U B e) (A:Scree.Loom (mid N B))
local notation "Ω"=> mid N B
local notation "σ"=> X.p
open Push.Local StressFlux AnalyticBridge.VerifiedReset
variable {J I: Type} [Fintype J][Fintype I][LinearOrder J][LinearOrder I]
attribute [-instance] instDecidableEqLex
def clothMark {n:Side}(q τ:ℝ)(o: Site n)(U:Pane n):ℝ:= if pingS τ (Φrap n o 10).val.2 U then q/τ^2*quadScore (node o) U else 0
lemma mark_zero (τ:ℝ)(o:Site N)(U:Pane N): clothMark 0 τ o U=0:=by unfold clothMark; split <;> simp
lemma exponent_pin (q:ℝ)(o:Site Ω)(U: Pane Ω): exponentL σ (cloth_E σ q o) U= (↑(clothMark q X.p.threshold o U):ℂ) • (1:Cipher Ω):=by
 let V:= Φrap Ω o 10; unfold cloth_E exponentL; rw [sum_eq_single V]; swap; · intro i v h; rw [Pi.single_eq_of_ne h]; simp [numbE] -- tune
 swap; · simp
 rw [Pi.single_eq_same]; unfold numbE clothMark; split
 next h=> rw [Set.indicator_of_mem h,plate_core,Complex.coe_smul]
 next h=> rw [Set.indicator_of_notMem h]; simp
variable (U:Skye.Orbit (mid N B)) (q:ℝ) (p': I→Site (mid N B))
lemma exponent_cloth (z:Key (Article I)): exponentL X.p (clothTable σ q p' z) U.1=(∑ i:Article I, z i * (↑(clothMark (readFee q (layer i)) X.p.threshold (treeO p' i) U.1):ℂ)) • (1: Cipher Ω):=by
 unfold clothTable; rw [e_s_K σ _ _ U]; simp_rw [voc_E σ _ _ U]; rw [Finset.sum_smul]; exact sum_congr rfl fun i _=> (congrArg (z i • ·) (exponent_pin X _ _ U.1)).trans (smul_smul ..)
lemma density_fee (F G:RegBudget Ω)(E:ForceBudget Ω){z:ℂ}(hz:exponentL X.p G U.1=z • 1): Scree.denZ (color_b X X.beta (X.F+(F+G)) X.slip (X.K+E) X.v) p A U= Complex.exp z • Scree.denZ (color_b X X.beta (X.F+F) X.slip (X.K+E) X.v) p A U:=by
 let D:= color_b X X.beta (X.F+(F+G)) X.slip (X.K+E) X.v; let W:= color_b X X.beta (X.F+F) X.slip (X.K+E) X.v
 have he: D.board U= Complex.exp z • W.board U:=by
    unfold GramM.board; change exp (exponentL X.p (X.F+(F+G)) U.1 + exponentL _ _ _)* _=_; rw [←add_assoc X.F,Larch.ripe_H X.p U _ G,hz]; rw [show (exponentL X.p (X.F+F) U.1+z • 1)+exponentL X.p X.slip U.1 = (z • 1)+(exponentL X.p (X.F+F) U.1+ exponentL X.p X.slip U.1) by abel]
    letI :NormedAlgebra ℚ (Cipher Ω):= NormedAlgebra.restrictScalars ℚ ℂ _; let t:Cipher Ω:= exponentL σ (X.F+F) U.1+exponentL X.p X.slip U.1
    rw [NormedSpace.exp_add]; change exp (Pastry.hollow z) * exp t*_ = _; rw [← Iva.yeaH]; change (Complex.exp z • (1:Cipher Ω))* _*_= _; rw [smul_mul_assoc,smul_mul_assoc,one_mul]
 change (Complex.exp (D.betaL A U)) • (acts (tank _ (D.board U)) _) = _; rw [he]; let Z:= spar K.j X.J.M (A U)
 change (Complex.exp (W.betaL A U)) • (acts (tank Z (Complex.exp z • W.board U)) _) = _; rw [show tank Z _=_ from (tankL (N:=Ω) Z).map_smul (Complex.exp z) (W.board U),act_smul]; exact smul_comm ..
lemma density_ticket (z:Key (Article I)): Scree.denZ (dayShift X (clothTable X.p q p') 0 z) p A U= Complex.exp (∑ i:Article I, z i*(↑(clothMark (readFee q (layer i)) X.p.threshold (treeO p' i) U.1):ℂ)) • Scree.denZ X p A U:=by
 let TK:= clothTable σ q p'; have hp:= density_fee X V p A U 0 (TK z) 0 (exponent_cloth X U q p' z); rw [zero_add (TK z),add_zero X.F,add_zero X.K,show color_b X X.beta X.F X.slip X.K X.v=X from rfl] at hp
 unfold dayShift; rw [Pi.zero_apply,add_zero]; exact hp
#print axioms density_ticket
end YM.CF.QuadClock
