import Rods.Ink
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
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
open Stencil Push.SectorMeasure Larch
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e kL:ℝ}{B:Side}{P:Grasp V.U B e}{qχ:Chi}(A:SiteLedger V P kL qχ){φ:Vxpert V A}{D0 f v D Q U:ℕ}(J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Margin R.L D0 D Q U)
variable(j r p:ℕ){G:Calibration}{m:Side}(u₁: U=G.ℓ)(hf:f≤ j)(hr:j≤r)(hv:r≤ v)(hp:22≤ p)(C D₁:ℕ→ℝ)(he:Scree.mid (A.side j) B=G.c m)
local notation "tK"=> sportT A h j r p u₁ J S h hf hr hv u₁ hp C D₁ he
local notation "Σs" k:max=>mid (A.side k) B
variable (l:List (Tix A j))
open ThinGauge
noncomputable abbrev bpay(L:Side)(j r v:ℕ):ℝ:=gainCost L^(v-j) + gainCost L^(v-r)*((boost (Xη L))^(r-j)*2)+ boost (Xη L)^(r-j)
lemma bpayG(L:Side)(j r v:ℕ):0≤ bpay L j r v:=by unfold bpay; have h:=gainCost_pos L; have k:=boostP L; positivity
lemma sum_box {I:Type}[LinearOrder I][Fintype I](ι:PairKey I)(L:Side)(j r v:ℕ)(C D₁:ℕ→ℝ)(hr:j≤r)(hv:r≤ v)(ht:∀ i,j ≤ i → i<v → Niche L (C i) 0)(hs: |revenue L C D₁ r j-1|≤1/4): ‖shareT L C D₁ r v j ι‖+‖shareS L r j ι‖≤bpay L j r v:=by
 have hg:=gainCost_pos L; have hu:=boostP L
 have h₁: |revenue L C D₁ r j|≤2:= by linarith only [abs_le.mp hs|>.1,abs_le.mp hs|>.2, abs_le.mpr (show -(2:ℝ) ≤ revenue L C D₁ r j ∧ revenue L C D₁ r j ≤2 from by obtain ⟨a,b⟩:= abs_le.mp hs; constructor<;> linarith)] -- simplify
 have hj:= gainBoundS C L (hr.trans hv) ht
 have hk:= gainBoundS C L hv (fun i h v=>ht i (hr.trans h) v)
 unfold shareT shareS bpay; by_cases h:ι.2=true
 · rw [if_pos h,if_pos h,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_mul,abs_neg,abs_of_pos (pow_pos hu _)]
   have e:= mul_le_mul hk (mul_le_mul_of_nonneg_left h₁ (pow_pos hu (r-j)).le) (mul_nonneg ((pow_pos hu _).le) (abs_nonneg _)) (pow_pos hg _).le; linarith [pow_pos hg (v-j)]
 rw [if_neg h,if_neg h,Complex.norm_real,Real.norm_eq_abs,norm_zero,add_zero]; exact hj.trans (by have h:=mul_nonneg (pow_pos hg (v-r)).le (show 0≤boost (Xη L)^(r-j)*2 by positivity); linarith [pow_pos hu (r-j)])
include J
lemma careerPlain(r:ℕ)(hr:f ≤ r)(hv:r≤ v)(F:Mark (mid (A.side r) B))(c:ℝ)(hS:SoloC F c):SoloC (blaze V A φ r v F) c:=by
 by_cases a:v=r; · subst v; simpa [Keeping.blaze, hop_here] using hS
 obtain ⟨d,y,pS,⟨h'⟩,w,_⟩:=J.clock r hr (show r<v by omega)
 unfold Keeping.blaze; rw [hop_step _ _ _ _ (lt_of_le_of_ne hv (Ne.symm a))]; change SoloC (blaze V A φ (r+1) v _) c
 apply careerPlain (r+1) (hr.trans (Nat.le_succ _)) (by omega) _ c
 rw [J.choice r]; exact upgrades (A.ratio r) (A.job r) _ _ _ _ _ _ _ _ w hS
termination_by v-r
decreasing_by omega
noncomputable abbrev steamPrice(L:Side)(j r v:ℕ)(M M':BudgetPoint)(x y:ℝ):ℝ:=bpay L j r v * (pcH M x + pcH M' y)
variable (c:(A.gram v).p.B≥0) -- using
include J
lemma hot_upper (hq:j≤r)(γ:f≤r)(hM:r≤v)(ht:∀ i,j ≤ i → i<v → Niche R.L (C i) 0)(hs: |revenue R.L C D₁ r j-1|≤1/4)(T:Tix A j)(F:Fields (mid (A.side v) B)):
    ‖pose2 A j r T v φ C D₁ F‖ ≤ steamPrice R.L j r v (A.gram v).p (A.gram r).p (A.money v) (A.money r):=by
 let jT:=fun _:Fin 1=> T.1
 let k:=liftCanvas V A j r jT
 let Y:=liftCanvas V A r v k
 let x:= (A.gram v).p; let y:=(A.gram r).p; let X:= pcH x (A.money v);let Q:= pcH y (A.money r); let e:= bpay R.L j r v
 let A':=cameo (Y 0) x (A.money v); let B':=blaze V A φ r v (cameo (k 0) y (A.money r)); let kT:PairKey (Fin 1):=(0,T.2); let α:=shareT R.L C D₁ r v j kT; let β:=shareS R.L r j kT
 have he:=solo_far (t:=F) (inkwell x (A.money v) (Y 0)); have hx: ‖B' F‖≤Q:=solo_far (careerPlain A J r γ hM _ Q (inkwell y (A.money r) (k 0)))
 change ‖α • A' F + β • B' F‖ ≤ e*(X+Q)
 apply (norm_add_le ..).trans; rw [norm_smul α (A' F),norm_smul β (B' F)]; have h:‖α‖+‖β‖≤e:=sum_box kT R.L j r v C D₁ hq hM ht hs
 apply le_trans _ (show (‖α‖+‖β‖)*(X+Q)≤_ from mul_le_mul_of_nonneg_right h (add_nonneg (pc_pos ..) (pc_pos ..))); rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (he.trans (le_add_of_nonneg_right (pc_pos ..))) (norm_nonneg α)) (mul_le_mul_of_nonneg_left (hx.trans (le_add_of_nonneg_left (pc_pos ..))) (norm_nonneg β))
#print axioms hot_upper
end Decaf
end YM.CF.Py.Rate
end
