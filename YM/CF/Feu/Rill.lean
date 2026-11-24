import YM.CF.Lilt.Flow
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Feu
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
local notation "B_"=> (More N)
local notation "S₁"=> (Domain N B)
local notation "dN"=> Directions SU.group (More N)
variable (P0:BudgetPoint) (o:Seat N) (X V_:Support (More N))(K_:ℕ)
variable (tH:o∈X)
-- Scale aperture.K.Root ext. stage ∣∆∣ estimation.
abbrev brim (P:BudgetPoint)(k:ℕ)(X:Support (More N)):ℝ := (1+(coverNumber k X : ℝ))^P.power
def lineP : dN→L[ℝ]dN:= (brim P0 K_ X)⁻¹ • rodV P0 o X ∅
local notation "t'"=> brim P0 K_ X
local notation "p'"=> lineP P0 o X K_
local notation "n'"=> P0.power
local notation "£"=> (stilK K_)^P0.power
lemma no_w(k:ℕ)(v:dN):wakeB (unrest ∅ k) v=v:=funext fun i=> by rw [steadyB,if_pos]; simp [unrest,Lattice.halo]
lemma non_r(U:Pane N)(k:ℕ)(v:dN):gyrate (unrest ∅ k) U v=increment U v:=by rw [gyrate,Function.comp_apply,no_w]
include tH
lemma verge_p:1 ≤ t':=one_le_pow₀ (by apply le_add_of_nonneg_right; positivity)
lemma vscale : ‖p'‖ ≤ £:=by
 have h:=zero_lt_one.trans_le (verge_p P0 o X K_ tH); rw [lineP,norm_smul,Real.norm_of_nonneg (inv_pos.mpr h).le,inv_mul_le_iff₀ h,mul_comm t']; exact (lens_x P0 o X _ K_ tH).trans (Nor.calendar P0 X)
lemma leg_r (v:dN): t' • p' v=rodV P0 o X ∅ v:=smul_inv_smul₀ (zero_lt_one.trans_le (verge_p P0 o X K_ tH)).ne' _
lemma pinch (P:P0.threshold=temp x) (U:Pane N)(t:dN): Agrees X (increment U (Prism.trunk P0 o t)) (Vmove x U (p' (t' • t))):=by
 rw [map_smul,leg_r P0 o X K_ tH t,←non_r U P0.B]; exact stoveV P0 o X ∅ P t
lemma peg_z (P:P0.threshold=temp x):∃ I:dN→L[ℝ]dN,‖I‖≤1∧∀ v:dN,temp x • p' v=Prism.trunk P0 o (I v):=by
 let I:dN→L[ℝ]dN:= highlight X; have ht:=verge_p P0 o X K_ tH; refine ⟨t'⁻¹ • I,le_trans ?_ (show t'⁻¹≤1 from inv_le_one_of_one_le₀ ht),fun v=>?_⟩
 · rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (zero_lt_one.trans_le ht)).le]; exact mul_le_of_le_one_right (inv_pos.mpr (zero_lt_one.trans_le ht)).le (Forge.high_nn X)
 have h:P0.threshold≠0:=P0.threshold_pos.ne'; have hx:=Prism.trunk P0 o; rw [←P]; unfold lineP rodV; simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, no_w,map_smul]; rw [smul_comm P0.threshold,smul_inv_smul₀ h]
 congr 1; funext i; by_cases w: pinPos i ⊆ X<;> simp [I,highlight,Prism.trunk,w] -- tune
variable (f:Pane N→ℂ)
lemma socks (p:P0.threshold=temp x)(U:Pane N)(w: U∈ Rue.litres P0.threshold X ∅)(u:∀ V W:Pane N,V∈Rue.litres P0.threshold X ∅→W∈Rue.litres P0.threshold X ∅→Agrees X V W → f V=f W)(q:Pence P0.order (fun i:dN=> f (Vmove x U (p' i))) 0 d): Signs P0 o (f ∘ increment U) (composeCost P0.order ((P0.order.factorial:ℝ)*d) t'):=by
 apply Prism.skills; let M:dN→L[ℝ]dN:= t' • ContinuousLinearMap.id ℝ dN; have hz:M 0=0:=M.map_zero
 have ht:= verge_p P0 o X K_ tH; have hx:‖M‖≤ t':=by unfold M; rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]; exact mul_le_of_le_one_right (zero_le_one.trans ht) (ContinuousLinearMap.norm_id_le ..)
 let Qy(y:dN):= f (Vmove x U (p' y)); have hv:= (show Allows P0.order Qy (M 0) (P0.order.factorial*d) from hz.symm ▸ q.pay).comp (allows_linear hx (by rw [M.map_zero,norm_zero]; exact zero_le_one.trans ht)); refine hv.germ ?_
 filter_upwards [Nor.lyreH P0 o X ∅ w, Nor.turfH P0 X ∅ w ((p').comp M) x] with i v t; rw [non_r] at v; exact (u _ _ v t (pinch P0 o X K_ tH p U i)).symm
lemma shoe (p:P0.threshold=temp x)(U:Pane N)(t:Signs P0 o (f ∘ increment U) d) : Allows P0.order (fun i:dN=> f (Vmove x U (p' i))) 0 d:=by
 obtain ⟨I,h,e⟩:= peg_z P0 o X K_ tH p; simp_rw [Vmove,e]; let F':= (f ∘ increment U)∘ Prism.trunk P0 o; have hx:Allows P0.order F' 0 d:= Prism.skin t
 change Allows P0.order (F'∘ I) 0 d; refine ⟨(show ContDiffAt ℝ (P0.order:ℕ∞ω) F' (I 0) from I.map_zero.symm ▸ hx.smooth).comp 0 I.contDiff.contDiffAt,fun j u=>?_⟩
 rw [Next.Foundations.jets_linear I (hx.smooth.of_le (Nat.cast_le.mpr u))]; exact ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (by simp only [prod_const,card_univ,Fintype.card_fin]; exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) h)).trans (hx.norm_le j u)))
end YM.CF.Feu
