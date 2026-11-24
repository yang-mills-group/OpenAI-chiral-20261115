import YM.CF.Song.Height
import YM.CF.Song.Fish
import YM.CF.Song.Beat
import YM.CF.Sere.Uinta
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Ione Lilt Nor Larch Beau Vow Sour Glyph
lemma crown_T(P_:BudgetPoint)(R:Patch)(F Pk M0:ℝ→ℝ)(t:sizeK R.L 1 F)(ht:∀ᶠ x:ℝ in atTop,0 < F x)(h:sizeK R.L 3 Pk)(k0 j0:ℕ)(hp:Chill_v M0): let V(x):= rateΓ (hall_P P_ x) (F x) wΨ;∃ X:ℝ→ℝ, Chill_v X∧Jade.warmK X∧ Litt R 2 (growC j0 k0 R X)∧∀ᶠ x:ℝ in atTop,M0 x+V x ≤1∧ rainX R 2 x* Pk x+Real.exp 1*(V x+M0 x) ≤ X x:=by
 intro V; have hp':=fee_Q P_ F t; let W:= zeST P_ F; have hw:Tendsto (fun i=> (1-W i)⁻¹) atTop (𝓝 1):=by simpa only [sub_zero,inv_one] using ((tendsto_const_nhds (x:=(1:ℝ))).sub hp'.spine|>.inv₀ (show (1:ℝ)-0≠0 by simp)); -- tune
 have hu: sizeK R.L 0 (fun x=>(1-W x)⁻¹):= (sizeK.mild _ 2).cost_d (hw.abs.eventually (ge_mem_nhds (by norm_num : |(1:ℝ)| < |(2:ℝ)|)))
 have he:Chill_v V:= by unfold V rateΓ; simp_rw [pow_zero,mul_one]; exact Chill_v.coin (t.tint hu); -- tune
 let Y(x):=rainX R 2 x*Pk x+Real.exp 1*(V x+M0 x); have hq:Chill_v Y:= Chill_v.noteR (Chill_v.coin (rockP 2 h)) ((he.noteR hp).cheap _)
 let X(x):= |Y x|+F x; have hX:Chill_v X:= Chill_v.noteR (hq.trend (Eventually.of_forall fun i=> (abs_abs (Y i)).le)) (Chill_v.coin t); have hy: Jade.warmK X:= (ht.and ((chant_A hX).spine_a.eventually (ge_mem_nhds (by norm_num : (0:ℝ)< 1/2)))).mono fun x t=>⟨add_pos_of_nonneg_of_pos (abs_nonneg _) t.1,t.2⟩
 refine ⟨X,hX,hy,?_ ,?_⟩
 · have hk:Tendsto (fun x=> (1-ink_P X x)⁻¹) atTop (𝓝 1):= by
      have hk:Tendsto (fun x=>1-ink_P X x) atTop (𝓝 1):= by simpa only [sub_zero] using Tendsto.sub (tendsto_const_nhds (x:=(1:ℝ))) ((chant_A hX).spine_a)
      simpa only [inv_one] using hk.inv₀ (show (1:ℝ) ≠0 from one_ne_zero)
   have hV:BoreP (fun x=>(1-ink_P X x)⁻¹):= (BoreP.still 2).tune (hk.abs.eventually (ge_mem_nhds (by norm_num: |(1:ℝ)| < |(2:ℝ)|))) -- tune reuse
   let Q(x):= reserveT j0 k0 (radiusB x) 1*(X x*(1-ink_P X x)⁻¹); have hk:BoreP Q := (Nor.vale_u ..).grip (hX.pane.grip hV); unfold growC; apply Litt.gearX hk; filter_upwards with x; unfold Q rainX ink_P; simp only [inv_inv,pow_zero,mul_one]; ring
 filter_upwards [(hp.noteR he).spine_a.eventually (ge_mem_nhds zero_lt_one),ht] with x v p; exact ⟨v,(le_abs_self _).trans (le_add_of_nonneg_right p.le)⟩
abbrev Qα(P_:BudgetPoint)(H Θ:ℝ)(R:Patch)(F:ℝ→ℝ)(x:ℝ):=νC P_ H*(F x+Scales.g SU.group R.L x^2)
lemma subsidy_K(R:Patch): Litt R 2 (fun x=> Scales.g SU.group R.L x^2):=Litt.gearX (BoreP.still 1) (Eventually.of_forall (fun i=> Eq.symm (one_mul ..)))
lemma lent(P_:BudgetPoint)(R:Patch)(H Θ:ℝ)(f:ℝ→ℝ)(hf:sizeK R.L 2 f)(hp:Chill_v (Fp f)) :sizeK R.L 2 (Qα P_ H Θ R f)∧Chill_v (Fp (Qα P_ H Θ R f)):=⟨(hf.accrue (subsidy_K R).height_r).scale _, plunge_L _ (plume_L hp (coin_p (subsidy_K R)))⟩
end YM.CF.Py
