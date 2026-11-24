import YM.CF.Hype.Tres
import YM.CF.Hype.Rome
import YM.CF.Hype.Flash
import YM.CF.Hype.Mora
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
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Prism Haro Tap Oath
open Larch
-- decays compared with all plow^•
abbrev Chill_v(F:ℝ→ℝ):Prop:= ∀ n:ℕ, Tendsto (fun x=> plow x^n *F x) atTop (𝓝 0)
namespace Chill_v
variable{E F:ℝ→ℝ}{Q:Patch}
lemma cash (p:Chill_v E)(h:sizeK Q.L 1 F): Chill_v F:=by intro n; exact (((BoreP.relB.self n).creditK _).tint h).spine -- tune p unused
lemma coin (h:sizeK Q.L 1 F): Chill_v F:=fun n=>(((BoreP.relB.self n).creditK _).tint h).spine
lemma noteR (p:Chill_v E)(h:Chill_v F):Chill_v fun i=> E i+F i:=by intro n; simp_rw [mul_add]; simpa only [add_zero] using Tendsto.add (p n) (h n)
lemma cheap(p:Chill_v E)(v:ℝ):Chill_v fun i=> v* E i:= by intro n; simp_rw [mul_left_comm _ v]; simpa only [mul_zero] using (p n).const_mul v
lemma trend(p:Chill_v E)(h:∀ᶠ x in atTop,|F x|≤ |E x|):Chill_v F:=by
 intro n; rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) _ (tendsto_zero_iff_norm_tendsto_zero.mp (p n)); filter_upwards [h] with i t; exact (norm_mul ..).trans_le (le_trans (mul_le_mul_of_nonneg_left t (norm_nonneg _)) (le_of_eq (norm_mul ..).symm))
lemma leanB (p:Chill_v E)(q:BoreP F) :Chill_v (fun x=> F x * E x):=by
 obtain ⟨C,i,h,t⟩:=q.pace; have ht:Chill_v (fun x=> plow x^i * E x):=by
    intro n; simp only [← mul_assoc,←pow_add]; exact p _
 refine (cheap ht C).trend ?_; filter_upwards [t] with x v; rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg h,←mul_assoc,abs_of_nonneg (pow_nonneg (show 0 ≤ plow x from zero_le_one.trans (Scales.size x)) _)]; exact mul_le_mul_of_nonneg_right v (abs_nonneg _)
lemma spine_a (p: Chill_v E):Tendsto E atTop (𝓝 0):=by simpa only [pow_zero,one_mul] using p 0
lemma pane (p: Chill_v E): BoreP E:= (BoreP.still 1).tune ((spine_a p).abs.eventually (show ∀ᶠ x in 𝓝 (|(0:ℝ)|), x≤ (|(1:ℝ)|) from ge_mem_nhds (by norm_num)))
end Chill_v
lemma fiW (x:ℝ): fiery SU.group x 1=temp x:=by simp [fiery,betaF]
lemma port_G(R:Patch) :∀ᶠ x:ℝ in atTop, Scales.g SU.group R.L x ≤ Scales.g SU.group 1 x:=by
 have he: ∀ x:ℝ, Scales.y SU.group 1 x≤ Scales.y SU.group R.L x:=by intro x; unfold Scales.y betaF; have h: 0≤ Real.log (R.L.val:ℝ):=Real.log_nonneg (by exact_mod_cast R.L.property); simp only [PNat.val_ofNat,Nat.cast_one,Real.log_one,mul_zero,add_zero]; exact le_add_of_nonneg_right (mul_nonneg (Work.E07.slope_nonneg _) h)
 filter_upwards [(year SU.group 1).eventually_gt_atTop 0] with x t; apply (show (Real.sqrt _)⁻¹ ≤ (Real.sqrt _)⁻¹ from inv_anti₀ (Real.sqrt_pos.2 t) (Real.sqrt_le_sqrt (he x)))
local notation "CF'"=> Chill_v
local notation "f∎"=> Scales.g SU.group R.L
lemma clove_p (R:Patch) : CF' fun x=> Scales.g SU.group R.L x/ temp x:=by -- public escape: ratio.B dominated.P_r1
 let e:= (Scales.p SU.group 1); have he: CF' (fun x=> 1/e x):=by
    intro n; have ht:= cover_pay SU.group 1 n (a:=1) (by norm_num); simp_rw [Real.rpow_one] at ht; exact ht.congr fun x=>by unfold plow; unfold e; ring
 apply he.trend; filter_upwards [port_G R,(Scales.year SU.group R.L).eventually_gt_atTop 0,(Scales.year SU.group 1).eventually_gt_atTop 0] with x t hx hv; rw [abs_div,abs_of_pos (Scales.gauge _ _ hx)]
 let z:= Scales.g SU.group 1 x; have hh:= Scales.pos SU.group 1 x; have hp:= Scales.gauge SU.group 1 hv; rw [←fiW x,fi,abs_of_pos (mul_pos hp hh)]; exact (div_le_div_of_nonneg_right t (mul_pos hp hh).le).trans_eq (by change z / (z* e x)=_; rw [abs_of_pos (by positivity)]; unfold z e; field_simp) -- power cost
variable {Em Qy:ℝ→ℝ}
lemma coin_p(h:Litt R 2 Em):Chill_v (fun x=>Em x/ (temp x)^2):=by
 let k(x):=Scales.g SU.group R.L x/ temp x; let F:= fun x=> Em x/ Scales.g SU.group R.L x^2
 have ht:= clove_p R; apply ((Chill_v.leanB (Chill_v.leanB ht (Chill_v.pane ht)) h)).trend ?_ -- tune replace
 filter_upwards [(Scales.year SU.group R.L).eventually_gt_atTop 0] with x t; refine Eq.le (congrArg _ ?_); have he:=Scales.gauge SU.group R.L t; rw [show F x*_ = F x*k x^2 from (by unfold k F; ring),div_pow]; unfold F; field_simp -- tune
abbrev dleaf (L:Side)(x:ℝ):ℝ:=Scales.g SU.group L x * temp x
lemma dev_R(R:Patch): sizeK R.L 2 (dleaf R.L)∧Chill_v (fun x=> dleaf R.L x/temp x^2):=by
 refine ⟨(sizeK.main _).tint (sizeK.tempo _),(clove_p R).trend (Eventually.of_forall fun x=>?_ )⟩; unfold dleaf; by_cases h:temp x=0; simp [h]; apply Eq.le; congr 1; field_simp -- zero fallback
end YM.CF.Py
