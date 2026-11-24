import YM.CF.Roots.Halo
import YM.CF.Brood.Rim
import YM.CF.Brood.Quill
import YM.CF.Brood.Told
import YM.CF.Roots.Sail
import YM.CF.Fans.Cause
import YM.CF.Roots.Flux
import YM.CF.Roots.Melt
import YM.CF.Fans.Emit
import YM.CF.Neon.Park
import YM.CF.Fans.Moon
import YM.CF.Fans.Wake
import YM.CF.Fans.Pose
import YM.CF.Neon.Quay
import YM.CF.Neon.Lux
import YM.CF.Fans.Toll
import YM.CF.Rive.Lob
import YM.CF.Ups.Tree
import YM.CF.Ups.Shea
import YM.CF.Paxos.Pen
import YM.CF.Pso.Tide
import YM.CF.Pso.Wage
import YM.CF.Pso.Azim
set_option autoImplicit false
set_option maxHeartbeats 2200000
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
open Footprint Jade Py
-- earnings profiles quant issued b through \ell. Accept permit Rent
open Larch Vow Bake Mew Roots Rive Neon
local notation "BN"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
local notation "Θ"=> X.p.supportExponent
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→Site (mid N B))(K_ E0:Key J→ RegBudget (mid N B))(F_:Key J→ ForceBudget (mid N B))
variable (Xo Yo:Key J→ RegBudget (mid P B))(Zo:Key J→ ForceBudget (mid P B)) {G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} (Xi:Op SU.Slot){q:Chi}{h:ℝ}
local notation "Tz"=> Cube.node ∘ σ
local notation "P_"=> X.p
open Moto Hove Haro Tap
open Module
open scoped YM.CF.Mew
variable (Xq Y':BudgetPoint) {F E:Ξθ→ ArcΦ}{x' a' pΞ C_ζ:ℝ}
local notation "Kg"=> (Real.exp 1)
abbrev Hπ:=1+∑ i:Ξθ,‖Gior i‖
lemma hPπ : 0≤ Hπ:=add_nonneg zero_le_one (sum_nonneg fun _ _=>norm_nonneg _)
lemma basis_D(i:Ξθ):‖Gior i‖≤ Hπ:=(single_le_sum (fun i _=>norm_nonneg (Gior i)) (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one)
variable (L:Side)
local notation "xL"=> ((L.val:ℝ)⁻¹)
variable (z:ℂ)(w Q H A:ℝ)(pΩ:‖z‖≤ Real.exp 1)(g0:0 ≤ w)(hV:w ≤ Q*((L.val:ℝ)⁻¹)^5)(uQ:0<Q)(hH:1≤H)(hA:0≤A)
abbrev MF:= (Real.exp 1)*Hπ
abbrev Kmaxα:= 4*MF+4
abbrev αsmall (L:Side)(A:ℝ):= ((L.val:ℝ)⁻¹)*(3*MF+A+1)
-- threshold pulses. Axon envelope Ppa=λ*s. include. conditional Stage.Fl.
include pΩ g0 hV uQ hH hA
-- mixed Ψ fee scale.R.Act.Pin budget.
lemma subΛ (i:Ξθ) : let R:= cue_Φ Q H i; let s:= (L.val:ℝ)⁻¹; let a:= chipH L Q i; let B:=κprobe naxR L H (A*Q) w z R; let C:= κprobe nagR L H (A*Q) w z R; let k:=κprobe mintR L H (A*Q) w z R; 0 ≤ B∧0≤ C∧0≤k ∧ B≤ αsmall L A*a ∧ C ≤ αsmall L A*a+(if i.isLeft then MF*a else 0)∧ k≤ (3*MF*a + αsmall L A*a):=by
 intro v x a' B C L' -- shadow A,B.fok
 let a:= ‖z‖*‖v.1‖; let b:= (‖z‖*‖v.2.1‖*H^2); let c:= ‖z‖*‖v.2.2‖*H^2
 have he:0<x:=by unfold x; positivity
 have hv:x≤1:= inv_le_one_of_one_le₀ (by exact_mod_cast L.property)
 have ha:0 ≤ a:=by unfold a; positivity
 have hb:0 ≤ b:=by unfold b; positivity
 have hc:0≤ c:=by unfold c; positivity
 have ht:=basis_D i; have hm:0 ≤ MF:=mul_nonneg (Real.exp_pos _).le hPπ
 have hg:0 ≤ αsmall L A:=by unfold αsmall; positivity
 obtain ⟨xq,yq,zq⟩:= norms_t (Gior i) Q H uQ (zero_lt_one.trans_le hH); let F:=Gior i; let v_:ℝ:= MF*Q
 have hu(x:ℝ)(p:0 ≤ x)(h:x≤ ‖Gior i‖) : ‖z‖*(Q*x)≤ MF*Q:=(mul_le_mul pΩ (mul_le_mul_of_nonneg_left (h.trans ht) uQ.le) (mul_nonneg uQ.le p) (Real.exp_pos _).le).trans_eq (by unfold MF; ring)
 have hK:a ≤ v_:=by unfold a v cue_Φ; rw [zq]; exact hu _ (norm_nonneg _) ((norm_fst_le _).trans (norm_snd_le _))
 have hL:b ≤ v_:=by unfold b v cue_Φ; rw [mul_assoc,xq]; exact hu _ (norm_nonneg _) (norm_fst_le _)
 have hC:c ≤ v_:=by unfold c v cue_Φ; rw [mul_assoc,yq]; exact hu _ (norm_nonneg _) ((norm_snd_le _).trans (norm_snd_le _))
 have he' : Q*x^4≤ a' :=by unfold a' x; cases i <;> first|exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one he.le hv (by norm_num: (3:ℕ) ≤ 4)) uQ.le|exact le_rfl
 have hB: B≤ αsmall L A * (Q*x^4):=by
    change x^5* (a+b+c+A*Q)+w ≤ _; exact (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hK hL) hC) le_rfl) (pow_nonneg he.le _)) hV).trans_eq (by unfold x v_ αsmall; ring)
 have hW:w≤ αsmall L A*a':=by refine le_trans (le_trans ?_ hB) (mul_le_mul_of_nonneg_left he' hg); exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg he.le _) (add_nonneg (add_nonneg (add_nonneg ha hb) hc) (mul_nonneg hA uQ.le)))
 let i_:= i
 have hp: x^3*b ≤ (if i.isLeft then MF*a' else 0):=by
    unfold a'; cases i with
    | inl k=> exact (mul_le_mul_of_nonneg_left hL (pow_nonneg he.le _)).trans_eq (by unfold v_; change x^3*(MF*Q)=MF*(Q*x^3); ring)
    | inr k=> unfold b v cue_Φ; rw [mul_assoc,xq,Aθ_i]; simp only [Prod.fst_zero,norm_zero,mul_zero,Sum.isLeft_inr, Bool.false_eq_true,↓reduceIte]; exact le_rfl
 have hψ: (if i.isLeft then MF*a' else 0)≤ MF*a':=by split; exact le_rfl; exact mul_nonneg hm (chipX _ _ uQ _).le
 change 0≤ naxR x a b c (A*Q) w∧0 ≤ nagR x a b c (A*Q) w∧0 ≤ mintR x a b c (A*Q) w ∧_≤_∧ _≤_ ∧_≤_
 have hxP: 0 ≤ B:=by change 0 ≤ naxR x a b c (A*Q) w; unfold naxR; positivity
 let hΨ:=hB.trans (mul_le_mul_of_nonneg_left he' hg); refine ⟨hxP,(by unfold nagR; exact add_nonneg hxP (mul_nonneg (pow_nonneg he.le _) hb)),(by unfold mintR; positivity),hΨ, add_le_add hΨ hp,?_⟩ -- K bound uses λ* includes x⁵*A Q+w already within B
 have hA': x^4*a≤ MF*a':= (mul_le_mul_of_nonneg_left hK (pow_nonneg he.le _)).trans (by unfold v_; rw [show x^4*(MF*Q)= MF*(Q*x^4) from by ring]; exact mul_le_mul_of_nonneg_left he' hm)
 have hC': x^4*c ≤ MF*a':= (mul_le_mul_of_nonneg_left hC (pow_nonneg he.le _)).trans (by unfold v_; rw [show x^4*(MF*Q)= MF*(Q*x^4) from by ring]; exact mul_le_mul_of_nonneg_left he' hm)
 change x^4*a+x^3*b+x^4*c+x^5*(A*Q)+ w ≤ _
 have hy:x^5*(A*Q)+w ≤ B:=add_le_add_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (add_nonneg (add_nonneg ha hb) hc)) (pow_nonneg he.le _)) _
 nlinarith only [hy,hΨ,hA',hp.trans hψ,hC']
omit pΩ g0 hV uQ hH hA
open Tune
abbrev start_M:= Real.exp (-1)/4
lemma αG:0<start_M:= div_pos (Real.exp_pos _) (by norm_num)
lemma lit_h {z:ℂ}(p:Real.exp (-1)≤‖z‖)(s:xL^4/4≤ qCorset Xq.threshold Y'.threshold (L.val:ℝ)) (x:BadgeΦ): start_M* ‖x.1‖ ≤ ‖(Vera L Xq Y' z x).1‖ ∧ start_M*‖x.2‖ ≤ ‖(Vera L Xq Y' z x).2‖:=by
 let A:= Vera L Xq Y' z x; let r:= start_M; have h:r ≤ ‖z‖:= by unfold r start_M; linarith only [p,Real.exp_pos (-1)] -- alpha unfolded? fix
 let C:= deal_G L Xq Y'; have he:(1/4:ℝ) ≤ C:= (le_div_iff₀ (by positivity)).mpr (by linarith); have hx: r ≤ ‖((C:ℂ)*z)‖:=by rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by linarith : 0≤C)]; exact (Eq.le (show r= 1/4*Real.exp (-1) from (by unfold r start_M; ring))).trans (mul_le_mul he p (Real.exp_pos _).le (by linarith))
 change r*‖x.1‖ ≤ ‖z • (x.1)‖ ∧ r*‖x.2‖≤ ‖(A).2‖; constructor; · rw [norm_smul]; exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
 rw [Prod.norm_def]; rcases le_total ‖x.2.1‖ ‖x.2.2‖ with u|u
 · rw [max_eq_right u]; apply le_trans ?_ (norm_snd_le A.2); change _ ≤ ‖z • x.2.2‖; rw [norm_smul]; exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
 rw [max_eq_left u]; apply le_trans ?_ (norm_fst_le A.2); change _ ≤ ‖((C:ℂ)*z) • x.2.1‖; rw [norm_smul]; exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
end YM.CF.Py
