import YM.CF.Paxos.Rost
import YM.CF.Ups.Gul
set_option autoImplicit false
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
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
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
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
variable {x':ℕ→ℝ}(t:Tendsto x' atTop atTop){L':ℕ→ℕ} (U':∀ i',SpanPS V a p i N0 J q h R0 δ (x' i') (L' i'))
local notation "N_X"=> rimZ V N0 J (x':=x')
local notation "S_X"=> (fun i=>mid ((rimZ V N0 J (x':=x')) i) B)
local notation "Φ"=> (fun i=>Lr (x' i))
local notation "Kχ"=> (fun i=> (U' i).E 0)
variable(hv:1 ≤ h)
include U' t hv
variable {KX b' vL c' l' b a' D E' C0 h1 r:ℝ}{kT d' :ℕ} (P_: Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ D E' C0 h1 r d')(hX:C0 ≤ h)
open Graph Onyx Pyx Brioche
universe a0
include P_ Q hX
local notation "cpT"=> (b'/(2*Nova.poseX))
local notation "zε" i=> (Real.sqrt i)⁻¹ /4
local notation "MJ" x=> (cell (oYY V N0 J x) B R.L 0)
local notation "Y0"=> (fun i:ℕ=>(U' i).Y 0)
local notation "X0"=> (fun i:ℕ=>(U' i).E 0)
private def spec_PS (X:Side)(x η w:ℝ):= Graph.gainS (More X) ((Real.sqrt x)⁻¹ /4)*Real.exp (-stoutY (More X) x (4*((Real.sqrt x)⁻¹/4)) K.top.clip.direct (temp x) K.top.paths V.W.bar) *Roe.horn X η*w
local notation "μt"=> spec_PS V
lemma zα :∀ᶠ i in atTop,0 < spec_PS V (cell (oYY V N0 J (x' i)) B R.L 0) (x' i) b (b'/(2*Nova.poseX)/2) ∧ spec_PS V (cell (oYY V N0 J (x' i)) B R.L 0) (x' i) b (b'/(2*Nova.poseX)/2) ≤ ‖Complex.exp (-((U' i).E 0).v)*partitionZ ((U' i).E 0) U ((U' i).Y 0)‖ :=by
 let pY:=sham_k V a p i N0 J q h R0 δ t U' hv; let X(i):= (U' i).Y 0; have hT:∀ i,Graph.SkinT ((U' i).E 0) (X i) d:=by
    intro i; let Z:= (U' i).scale; let F:= (Z.roof 0).paid; let F':Roof _ J.k d J.n (X i):={F with paid:=fun i=>(F.paid i).shrink J.hr.le}; exact Mint.Stop.sage _ _ _ F' ((Z.note.owns 0 (Nat.zero_le _)).width ▸ Z.pole 0)
 have hx:= P_.pos; have hg:= P_.rP; have hw:0 < cpT/2:=by have h:= Nova.pose_p; positivity
 filter_upwards [Roe.fog P_ pY,(Roe.costR P_ pY X (Eventually.of_forall hT) Q hX).1, t.eventually_gt_atTop 0] with i ⟨p,v⟩ ⟨A,G,V',x,Z,u,hk,pU⟩ t
 constructor
 · unfold spec_PS Graph.gainS Mint.Roe.horn; have h:= Ember.pinch_pos (cell (oYY V N0 J (x' i)) B R.L 0); positivity
 let n:=cell (oYY V N0 J (x' i)) B R.L 0; let f:= (Real.sqrt (x' i))⁻¹ /4; let z' := X0 i; have he:z'.beta=x' i:= (U' i).scale.note.color.trans (U' i).scale.day.unit; change Graph.gainS (More n) f*Real.exp (-stoutY (More n) z'.beta (4*f) K.top.clip.direct (temp (x' i)) K.top.paths V.W.bar)* Roe.horn n b ≤ _ at p; rw [he] at p; exact le_trans (mul_le_mul_of_nonneg_right p hw.le) hk
omit U' t
lemma Ωnorm :∀ᶠ x:ℝ in atTop, ∃ ℓ:ℝ,0 < ℓ∧∀ l:ℕ,∀ X:SpanPS V a p i N0 J q h R0 δ x l,ℓ≤ ‖Complex.exp (-(X.E 0).v)*partitionZ (X.E 0) U (X.Y 0)‖:=by
 have hh:∀ᶠ x:ℝ in atTop,0<μt (MJ x) x b (cpT/2):=(eventually_gt_atTop (0:ℝ)).mono fun x p=>by
    unfold spec_PS Graph.gainS Mint.Roe.horn; have he:=Ember.pinch_pos (MJ x); have t:=P_.pos; have h:=P_.rP; have k:=Nova.pose_p; positivity
 suffices hv:∀ᶠ x:ℝ in atTop, ∀ l:ℕ,∀ X:SpanPS V a p i N0 J q h R0 δ x l,spec_PS V (MJ x) x b (cpT/2)≤ ‖Complex.exp (-(X.E 0).v)*partitionZ (X.E 0) U (X.Y 0)‖ by exact (hh.and hv).mono fun x ⟨p,q⟩=>⟨_,p,q⟩
 rw [eventually_atTop]; by_contra! hx
 choose g hG l X t using fun i:ℕ=>hx (i:ℝ); have h:= zα V a p i N0 J q h R0 δ (tendsto_atTop_mono hG tendsto_natCast_atTop_atTop) X hv P_ Q hX; exact h.exists.elim fun i v=> (not_le.mpr (t i)) v.2
end YM.CF.Py
