import Weft.Bulletin
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
import Compass.Prime
import YM.CF.Reef.Pole
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
variable (Q:J→ℝ)(qE:J→ArcΦ)(qΨ:J→ ArcΦ)(s:J→ℂ)
variable {Vp Va Bk Cμ Wη Eμ Cx ZΨ QΦ ξQ:ℝ} -- remove
variable (Fκ:Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xi q kL h Vp Va σ Q qE K_ F_ qΨ s Bk Cμ Wη Eμ Cx ZΨ QΦ)
open Roots Mew Rive Oise
variable {α:Type}[DecidableEq α]
open scoped YM.CF.Mew
local notation "Ω"=> mid N B
local notation "qμ"=> (Cube.node ∘σ)
local notation "Ωk"=> MixT σ
open Drift Oise
attribute [-instance] instDecidableEqLex
open Compass
namespace Dyad
open Taxi Moto Compass Ione Tune
open Push.Local AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes
open Reef
variable {n0:Side}
lemma petalsCharge(U: Pane n0)(o:Site (More n0))(b:PlaqAxes):petals (Reef.echo U) o b=Reef.frolic (petals U o b):=by
 have r(a b:Step): StressFlux.plate (echo U) o a b= frolic (StressFlux.plate U o a b):=by unfold StressFlux.plate; rw [Reef.echo_t,Reef.swing]
 unfold AnalyticBridge.VerifiedReset.petals StressFlux.clover StressFlux.stencil; simp only [r,map_sub,map_smul] -- inspect
lemma eco_s (K:PlaqAxes→ℝ)(U:Pane n0)(o:Site (More n0))(s:Sweep n0)(b:PlaqAxes): ‖petals (flashA s U) o b‖ = ‖petals U (boxA s o) (PlaqAxes.rotate s.s b)‖:=by
 let T:= pull s.s ((assembly n0).embed s.b) U
 have hs: ‖petals T o b‖=‖petals U (boxA s o) (PlaqAxes.rotate s.s b)‖:=by rw [sitA, petals_moves,reframe_norm]; rfl
 cases z:s.charge <;> rw [Skye.revoke,z]
 · exact hs
 change ‖petals (Reef.echo T) o b‖=_; rw [petalsCharge, frolic.norm_map]; exact hs
#check reframe_norm
/- Clover scalar simplifies to quad with real decor rows, τ independent! Actually kerPτ coefficients.Delta. -/
abbrev Inkprice(a:ℝ)(Q:BudgetPoint)(o:Site (More n0))(U:Pane n0):ℝ:= (∑ b:PlaqAxes, a*((decor b):ℝ)/Q.threshold^2 * ‖petals U o b‖^2) / 2
lemma paint_r (a:ℝ)(i j:PlaqAxes):paintS (a:ℂ) i j= if i=j then ((a*(decor i:ℤ):ℝ):ℂ) else 0:=by
 unfold paintS decor; split_ifs<;> simp_all -- syntax ℕ casts
lemma proprietor (X:ℝ)(W:BudgetPoint)(o:Site (More n0))(U:Pane n0):kerP o W (paintS (X:ℂ)) U=(Inkprice X W o U:ℝ):=by
 have ht:∀ q:PlaqAxes→PlaqAxes→ℝ, counter q o U = (∑ i:PlaqAxes,∑ j:PlaqAxes,q i j*inner ℝ (petals U o i) (petals U o j))/2:=fun _=>rfl -- inner ambiguity
 have he(i): (∑ j:PlaqAxes, ((paintS (X:ℂ) i j).re/W.threshold^2)*inner ℝ (petals U o i) (petals U o j))= X*(decor i:ℝ)/ W.threshold^2*‖petals U o i‖^2:=by
    rw [Finset.sum_eq_single i,paint_r,if_pos rfl,Complex.ofReal_re,real_inner_self_eq_norm_sq]
    · intro b _ p; rw [paint_r,if_neg p.symm,Complex.zero_re,zero_div,zero_mul]
    intro p; exact (p (mem_univ ..)).elim
 have heq(i j:PlaqAxes): (paintS (X:ℂ) i j).im=0:=by rw [paint_r]; split <;> rfl
 unfold kerP; rw [ht,ht]
 simp_rw [he,heq,zero_div,zero_mul]; simp; first|rfl|done
 -- remaining
lemma tollDecor (w:staff n0)(i:PlaqAxes) : (decor (PlaqAxes.rotate w.val.s i):ℝ)= taxK w*(decor i:ℝ):=by
 have ht:= sail_decide w.val.s w.property i; rw [ht,Int.cast_mul]; unfold taxK taxF taxB times; split_ifs<;>simp
lemma ink_raise (X:ℝ)(w:staff n0)(Q:BudgetPoint)(o:Site (More n0))(U:Pane n0): Inkprice X Q o (Spire.flashA w.val U)= taxK w*Inkprice X Q (boxA w.val o) U:=by
 let e:=PlaqAxes.transform w.val.s; unfold Inkprice; rw [←mul_div_assoc, mul_sum]; refine congrArg (fun t:ℝ=>t/2) ?_; apply sum_equiv e (fun i=>by simp) (fun i _=>?_)
 rw [eco_s (fun _=>0)]; change _= taxK w*(X*(decor (PlaqAxes.rotate w.val.s i):ℝ)/_*_)
 rw [tollDecor]; have ht(v:ℝ): taxK w*(X*(taxK w*v))=X*v:=by rw [mul_left_comm X,←mul_assoc (taxK w) (taxK w), (prop1 w).2,one_mul]
 rw [←mul_assoc,←mul_div_assoc,ht]
 rfl
#print axioms ink_raise
#print axioms proprietor
end Dyad
end YM.CF.Py
end
