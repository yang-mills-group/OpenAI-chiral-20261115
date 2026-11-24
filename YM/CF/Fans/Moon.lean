import YM.CF.Neon.Lux
import YM.CF.Neon.Vex
import YM.CF.Hype.Tram
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
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
variable{N P B:Side}{S_O:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S_O}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
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
variable {u_O Hh pKe qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Moto
open Vow Lilt Larch Bake Rue
open Prism Hove Oise
-- primary picture: rank 0 pressure (global scalar extracted separately), 3 PH weight and 4 derivatives, 4 radial. representation.H.
open Taxi Hope Mew
local notation "Θ"=> mid N B
local notation "Η"=> Scree.Hub (mid N B)
-- Total motion receipt ONE SOURCE. c offsets only constrained at singleton.Fo.Press.Priority. covariance later. mask pay separately.
variable (o:Site (mid N B)) (p0:BudgetPoint) (h ν :ℝ)
local notation "Tκ"=> Cube.node o
local notation "Cκ"=> (Φrap Θ o 10)
variable (L0:ℕ)(Vκ:ℝ)(Ψ: DayT p0.order Vκ)(uK:0 ≤ Vκ)
variable {I:Type}[Fintype I][LinearOrder I]
local notation "ΦΞ"=> Key I
variable (σ:I→ Site (mid N B))(Q':I→ Cusp (mid N B))(W:I→ℝ)(Kχ:I→ ℂ) -- fix
variable (u:PathGap σ p0.B L0)(hZ:∀ i:I,∀ x:Aura (mid N B),Cube.node (σ i) ∉x.val→ Q' i x=0) (Mp0:I→Aura (mid N B)→ℝ) (gp:∀ i, Anuk (Q' i) (Mp0 i) p0 h) (Hp:∀ i,SparF (σ i) p0 (Mp0 i) L0)(pK:∀ i,∀ x:Seat (mid N B), tallB (Mp0 i) p0.B (p0.supportExponent+1+1) x ≤ W i)
local notation "ω"=> Aura Θ
local notation "mζ"=> Mp0
local notation "Lx"=> ((L0+1)*(4*p0.B+2)+2*p0.B)
variable (Tz:ℕ)
abbrev GapN (σ:I→ Site (mid N B))(B0 L T:ℕ):Prop:=∀ y: Seat (mid N B),(univ.filter (fun i:I=> near_H ((L+1)*(4*B0+2)+2*B0) y (σ i))).card ≤ T
variable (vK:GapN σ p0.B L0 Tz)
include vK gp Hp pK
local notation "Zκ" z:max=> (∑ i:I,‖(z:Key I) i‖ • (Mp0 i))
lemma moon_Z (z: Key I)(f:ℝ)(p:0 ≤ f)(hw:∀ i,‖z i‖*(W i) ≤ f): Anuk (Φstack Q' z) (Zκ z) p0 h ∧∀ y:Seat Θ,tallB (Zκ z) p0.B (p0.supportExponent+1+1) y ≤ Tz*f:=by
 let Q:= Zκ z; refine ⟨⟨?_,?_⟩,?_⟩ -- 
 · intro i; rw [Finset.sum_apply]; exact sum_nonneg fun j _=>mul_nonneg (norm_nonneg _) ((gp j).1 i)
 · intro i D p t; unfold Φstack; simp_rw [Finset.sum_apply]; exact Medal.sumP _ _ _ fun k _=> num_h _ _ _ 0 ((gp k).2 i D p t) (z k)
 intro y; let A:=p0.supportExponent+1+1; let K(i):=‖z i‖ • Mp0 i; have he:tallB Q p0.B A y=∑ i:I,‖z i‖ * tallB (Mp0 i) p0.B A y:=by
    unfold Q tallB; simp_rw [Finset.sum_apply,sum_mul]; rw [Finset.sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [mul_sum]; exact sum_congr rfl fun j _=> mul_assoc ..
 change tallB Q p0.B A y≤_; rw [he]
 let T:=univ.filter fun i:I=> near_H Lx y (σ i); let F(i:I):=‖z i‖* tallB (Mp0 i) p0.B A y
 have hz:∑ i∈T,F i=∑ i:I,F i:= Finset.sum_subset (filter_subset ..) fun j _ t=> by
    have hp:¬ near_H Lx y (σ j):=fun w=>t (mem_filter.mpr ⟨mem_univ _,w⟩); unfold F; rw [mν_s L0 p0 (σ j) _ (Hp j) y hp,mul_zero]
 change ∑ i:I,F i≤_; rw [←hz]; refine le_trans (sum_le_sum (g:=fun _=>f) (fun i _=>(mul_le_mul_of_nonneg_left (pK i y) (norm_nonneg _)).trans (hw _))) ?_; rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (vK y)) p
end YM.CF.Neon
