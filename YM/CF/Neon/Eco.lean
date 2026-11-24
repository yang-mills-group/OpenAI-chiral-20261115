import YM.CF.Neon.Aps
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
variable {u_O Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
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
-- combine annual. Evo shape only.Clock mask.C. 
local notation "ζP"=> p0
local notation "EA" x:max=> (Δv p0 Vκ*x)
local notation "KA" x:max=> (Extr_h L0 p0 Vκ*x)
variable (F G' T_:Copy (mid N B))(gℓ dℓ bℓ kℓ yμ δP:ℝ)
-- Combined relative norm lower on Aqua. Canvas.P. Lκ may independent of Ltc but domain filter set. Error Ψ general chooses Z∈Dome(P,Pe). 
variable (TΦ:Skate)(TΨ:Dome)
local notation "ρx"=> (2*peka_H p0.power)
variable (Eℓ E0 d0:ℝ)
local notation "Pσ"=> (yμ+δP+E0)
local notation "Z_"=> (gℓ+dℓ+bℓ)
variable (ηρ ηE ηK:ℝ)(T1:∃ G K Tv GΦ GΨ,Ice L0 o p0 h (Δv p0 Vκ*gℓ) (Extr_h L0 p0 Vκ*gℓ) gℓ F G K Tv (GΦ,GΨ)∧ ‖GΦ-TΦ‖ ≤ d0+2*yμ ∧ ‖GΨ‖*h^2≤ 2*peka_H p0.power*yμ)(T2:∃ G K Tv GΦ GΨ,Ice L0 o p0 h (Δv p0 Vκ*dℓ) (Extr_h L0 p0 Vκ*dℓ+kℓ) dℓ G' G K Tv (GΦ,GΨ) ∧ ‖GΦ‖≤ δP∧ ‖GΨ-TΨ‖*h^2 ≤ 2*peka_H p0.power*δP)(T3:∃ E c KΨ GΦ GΨ, Ice L0 o p0 h (Δv p0 Vκ*bℓ) (Extr_h L0 p0 Vκ*bℓ) bℓ T_ E KΨ c (GΦ,GΨ) ∧ ‖GΦ‖ ≤ bℓ ∧ ‖GΨ‖ * h^2 ≤2*peka_H p0.power *bℓ)
local notation "Tµ"=> yμ+δP+bℓ
include T1 T2 T3
lemma era_X (A:Copy (mid N B))(p:A =F+G'+T_)(he:0 ≤ h) :∃ E Q KΨ GΦ GΨ,Ice L0 o p0 h (EA Z_) (KA Z_ + kℓ) Z_ A E Q KΨ (GΦ,GΨ)∧ ‖GΦ-TΦ‖≤ d0 +2*yμ +δP+bℓ∧ ‖GΨ-TΨ‖*h^2 ≤ (2*peka_H p0.power)*(yμ+δP+bℓ):=by
 obtain ⟨A',K1,t1,B1,P1,z,w,v⟩:= T1; obtain ⟨G0,K2,t2,B2,P2,hx,hy,u⟩:=T2; obtain ⟨A0,t3,K3,B3,P3,a,t,g⟩:=T3; let Z:= Ice.plan_ADD o L0 (Ice.plan_ADD o L0 z hx he) a he; rw [p]; refine ⟨A'+G0+A0,K1+K2+K3,t1+t2+t3,B1+B2+B3,P1+P2+P3,?_,?_,?_⟩
 · rw [mul_add (Δv p0 Vκ) (gℓ+dℓ),mul_add (Δv p0 Vκ) gℓ, mul_add (Extr_h L0 p0 Vκ) (gℓ+dℓ),mul_add (Extr_h L0 p0 Vκ) gℓ]; -- cancellation KA kℓ
   rw [show KA gℓ+ KA dℓ+KA bℓ+kℓ=KA gℓ+(KA dℓ+kℓ)+KA bℓ from by ring]; exact Z
 · rw [add_sub_right_comm, add_sub_right_comm B1]; exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add w hy)) t)
 rw [add_sub_right_comm,add_sub_assoc]; rw [mul_add,mul_add]; apply le_trans (mul_le_mul_of_nonneg_right (norm_add_le ..) (sq_nonneg _)); rw [add_mul]; refine add_le_add ?_ g; apply le_trans (mul_le_mul_of_nonneg_right (norm_add_le ..) (sq_nonneg _)); rw [add_mul]; exact add_le_add v u
omit T1 T2 T3
variable (y:Tap.Pal)(g':Dome)(α0 β':ℝ) (W:ArcΦ)(JΨ:Tap.Pal)(JΦ:Dome)
lemma lo_ρ (w:Dome)(ht:‖w-TΨ‖*h^2≤g)(pv:‖TΨ.1-JΦ.1‖≤α0)(pt:‖TΨ.2-JΦ.2‖≤β') : ‖w.1-JΦ.1‖ *h^2≤ g+α0*h^2 ∧ ‖w.2-JΦ.2‖ *h^2≤ g+β'*h^2:=by
 let x:= (w-TΨ); have hs:0≤h^2:=sq_nonneg _; constructor
 · rw [show w.1-JΦ.1=w.1-TΨ.1+(TΨ.1-JΦ.1) from by abel]; apply le_trans (mul_le_mul_of_nonneg_right (norm_add_le ..) hs); rw [add_mul]; exact add_le_add ((mul_le_mul_of_nonneg_right (show ‖w.1-TΨ.1‖ ≤ ‖x‖ from le_max_left ‖x.1‖ ‖x.2‖) hs).trans ht) (mul_le_mul_of_nonneg_right pv hs)
 rw [show w.2-JΦ.2=w.2-TΨ.2+(TΨ.2-JΦ.2) from by abel]; apply le_trans (mul_le_mul_of_nonneg_right (norm_add_le ..) hs); rw [add_mul]; exact add_le_add ((mul_le_mul_of_nonneg_right (show ‖w.2-TΨ.2‖≤ ‖x‖ from le_max_right ‖x.1‖ ‖x.2‖) hs).trans ht) (mul_le_mul_of_nonneg_right pt hs)
end YM.CF.Neon
