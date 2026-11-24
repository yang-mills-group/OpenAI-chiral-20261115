import YM.CF.Neon.Plast
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
variable {u_O Hh pKe qK a γ vS dS kL w:ℝ}{r p_aux i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
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
local notation "ω"=> Aura Θ
variable (F:Mew.Key I→ Pax (mid N B))(F':I→ RegBudget (mid N B))(Z Φ:I→ℝ)(E:I→ArcΦ)(Ux:∀ i,Ice L0 (σ i) p0 h (Z i) (W i) (Φ i) (coldE p0 (τι F [i])) (F' i) (Q' i) (Kχ i) (E i))
local notation "Dμ"=> Φstack Q'
abbrev EraT (Vh:I→RegBudget (mid N B))(Y':Key I): RegBudget (mid N B):= ∑ i:I,(Y' i) • Vh i
abbrev Aura_T (F: Mew.Key I→ Pax (mid N B))(Y':Key I):Pax (mid N B):=F Y'-∑ i:I,(Y' i) • (τι F [i])
local notation "Φt" z:max=> Aura_T F z
abbrev α_ξ (z:Key I):=∑ i:I,z i*Kχ i
variable (Tp:Ids (mid N B))
local notation "Φr" z:max=> Ione.cast_E (Aura_T F z) Tp
def FacetE (z:Key I): RegBudget Θ:= EraT F' z + Ione.cast_E (Aura_T F z) Tp
local notation "IZ"=> FacetE F F' Tp
local notation "Tσ"=> α_ξ Kχ
open Rive
variable (w0:∀ z∈hill I,Turf (F z))(uF:∀ i x,River fun z=> F z i x) (p:∀ i:Aura (mid N B),Hush (Cube.node ∘ σ) i.val fun z=> F z i)
include w0
lemma turp_X(z:Key I)(hz:z∈hill I): Turf (Aura_T F z):=by
 intro i u t; unfold Aura_T; simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,w0 z hz _ _ t]
 congr 1; apply sum_congr rfl; intro i' _; exact congrArg (z i' • ·) (lace_C [i'] (show Set.EqOn (fun z=> F z i u) (fun z=> F z i (u.1,t)) (hill I) from fun z p=>w0 z p i u t) roots) -- defeq
omit w0
lemma voc_E (z:ℂ)(F:RegBudget (mid N B))(x: Orbit Θ): exponentL p0 (z • F) x.1= z • exponentL p0 F x.1:=by unfold exponentL; rw [Finset.smul_sum]; simp_rw [numb_b p0 _ _ x]; apply sum_congr rfl; intro i _; unfold Vow.march; split; rfl; rw [smul_zero]
lemma e_s_K {ι:Type*}[DecidableEq ι](I:Finset ι)(F:ι→ RegBudget (mid N B))(x: Orbit Θ) : exponentL p0 (∑ i∈I,F i) x.1=∑ i∈I,exponentL p0 (F i) x.1:=by induction I using Finset.induction with|empty=> rw [sum_empty,sum_empty]; apply Ione.zero_r|insert a I z u=> rw [sum_insert z,sum_insert z,ripe_H, u]
open Ione
lemma con_z (z:ℂ)(U:Pax Θ)(x:Orbit Θ): coldE p0 (z • U) x= z • coldE p0 U x:=by unfold coldE; rw [Finset.smul_sum]; rfl
lemma cul_z (z:ℂ)(U:Cusp Θ)(x:Orbit Θ): fuelV p0 (z • U) x=z • fuelV p0 U x:=by unfold fuelV; simp_rw [Finset.smul_sum]; rfl
lemma τsum {ι:Type*}[DecidableEq ι](I:Finset ι)(F:ι→ Pax (mid N B))(x:Orbit Θ): coldE p0 (∑ i∈I,F i) x=∑ i∈I,coldE p0 (F i) x:=by
 induction I using Finset.induction_on with| empty=> rw [sum_empty,sum_empty]; unfold coldE; simp| insert j i t u=> rw [sum_insert t,sum_insert t,crep,u]
lemma τlump {ι:Type*}[DecidableEq ι](I:Finset ι)(F:ι→ Cusp (mid N B))(x:Orbit Θ): fuelV p0 (∑ i∈I,F i) x=∑ i∈I,fuelV p0 (F i) x:=by induction I using Finset.induction_on with|empty=> rw [sum_empty,sum_empty]; unfold fuelV; simp|insert j i t u=>rw [sum_insert t,sum_insert t,Vow.toast,u]
include w0 Ux
-- assemble LHS Wox. Apert equality Kχ offset.L prove. future M shape. 
lemma hepa_F (z:Key I)(u:z∈hill I)(U:Orbit Θ)(hz:FleetS p0.threshold U.1): coldE p0 (F z) U= α_ξ Kχ z • (1:Cipher Θ) + exponentL p0 (FacetE F F' Tp z) U.1+fuelV p0 (Φstack Q' z) U:=by
 let s:Pax Θ:=∑ i:I,(z i) • (τι F [i]); let K:= Aura_T F z; let Y':= exponentL p0 (Ione.cast_E K Tp) U.1; let V':=α_ξ Kχ z
 rw [FacetE, ripe_H, ocean p0 K Tp (turp_X F w0 z u)]; nth_rw 1 [show F z=s+K from (by unfold K Aura_T s; abel)]
 have hS(k):coldE p0 (τι F [k]) U = _:= (Ux k).wear _ hz
 unfold s; simp_rw [crep, τsum p0, con_z p0,hS, smul_add, sum_add_distrib]; unfold EraT α_ξ Φstack; simp_rw [Finset.sum_smul,e_s_K p0,voc_E p0,τlump p0,cul_z p0, smul_smul]; abel -- expensive
omit w0
local notation "Sχ"=> (σ)
include p uF
lemma HushT (X:Scree.Hub Θ):Hush (Cube.node ∘ σ) X.val.2 (fun z=>FacetE F F' Tp z X):=by
 let K0:= X.val.2; intro v hv x hx px; unfold FacetE EraT; let t(i):=(Ux i).axle; simp_rw [Pi.add_apply,Finset.sum_apply]; apply congrArg₂ _
 · apply sum_congr rfl; intro i _; rw [Pi.smul_apply,Pi.smul_apply]; by_cases w: node (σ i)∈K0; rw [px _ w]; rw [(t i).site X (fun h=>w (h ▸ X.property)),smul_zero,smul_zero]
 unfold Ione.cast_E; congr! 1 -- tune columns
 funext y; let T:= Tp; unfold Aura_T; simp_rw [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply, show F v (lagE X)= F x (lagE X) from p _ _ hv _ hx px]; apply congrArg; apply sum_congr rfl; intro i _; by_cases w: node (σ i)∈K0; rw [px _ w]; rw [show τι F _ (lagE X) (y,Tp)=0 from husht_B (Cube.node∘σ) (lagE X).val _ (fun z v u y q=>congrFun (p _ _ v _ y q) _) (uF _ _) [i] i w (by simp),smul_zero,smul_zero]
end YM.CF.Neon
