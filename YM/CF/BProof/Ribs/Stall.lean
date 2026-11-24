import YM.CF.BProof.Ribs.Oxide
import YM.CF.Pso.Steps
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
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
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
open Cascade
open Fief
variable {X: Interest (mid N B)}{Y:Interest (mid P B)}{U: Grasp V.U B d}{W:GivenX V U}
variable (M: Sheep V U W G Y X k n A)
open Corne
variable {ρ α γ:ℝ}{F:Pilot}{Z:Pluck R}{P₁ P₂:BudgetPoint}
open Girt Eire
variable{H₀: GramM (mid P B)}{H₁:GramM (mid N B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)}{pK L':ℝ}{q q':Chi}{H:Muster G S x d T}
open YM.CF.Floral
open scoped YM.CF.Mew
variable {D:Set ℂ}(Xo Yo:D→ RegBudget (mid P B))(Zo:D→ForceBudget (mid P B))(Jk:D→ℂ)
local notation "P0" i:max=> color_b H₀ β (Xo i) (Yo i) (Zo i) (Jk i)
variable (oP:∀ i y,SubHol D fun z=> Xo z i y)(vP:∀ i y,SubHol D fun z=> Yo z i y)(cP:∀ i y,SubHol D fun z=> Zo z i y)
variable (Mk:Monk SU.group S)(A₀:Ids (mid N B))(T₁: Ids (mid P B)) {r₁:ℕ}
variable (M':Sheep V U W G H₀.J H₁.J (k+2) n A) (Lx:∀ v:D,Girt.BaseL U G (color_b H₀ β (Xo v) (Yo v) (Zo v) (Jk v)) G₀ G₁ q' pK)
variable(Y_:∀ (_:D),Fend V H M' Z F q H₀.p H₁.p γ α j l r₁)(U_:∀ X:Support (Domain P B), Lend P B d X)(w':Hive.Vista U H₀.J.M H₀.J.P U_ (k+2) M'.q ((Fintype.card Play:ℝ)*L') M'.lot M'.tone)
local notation "G'" i:max=> GroupD Mk A₀ T₁ (H₁:=H₁) (Lx i) (Y_ i) U_ w'
include V H
lemma same_brew (i z:D)(t0:Troupe S r₁ (Words S)) : (G' i).brew t0 = (G' z).brew t0:=by rfl
lemma same_song (i z:D)(t0:Troupe S r₁ (Words S)) : (G' i).songP t0 = (G' z).songP t0:=by rfl
lemma same_heat (i z:D)(t0:Troupe S r₁ (Words S))(C:Ride S) : (G' i).heatT t0 C= (G' z).heatT t0 C:=by rfl
include Y_ U_ w' Lx oP vP cP
open Stilo
lemma still_z (u:D)(t0:Troupe S r₁ (Words S))(C:Ride S): SubHol D fun i=> (G' i).blazon x H.post t0 C:=by
 let A(i:D):=(G' i).bodyL x H.post t0; have hv:SubHol D A:= by
    unfold A Dress.bodyL Eire.lure; apply Floral.SubHol.prod; intro i j
    exact olive_Ω Xo Yo Zo Jk oP vP cP (Eire.trot S Mk (penn S t0)) T₁ (q:=H.trot) (d:=H.room) (k:=H.post) _ -- order
 let Γ:= cluster (BranchX S (vast (k:=Z.N1*radiusB x) H) ((H.post+90)*radiusB x)) t0; let Fm(i:D):= (G' i).stageT x H.post t0
 let Pk(C:Ride S):= (G' u).heatT t0 C; let Z1:=(G' u).songP t0; let B0:=(G' u).brew t0
 have hT(i:D): (G' i).songP t0= Z1:=same_song V Xo Yo Zo Jk Mk A₀ T₁ M' Lx Y_ U_ w' i u t0 -- order check
 have hp(i:D)(C): (G' i).heatT t0 C=Pk C:= same_heat V Xo Yo Zo Jk Mk A₀ T₁ M' Lx Y_ U_ w' i u t0 C
 have hτ(i:D): (G' i).brew t0=B0:= same_brew V Xo Yo Zo Jk Mk A₀ T₁ M' Lx Y_ U_ w' i u t0
 have hg(C: Ride S):SubHol D fun z=> Scion.tempo (Fm z) C:=by
    by_cases p:Γ ≤ C; swap
    · unfold Scion.tempo; simp_rw [show ¬Scion.cluster (BranchX S (vast (k:=Z.N1*radiusB x) H) (((H).post+90)*radiusB x)) t0 ≤ C from p, if_false]; exact SubHol.constant _ -- shadow `if_false`
    let L:=(issue (Pk C)).flip Z1; have he(z): Scion.tempo (Fm z) C=L (A z).val* B0.val:=by
       unfold Scion.tempo; rw [if_pos p]; change issue ((G' z).heatT t0 C) _ ((G' z).songP t0) * ((G' z).brew t0).val= _; rw [hp,hT,hτ]; rfl
    simp_rw [he]; exact ((hv.linear eat_c).linear L).mul (SubHol.constant _)
 have hk:SubHol D (fun z=> Scion.vigor (Fm z) C):=by
    apply subhol_dough; simp_rw [vig_all]; let T:=SubHol.pi (F:=fun z C=>tempo (Fm z) C) hg; exact (T.linear solve_c).linear (LinearMap.proj C)
 by_cases p: capG S (flags (temp x) Mk.V) (chillB Mk) H₀.p.threshold t0 C
 · have he(i:D): (G' i).blazon x H.post t0 C= Scion.vigor (Fm i) C:= if_pos (show capG S (flags (temp x) Mk.V) (chillB Mk) (P0 i).p.threshold t0 C from p); rw [funext he]; exact hk
 have he(i:D): (G' i).blazon x H.post t0 C=0:= if_neg (show ¬capG S (flags (temp x) Mk.V) (chillB Mk) (P0 i).p.threshold t0 C from p); rw [funext he]; exact SubHol.constant _
end YM.CF.Oise
