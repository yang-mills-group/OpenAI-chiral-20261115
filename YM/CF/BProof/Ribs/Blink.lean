import YM.CF.BProof.Ribs.Ripe
import YM.CF.Feu.Bird
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
open Feu Jade Plume Stilo
variable {r₁:ℕ}(M':Sheep V U W G H₀.J H₁.J (k+2) n A) (Xc:BaseL U G H₀ G₀ G₁ q' pK) (u:Fend V H M' Z F q H₀.p H₁.p γ α j l r₁) (U_:∀ X:Support (Domain P B), Lend P B d X)(w':Hive.Vista U H₀.J.M H₀.J.P U_ (k+2) M'.q ((Fintype.card Play:ℝ)*L') M'.lot M'.tone)
local notation "Υ" => Jade.loam V F Z (X:=H₁) (Y:=H₀) M' U_ w' u Xc
variable (T0:H₀.F=0)(T1:H₀.slip=0)
include Xc u U_ w' T0 T1
lemma no_brew (Mk:Monk SU.group S)(A₀:Ids (mid N B))(T₁:Ids (mid P B))(i:Roc (mid P B))(C:Ride S):(GroupD Mk A₀ T₁ (H₁:=H₁) Xc u U_ w').blazon x H.post (subtK S i) C=0:=by
 let Ω:=GroupD Mk A₀ T₁ (H₁:=H₁) Xc u U_ w'; let j:=subtK (r:=r₁) S i; let M:=Ω.stageT x H.post j
 have hf:M.voice=0:=by
    suffices Ω.bodyL x H.post j=0 from congrArg Subtype.val this
    unfold Dress.bodyL Eire.lure j; rw [Feu.husk_p,prod_singleton]; change sheer S x _ _ _ _ _ _ _= _; unfold sheer; simp [T0,T1]
 have hg: Scion.vig M=0:=funext fun v=> Subtype.ext (show Scion.tempo M v=0 from (by unfold Scion.tempo; split; rw [hf,map_zero,LinearMap.zero_apply,zero_mul]; rfl))
 change Ω.blazon x H.post j C=_; unfold Dress.blazon; split; swap; · rfl
 change (reconL.symm (vig M)) C=0; rw [hg,map_zero]; rfl
lemma veil_wane (O:Roc (mid P B))(C:Ride S){G:Scree.Copy (mid N B)}(Fh:LullT V F Z (X:=H₁) (Y:=H₀) M' U_ w' u Xc (subtK S O) C G):G=0:=by
 let j:=subtK (r:=r₁) S O; funext v; by_cases p:Rue.Gates (Rue.litres H₁.p.threshold (bay C) (cook S j.toLeft).flags) (bay C) v.1
 · obtain ⟨i,h,g⟩:=p; let x':Orbit (mid N B):=(i,v.2); have he(u':Plume.Cord S): Υ j C x' u'=0:= no_brew V M' Xc _ U_ w' T0 T1 _ _ _ O C; change G v=0; rw [Fh.levy v x' g (fun _ _=>rfl),←Fh.visor x' h]; change (∫ i,Υ j C x' i ∂ Plume.plummy S (F.hat R x))=0; simp_rw [he]; rw [integral_zero]
 exact Fh.wherep _ p
end YM.CF.Oise
