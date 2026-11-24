import YM.CF.BProof.Hill.Registry
import YM.CF.BProof.Forge.Dome
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Cupboard
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{N B:Side}{d x:ℝ}{U:Grasp V.U B d}{W:GivenX V U}{q:Chi}{e a h γ w:ℝ}{order power:ℕ}
-- Bough spine geometry keeps Hue, lifts genuine fields. h rt fixed at hq; no size when comparing l0 theta step. Spans Estimate. Need access S.ρ uniforms.
open Bake PushA Episode Salt
variable {m:Side}{hx N0 n:ℕ}{T': Month x a order power N0 V W}
-- Full auxiliary family before x. Use eventually nonnegative profiles also in table; no division.Price.Space.
variable (b p i:ℕ) (J:Robes N V W) {Fp:ℝ→ℝ}
structure TablesB (V:Grace K R L){U:Grasp V.U B d}{W:GivenX V U}(q:Chi)(h a:ℝ)(J:Robes N V W) (power order N0 b:ℕ)(Fp:ℝ→ℝ)(F:RankX→ℝ→ℝ) (R0:ℝ→ℝ)(x:ℝ):Prop where
 cool:∀ t:RankX,sizeK R.L 2 (F t)
 top:Fp x ≤ F (some b) x
 large:0<R0 x
 warm(t:RankX): (∀ i,t=some i→i ≤ b)→ 0≤F t x ∧∀ y,x≤y→ F t y ≤ F t x
 move{N P:Side}(S:StepData (Domain N B) (Domain P B))(G: Ratio (mid N B) (mid P B))(i:ℕ): i<b→ Duty V a power order N0 J q h S G x 1 (grant_B R.L x) (F (some i) x) (F (some (i+1)) x) 0 (some i) (some (i+1))
 vault{N P:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B)): Duty V a power order N0 J q h S G x (R0 x) (grant_B R.L x) (F none x) (F (some 0) x) 0 none (some 0)
-- `deconstruct Chefs` only; ticket.Availability. calls explicit loops. aggregate w_A.Fit
lemma cost_ℝ (v:MoveX (k:=i) (p:=p) V U W q a J.d J.n hx J.k J.roomX h)(pLx:hx≤ N0)(g:VaultXU (p:=p) (k:=i) V U W q a J.d J.n e N0 J.k J.roomX h)(hf:sizeK R.L 2 Fp):∃ (F:RankX→ℝ→ℝ)(R0 θ:ℝ→ℝ), CoolX R.L θ∧ ∀ᶠ x in atTop, TablesB V q h a J p i N0 b Fp F R0 x∧ (dleaf R.L x+F none x)≤ θ x/4:=by
 obtain ⟨F0,u,hF⟩:= CoolX.roomZ R.L Fp hf
 obtain ⟨F,Vm⟩:=start_K V a p i N0 J q h v pLx F0 b u
 obtain ⟨E,R0,c,t⟩:= vault_U V a p i N0 J q h g _ (Vm.grow 0).small ((Vm.grow 0).costs.mono fun i p=>p.1)
 let Y:RankX→ℝ→ℝ:=fun r=> Option.rec E F r; let G':=fun x=>dleaf R.L x+E x; obtain ⟨θ,hC,p⟩:= CoolX.roomZ R.L (fun x=> 4*G' x) (((dev_R R).1.accrue c).scale _)
 refine ⟨Y,R0,θ,hC,?_⟩
 filter_upwards [hF,t,p,eventually_all.mpr (fun j:Fin b=>Vm.warp j j.isLt), eventually_all.mpr (fun j:Fin (b+1)=> (Vm.grow j).costs)] with x h t p W Fp -- Fp shadow function! fix.
 refine ⟨⟨fun t=>?_,?_,t.1,fun tY v=> ?_,fun S G i q=>?_,t.2.2.2⟩,?_⟩ -- ∀ implicit braces maybe
 · cases t; exact c; exact (Vm.grow _).small
 · change _≤ F b x; rw [Vm.atK]; exact h
 · cases tY with
   | none=> exact ⟨t.2.1,t.2.2.1⟩ -- shadow
   | some i=> exact Fp (⟨i,by have he:= v _ rfl; omega⟩:Fin (b+1))
 · -- need iκ
   exact W (⟨i,q⟩:Fin b) S G i
 change dleaf _ _+E x≤_; unfold G' at p; linarith
end Cupboard
end YM.CF.Py
