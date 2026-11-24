import YM.CF.Stake.Loom
import YM.CF.Vp929.Grant.Wide
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Stake
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
open Tye Lich
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y β:ℝ}(p:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
variable {X: Interest (mid N B)}{Y:Interest (mid P B)}{U: Grasp V.U B d}{W:GivenX V U}
variable (M: Sheep V U W G Y X k n A)
local notation "sN"=>mid N B
local notation "θo"=> Hest.Budget R.L R.odd_side Y.P.den X.P.den G Y.M K.j
local notation "Δ"=> shipA G U Y.M Y.P.den Y.I X.I
local notation "TΦ"=> (Thera.yet_one)

open Corne

lemma Pilot.hat_zoom(F:Pilot)(R:Patch)(a:Dilation)(x:ℝ) : (F.zoom a).hat R x ≤ F.hat R x:=
 mul_le_mul_of_nonneg_right (mul_le_of_le_one_left F.high.le a.property.2) (Scales.pos ..).le
lemma Fend.zoom {X Y}{q:Chi}{H:Muster G S x d T}{U:Grasp V.U B d}{W:GivenX V U}{A:ℝ}
    {M:Sheep V U W G X Y k n A}{F:Pilot}{Z:Pluck R}{γ α:ℝ}{i j r:ℕ}{p p'} (v : Fend V H M Z F q p p' γ α j i r) (a:Dilation)(he: WideFire L q F R K i k j x) : Fend V H M Z (F.zoom a) q p p' γ α j i r:= by
  obtain ⟨u,q,r₁,r₂,r₃,r₄,_,h,v,t,m,n,q',s,p⟩:=v
  obtain ⟨a₁,a₂,a₃,a₄,a₅,y,H,f⟩:=v
  refine ⟨?_,?_,r₁,r₂,r₃,r₄,he.fire a,h,⟨a₁,a₂,a₃,a₄,a₅,y,H,fun M p=>?_⟩,t,m,n,q',s,p⟩
  · cases u; constructor <;> assumption
  · cases q; constructor <;> assumption
  specialize f M p; cases f; constructor <;> assumption
lemma pondsVolume {s pK:ℝ} (V:Grace K R L)(F:Pilot)(j l k:ℕ)(p:0<s)(hp:0<pK):∀ᶠ x:ℝ in atTop,∀ a:Dilation, PondP V (F.zoom a) x s pK j l k:=by
 filter_upwards [Atala.threshold R k l (s/2) (pK/2) F.bump F.large (half_pos p) (half_pos hp) F.fare F.high, Atala.threshold R k l s pK F.bump F.large p hp F.fare F.high] with x hx h a d B N P U W G A m r S T H₀ H₁ M Z q α γ L v Q p l'
 let Y:=v.head; let e:= v.pal; obtain ⟨g,k,t,z,w,T1,tickT⟩:= v.fireK.lope.heat _ v.money; have ht:40<(Domain N B).val:=by have ht:=v.fireK.blade; have hx:100*(1+radiusB x)≤(Domain N B).val:=Y.cert.size; omega
 rw [e.page,e.ward,e.guard]; constructor <;> exact (by first| exact hx _ T Q Y.cert.got (Eq.symm l' ▸ Subset.refl _) ht L.beta v.money (p.trans <| F.hat_zoom R a x) (F.skin R x) q (tickT S T Y.cert Q (Y.sized Q.park) l'|>.1)| exact h _ T Q Y.cert.got (Eq.symm l' ▸ Subset.refl _) ht L.beta v.money (p.trans <| F.hat_zoom R a x) _ q (tickT S T Y.cert Q (Y.sized Q.park) l'|>.1))
end YM.CF.Stake
