import GaugeFieldConstruction.Herd

-- Third purchase. Does NOT change the Muster constants. Refine plan_B
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
variable {W:GivenX V U}{M:Sheep V U W G Y.J X.J k n A}{H:Muster G S x d T}{q:Chi}{F:Pilot}{Z:Pluck R}
abbrev KeyUp (p:BudgetPoint): BudgetPoint :={p with power:=3,power_ge:=by omega}
abbrev Gram3 {N:Side}(Y:GramM N):GramM N:={Y with p:=KeyUp Y.p}
abbrev Muster3(H:Muster G S x d T):Muster G S x d T:={H with phaseUp:=KeyUp H.phaseUp, phaseLow:=KeyUp H.phaseLow}
abbrev Sheep3(M:Sheep V U W G Y.J X.J k n A)(t:SharpHerd M 3):= powerHerd V U W M 3 t
lemma census_3 (t:Census H k r p) : Census (Muster3 H) k r p:=by cases t; constructor <;> assumption
lemma mat_3 (u:MatP V H M F Z)(t:SharpHerd M 3) : MatP V (Muster3 H) (Sheep3 V (X:=X) (Y:=Y) M t) F Z:=by
 obtain ⟨A,hA⟩:=u.mint; exact ⟨u.scene,u.urge,u.lore,⟨A,census_3 hA⟩,u.pace⟩
lemma stat_3 (t:StatV V G T U W X Y a γ w x n k) : StatV V G T U W (Gram3 X) (Gram3 Y) a γ w x 3 k:=by have z:=t.down; exact ⟨t.hunt,⟨z.large,z.low,rfl,rfl,z.hU,z.order,z.holds⟩,t.dose,t.sound,t.foot,t.bill,t.cult,t.care,t.move,t.coinX,t.coinY,t.coat,t.rest,t.fee,t.fee',t.year⟩
lemma stage_3(t: StageP V H Y X U) : StageP V (Muster3 H) (Gram3 Y) (Gram3 X) U:=⟨t.fi,t.foil,t.iPath,t.oPath,t.wC,congrArg KeyUp t.fC,t.wc,congrArg KeyUp t.heat⟩
lemma fend_e(k l j:ℕ)(q:Chi)(p:2 ≤ k)(h:l≤18) : ∀ᶠ x:ℝ in atTop,∀ {N B P:Side}{G:Ratio (mid N B) (mid P B)}{Y: GramM (mid P B)}{Xs: GramM (mid N B)}{d A:ℝ} (U: Grasp V.U B d)(W:GivenX V U) {n:ℕ}{M:Sheep V U W G Y.J Xs.J k n A}{S:StepData (Domain N B) (Domain P B)}{T:Tube SU.group S}{H:Muster G S x d T} {γ α:ℝ}{Z:Pluck R}{r:ℕ}{F:Pilot}, Fend V H M Z F q Y.p Xs.p γ α j l r → ∀ t:SharpHerd M 3,Fend V (Muster3 H) (Sheep3 V (X:=Xs) (Y:=Y) M t) Z F q (KeyUp Y.p) (KeyUp Xs.p) γ α j l r := by
 filter_upwards [booth_k V j k l p h q] with x hx N B P G Y X d A U W n M S T H γ α Z r F p h
 have g:=p.pal; have hg:GiftP V (Muster3 H) (Sheep3 V (X:=X) (Y:=Y) M h) (KeyUp Y.p) (KeyUp X.p) F q α γ H.beta l j:=⟨g.iH,g.iC,g.belt,congrArg KeyUp g.tent,congrArg KeyUp g.fora,g.town,g.page,g.lamp,g.small,g.guard,g.ward,g.paid,g.fair,g.p0⟩
 have hm:=mat_3 (X:=X) (Y:=Y) V p.ram h
 exact ⟨hg,hm,p.room,p.hip,p.nil,p.line,p.fireK,p.head,hx F p.fireK α p.head U (Sheep3 V (X:=X) (Y:=Y) M h) (Muster3 H) hg hm p.money,p.money,p.height,p.fee,p.fare,p.vote,p.hope⟩
end YM.CF.Py
end
