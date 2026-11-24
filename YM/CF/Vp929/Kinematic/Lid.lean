import YM.CF.Vp929.Stage.Treaty
import YM.CF.Pso.Eris
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt

variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "y"=> Scales.y SU.group R.L x
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
/-- A preintegration group family held at this hat. Doesn't yet need the quantitative strip/grant hypotheses. -/
structure Lid (o:Pitching w D x)(p p':BudgetPoint)(t:ℝ) : Prop where
 night : 0 < Scales.y SU.group R.L x
 zoom : WideFire L q D.pilot R K 5 (6+2) 105 x
 start : 0≤ t
 crew : ∀ β∈ Year R x, (fends p p' o β D.pilot) ∧ ∀ F:Corr (Scree.mid n B), Location.gross p' D t F→Nonempty (base (q:=q) (J:=J) (w:=w) p' β F)
namespace Lid
variable (H: Lid o p p' f)
variable {F F': Corr (Scree.mid n B)}
lemma sunset {ff ag Cg x:ℝ}{o:Pitching w D x}{N0:ℕ} (g:o.Gains c p p' f ff ag Cg)(u:Provision (D:=D) c N0 x f ff ag Cg)(hs:0<Scales.y SU.group R.L x)(p0:0≤f): Lid o p p' f:= by
 refine ⟨hs,u.wide,p0,fun β h=>?_⟩; exact ⟨(g.full β h _ (Location.gross_zero _ _ f p0)).fire,fun F hp=>(g.full β h F hp).b⟩
include H
lemma living : y∈Year R x := by change y/2≤y ∧ y≤ 2*y; constructor<;> linarith [H.night]
lemma day: Year R x∈𝓝 y:= mem_of_superset (Ioo_mem_nhds (show y/2<y by linarith [H.night]) (show y<2*y by linarith [H.night])) Set.Ioo_subset_Icc_self
lemma pos (hb:β∈ Year R x): 0<β:= (half_pos H.night).trans_le hb.1
lemma fend (hb:β∈ Year R x)(a:Dilation): fends p p' o β ((P').zoom a):= (H.crew β hb).1.zoom V a H.zoom
abbrev choice (hb:β∈ Year R x) (hF:Location.gross p' D f F) : Bs β F:= Classical.choice ((H.crew β hb).2 F hF)
abbrev still : Bs y 0:= H.choice H.living (Location.gross_zero _ _ _ H.start)
local notation "τ"=> radiusB x
variable (Mk: Monk SU.group (w.step V))(A₀:Ids (Scree.mid m B))(T₁:Ids (Scree.mid n B))
local notation "Rc" v:max=> poleY Mk v (Scales.y SU.group R.L x)
local notation "Δ" => (o.muster.post+90)*radiusB x
omit H
abbrev groupTide (X:Pilot)(hv:fends p p' o β X)(Lx:base (w:=w) (V:=V) (J:=J) (q:=q) p' β F) : Eire.Dress w.G S' d z' (20*τ) (Rc β) (Ys β F) Δ (vast (k:=D.Z.N1*τ) A') := GroupD (H:=Up β) (Rc β) A₀ T₁ (H₁:=Xs β) Lx hv o.bags o.vista
abbrev Quori (X:Pilot)(hv:fends p p' o β X)(Lx:base (w:=w) (V:=V) (J:=J) (q:=q) p' β F) (A:Stores (w.step V)): Rill.Arch w.G d:= ArchL Lx hv.head.scaleP (Up β) (Cay.rough (Eire.trot S' (Rc β) A) 0) A₀ T₁
include H
variable {X X':Pilot}
lemma arch_eq (hp0:β∈Year R x)(pB:β'∈Year R x)(hv:fends p p' o β X)(hv':fends p p' o β' X')(Lx: Bs β F)(Lx':Bs β' F') : ArchL Lx hv.head.scaleP (Up β) (Rc β) A₀ T₁= ArchL Lx' hv'.head.scaleP (Up β') (Rc β') A₀ T₁:= by
 let f(V₁:Pane η):= (YF w.G w.coarse w.fine q J.d (hv.head.scaleP ▸ Mk.park) (Mk.V,A₀) (V₁,T₁), w.fine (V₁,T₁)); exact Subtype.ext (congrArg f ((spirit_X o.muster Mk H.night (H.pos hp0)).2.trans (spirit_X o.muster Mk H.night (H.pos pB)).2.symm))
lemma qori (hp0:β∈Year R x)(pB:β'∈Year R x)(hv:fends p p' o β X)(hv':fends p p' o β' X')(Lx: Bs β F)(Lx':Bs β' F') (Aq:Stores (w.step V)):
   Quori Mk A₀ T₁ X hv Lx Aq= Quori Mk A₀ T₁ X' hv' Lx' Aq ∧ (groupTide Mk A₀ T₁ X hv Lx).blocks Aq=(groupTide Mk A₀ T₁ X' hv' Lx').blocks Aq:=by
 let M₁:= Eire.trot S' Mk Aq; have he(u:ℝ): poleY (Cay.rough M₁ 0) u y=Cay.rough M₁ 0:=by unfold poleY Cay.rough; simp
 have h:=arch_eq H (Cay.rough M₁ 0) A₀ T₁ hp0 pB hv hv' Lx Lx'; rw [he,he] at h; exact ⟨h,arch_eq H M₁ A₀ T₁ hp0 pB hv hv' Lx Lx'⟩
abbrev eye (hF:Location.gross p' D f F):= groupTide Mk A₀ T₁ D.pilot (H.crew y H.living).1 (H.choice H.living hF)
local notation "Δ₀"=> (D.pilot.hat R x)
local notation "χ"=> (shotM o.muster.vita)
lemma shot_p (hb:β∈ Year R x)(X:Pilot)(hv: fends p p' o β X): 0 < χ (X.hat R x) β := mul_pos (spare_pos _ ((hv.pal.lamp).symm ▸ hv.fare) (H.pos hb)) (point_p (mul_pos X.high (Scales.pos ..)))
end Lid
end Pitching
end YM.CF.Py.Rate
