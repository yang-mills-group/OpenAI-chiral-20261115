import YM.CF.Plume.Lark

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
variable{S}
open scoped Classical ENNReal NNReal
open Girt Next.Fluctuations.Sector Dial
open Lich
-- active Modes: for Shape Y plan agreement full on X.
variable{k b l k1 k' o₁ o₂ r r' j:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]
local notation "bay"=> Stilo.bay
variable {X: Support (Domain N B)}{H H':Ride S}
variable{G:Ratio (mid N B) (mid P B)}{e:ℝ}{Q:GramM (mid P B)}
set_option pp.universes false
variable {V V':Orbit (mid N B)}{y y':Cord S}{K K':Ids (mid P B)}
variable {X0:ι→Palot.leaf (Site (Domain N B))}{i:Troupe S r ι}{t:ℝ}
local notation "U₀"=> cort V.1 y
local notation "U'"=> cort V'.1 y'
local notation "AX"=> BranchX S X0 k
local notation "ScopeF"=> Passage S
variable (h:Spark (Stilo.bay H) y y')(p:Palot.fits (BranchX S X0 k) i H)
variable {A₀:Side}{e:ℝ}{j κ n μ:ℕ}{ho:Odd A₀.val}{Y:Pricing j A₀ ho (Thread j)}{P':Grasp Y B e}{M:Male}{I:Aim (mid P B)}{I':Pec.Pride (mid P B)}{v v' g g' t t' w Z α ι₀:ℝ}
variable (A: Dress G S e r k' (cort V.1 y) Q k X0)(B':Dress G S e r k' (cort V'.1 y') Q k X0)
local notation "µ"=>A.wage
local notation "t₀"=>A.coats i
local notation "t₁"=>B'.coats i
variable {q:Chi}{T:Tube SU.group S}
variable {F:Scree.Loom (mid N B)}{W:Scree.Loom (mid P B)}{x w' o u cψ h₀ K₂:ℝ}{l0:ℕ}
structure Belf (s t w o t' a b α x g:ℝ)(l k1 k2:ℕ)(q:Chi)(F:Scree.Loom (mid N B))(W:Scree.Loom (mid P B))(T: Tube SU.group S)(K:Stores S→ Rill.Arch G e):Prop where
 cloth:A.cloth=y.2.2
 peg : A.pipe=T
 wage : A.wager= Plume.walksK A.cloth
 warm : A.Visit V.2 F W s t w o t' a b x g l k1 k2 q
 turn : ∀ i:Stores S,Eire.Clan G S (T:=A.pipe) A.axes V.2 A.cloth (Eire.trot S (rough (cort V.1 y) 0) i) F W A.chi q l x A.wage g Q.beta (K i)
 price : ∀ P:Stores S,P.flags=flags (temp x) V.1→ Bell S (Eire.trot S (rough (cort V.1 y) 0) P) x A.pipe A.chi A.wage l Q.beta t o
variable {K K': Stores S → Rill.Arch G e}{t₀_ b' b'' vη v_ :ℝ}
variable (c:Belf A u t₀_ w o w' v v' α x vη l k1 o₁ q F W T K)(d:Belf B' u t₀_ w o w' v v' α x vη l k1 o₁ q F W T K') -- nonsense pipe use
variable (hh:A.wage=B'.wage)(hq:A.chi=B'.chi)
variable (f : Agrees (Stilo.bay H) V.1 V'.1) (s : Set.EqOn V.2 V'.2 (Stilo.bay H))
local notation "CH0"=> Eire.capG S (flags (temp x) V.1) (chillB U₀) Q.p.threshold i H
local notation "CH"=> Eire.capG S (flags (temp x) V'.1) (chillB U') Q.p.threshold i H
include c d hh hq f s h p
lemma shape_g (u':CH0) : CrownB G S e (t₀) (t₁) k H∧ CrownB G S e (K (penn S i)) (K' (penn S i)) k H:=by
 have hv:= (c.warm.wear); have hr:= (c.warm.years); obtain ⟨t,p',v⟩:= Dress.Ion A x l c.warm i p u'
 let B₀:= penn S i; let Q':= erosion ((l+70)*radiusB x) (bay H)
 have he: Set.EqOn y.2.2 y'.2.2 (Passage S Q'):=by
    intro j l'; apply h.sharesL; change S.ratio.parent j∈ bay H; let L:=(l+70)*radiusB x; exact erosion_c _ _ (halo_subset L _ (mem_filter.mp l').2)
 have hK: Set.EqOn V.2 V'.2 Q':= fun j v' => s (erosion_c _ _ (halo_subset _ _ (show j∈ Q' from v')))
 have hT:= sail h f B₀ -- x not needed.
 have hk:Set.EqOn A.cloth B'.cloth (Passage S Q'):=by rw [c.cloth,d.cloth]; exact he
 let H''(u v):=CrownB G S e u v k H; have hu':B'.pipe=A.pipe:= d.peg.trans c.peg.symm
 constructor
 · let L:= t₀; let L':=t₁; have hz:=d.warm.haul B₀; rw [hu',←hh,←hq] at hz
   exact (congrArg (fun k=>CrownB G S e L L' k H) hv).mpr (frosty G S A.axes H V.2 V'.2 A.cloth B'.cloth (A.coats i) (B'.coats i) p' (skyC S H) i.toLeft t rfl hr c.warm.ceil (c.warm.haul B₀) hz hT.toBeat c.warm.pole c.warm.heel c.warm.toes c.warm.horn hK hk (fun a z=>h.sharesB.up _ (erosion_c _ _ (halo_subset _ _ z))))
 have hz:=d.turn B₀; rw [hu',←hh,←hq] at hz; let P:=peal S (rough U₀ 0) i.toLeft H u'.1 u'.2.2 hr t c.warm.legP c.warm.mint c.warm.tone c.warm.pole c.price; let g':=K B₀; let D':=K' B₀
 have hf:Beat (Eire.trot S (rough U₀ 0) B₀) (Eire.trot S (rough U' 0) B₀) (bay H):= ⟨hT.road,hT.fr,hT.fe,hT.trunks,hT.view,hT.data,fun _ _=>rfl⟩
 exact (congrArg (fun k=>CrownB G S e g' D' k H) hv).mpr (frosty G S A.axes H V.2 V'.2 A.cloth B'.cloth g' D' P (skyC S H) i.toLeft t rfl hr c.warm.ceil (c.turn B₀) hz hf c.warm.pole c.warm.heel c.warm.toes c.warm.horn hK hk (fun a z=>h.sharesB.up _ (erosion_c _ _ (halo_subset _ _ z))))
end YM.CF.Plume
