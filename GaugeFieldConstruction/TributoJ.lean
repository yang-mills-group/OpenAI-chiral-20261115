import GaugeFieldConstruction.SpursJ5
import GaugeFieldConstruction.Trimbo4
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Legends
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Swirls
import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Moll
import GaugeFieldConstruction.Panther
import GaugeFieldConstruction.Kenko
import GaugeFieldConstruction.HopeQ
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 70000
set_option maxRecDepth 4000
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
open Eire Girt
open VolumeRate
namespace Pitching
open Lich Iva
open Engine Engine.Basin Engine.Docket Dialect
open Vow Bake Salt Stax Sour Larch
namespace Focus
open Appel.Rate Stockpile
section
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt
open Next.Fluctuations.Sector
open Neon
open QuadClock Haro
open Mew Vow Rive Bake
open scoped YM.CF.Mew
open Riant
open YM.CF.Oath.BellPrice PinRack
open TableF TableF.Boom Lenten Layout Fren
open Mew Roots Roots.Connect Ing Ing.Iona CoeffArc Frugal
section
variable {m B:Side}{I J A C:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J]
variable [Fintype A][Fintype C][DecidableEq A][DecidableEq C]
namespace CoeffArc.Directory
-- induce from finite coordinate declarations. Naming scopes.Color generation.Needs $Full$ on all Principals of source. don't require image.F.P coherence if T0 differs.
variable (D:Directory I A)(H:Directory J C)(e:I↪J)(g:A↪C)(T:Sweep (mid m B))
variable (v:Embassy D H e g)(Θ:Finset I)
variable (s:A→Seat (mid m B))(t:C→Seat (mid m B))(F:D.TourF)(P:H.TourF)
variable (W:D.ToPC)(V:H.ToPC)(G:D.ToMG)(U:H.ToMG)(b:D.TourG)(d:H.TourG)(L:Side)
variable (X:GramM (mid m B))(M:I→Zone (mid m B))(N:J→ Zone (mid m B)) (α β γ q τ:ℝ)
local notation "ΦT"=> D.TransferX L s b G W
local notation "ΦF"=> H.TransferX L t d U V
local notation "Ω"=>Mantle e T
local notation "dA"=> D.depth∘ D.own
local notation "dP"=> H.depth∘ H.own
local notation "ΤF"=>D.F_v s
local notation "ΤG"=> H.F_v t
local notation "τν"=> (dA∘ ((↑) : Θ→I))
local notation "iM"=> (ΤF∘ ((↑) : Θ→I))
local notation "X0"=> (fun i:Θ=> Eye (I:=I) i.val)
local notation "Y0"=> (Ω ∘ X0)
local notation "XC"=> (ΦT∘ X0)
local notation "YC"=> (Ω∘ XC)
variable (hR:Rn D Θ)(hT:∀ a,t (g a)=sh T (s a))
include v hR hT
lemma paths_e : (∀ (u: Θ→ℝ), Sigt Θ (LegQ XC u) ∧ Ω (LegQ XC u)=LegQ YC u)∧ OnPlot τν ΤF iM dA XC ∧ OnPlot τν ΤG (sh T ∘ iM) dP YC:=by
 have op(i:Θ):D.Tribe (Eye i.val) (D.own i.val):=tribe_eye D _
 have ot(i:Θ): D.Tribe (XC i) (D.own i.val):= Tribe_c _ _ _ _ _ _ _ (op i)
 have ov(i:Θ):H.Tribe (YC i) (g (D.own i.val)) := Achamo _ _ _ _ T v (ot i)
 have ht(i:Θ): Sigt Θ (XC i):= PassU D s W b G L Θ (x:= Eye i.val) (fun j h=>Pi.single_eq_of_ne (show j≠i.val from fun e=>h (e ▸ i.property)) _) hR
 refine ⟨fun z=>⟨fun j k => ?_, Augurio ..⟩, fun i j h=> ot i j fun y=> h (mem_filter.mpr ⟨mem_univ _, Prod.ext (congrArg s y) (congrArg D.depth y) ⟩), fun i j h=> ov i j fun y=> h (mem_filter.mpr ⟨mem_univ _, Prod.ext ((congrArg t y).trans (hT _)) ((congrArg H.depth y).trans (v.dep _))⟩)⟩
 unfold LegQ SpotQ; rw [Finset.sum_apply]; refine sum_eq_zero fun i _=>?_; change Complex.ofReal (z i)*XC i j=_; rw [ht i j k,mul_zero] -- notation
variable (hA:D.Paid X M s F b G W L α β q)(hB:H.Paid X N t P d U V L α γ q)
variable (hx:Rib D H e g T v F P)(w:H.TourG)(pr:H.InShape P w τ)(p:300 < (mid m B).val) (a:0<α)(c:0≤q)
include hA hB hx pr p a c
omit hR
lemma reaches_e (i:Θ)(h:Zvia T (BandPlot M (XC i)) (BandPlot N (YC i))): ΦF (Y0 i)=YC i:=by
 symm; let n:=D.own i.val; have h0:=tribe_eye D i.val;
 exact Patent D L s M b F G W hA n c H (g n) N t d P U V hB T (Eye i.val) _ _ h0 (Achamo _ _ _ _ _ v (Tribe_c _ _ _ _ _ _ _ h0)) (Achamo _ _ _ _ _ v h0) (hT _) (v.dep _) w pr a p (fun f=> Katabasis D H e g T v s W b G L f _) (Toner D H e g T v _ _ _ _ hx) h
omit hT hA hB hx pr p a c
lemma mantle_p {z:Key I}(h:Sigt Θ z)(r:∀ i:Θ, ΦF (Y0 i)=YC i): Ω (ΦT z)=ΦF (Ω z):=by
 let Q: Key Θ:=fun i=> z i.val; let B:=SpotQ X0 Q; have hu: Ω z=SpotQ Y0 (Λpay T ∘ Q):=by rw [← show B=z from parade Θ h]; exact Arriba ..
 have hv:ΦT z=SpotQ XC Q:=by rw[← show B=z from parade Θ h]; exact by_column ΤF (D.Ctags G W L b) X0 XC (fun i=>rfl) _ -- tune order
 rw [hu,hv,show ΦF (SpotQ Y0 (Λpay T∘ Q))=SpotQ YC (Λpay T∘ Q) from by_column ΤG (H.Ctags U V L d) Y0 YC r _]; exact Arriba ..
#print axioms paths_e
end CoeffArc.Directory
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
