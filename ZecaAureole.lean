import ZecaFennel
import SatinThinFusionStation
import ZecaTwain
import ZecaMeniscus
import ZecaTeam
import SatinThinFusionTrumpets
import ZecaVat
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P:Spine) (x:P.Spectrum0 3)(Y:ℕ→P.Apron)(c r n:ℕ→ℕ)

lemma Afterimage.radiance {P:Spine}{x:P.Spectrum0 3}{Y:ℕ→P.Apron}
 (h:P.Afterimage x Y)(j:Axis)(l:List Axis):
 ∃ F,P.Iguana j (P.advocate 3 x j) F (fun i=>(Y i).pivot P l):=by
 obtain ⟨F,p⟩:=h.dye j l
 obtain ⟨B,q⟩:=h.dye j (j::l)
 exact ⟨F, Iguana.mk' p q⟩
def spark (z:Lead.Clan)(F:P.Nib 3 (P.advocate 3 x 3)) : P.Nib 3 (P.advocate 3 x 3):= fun a b=> (purePrice z : ℂ) • F a b

local notation "ξ"=> P.advocate 3 x 3
local notation "Q" k:max j:max=> P.stitchApron k (Y j) (c (n j)) (r (n j))

def Aureole: Prop:=
 P.Snowy c r ∧ P.Sown x c r Y n ∧ P.Afterimage x Y ∧
 ∃ F:P.Nib 3 (P.advocate 3 x 3),
 P.Iguana 3 ξ F Y ∧
 ∀ z:Lead.Clan,
 P.Iguana 3 ξ (P.spark x z F) (fun i=> Q z i) ∧
 ∀ (w:Lead.Clan→Prism), P.Iguana 3 ξ
   (P.trophy (P.advocate 3 x 3) (P.spark x z F) (w z))
     (fun i=>P.soldTrumpet Y c r n w z i)

lemma aureole (a:P.Afterimage x Y)(t:P.Snowy c r)(u:P.Sown x c r Y n)
 {q:P.HandleWith x c r Y n}
 {V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
 (v:P.FusionFleet x c r Y n q V): P.Aureole x Y c r n:=by
 obtain ⟨F,h⟩:= a.radiance 3 []
 have g:P.Iguana 3 ξ F Y:=h
 refine ⟨t,u,a,F,g,fun z=>?_⟩
 have e:=P.fennel z x c r Y n g u (v.thin z 3)
 exact ⟨e,fun w=> P.pours_trophy _ (P.spark x z F) _ e v.high.tendsto_atTop (w z)⟩
#print axioms Spine.aureole
