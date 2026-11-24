import Verses.AnchorP
import Verses.Culinary
import Verses.Shade
import Verses.Sensor
import YM.CF.Muse.Sail
import Verses.Staging
import Verses.Sensor
import Verses.Billing
import Verses.Fusing
import LusterS.Husk
import YM.SU5.Velvet.Hemline
import Refrain.Seismic
import YM.SU5.Velvet.Viper
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option maxHeartbeats 320000
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
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask
set_option maxHeartbeats 550000
lemma closeV (s i k:ℕ)(hp:closeDen Y s i k):VLine Y s i k ((ℶ s)^ (-(8:ℝ)⁻¹)):=by
 obtain ⟨a,b,v⟩:=hp
 obtain ⟨_,he,_⟩:=angle_pay (gram Y s i k).J.M P.K.j P.U _ (by rw [P.kJ]; omega) (P.J.gran.trans ((Y.voyage i).ownership s).size) P.W.health
 unfold VLine sod entryFin; dsimp only
 let A:=gram Y s i k; let N:=count Y s i
 let J:=Fineness.gaugedBase P.L A.beta (More N) (P.V.L.H (Y.uv k-s))
 change Real.exp (J+angleFin A.J.M N P.K.j- _* sites N) ≤ _
 rw [he]; exact v

/-- stronger inequality for scalar Mark enough for peek clover proposals, all marking still regulator-scaled on Gram. -/
def FoilMark {N:Side}(F:Mark N)(c:ℝ):Prop:=∀ x:Fields N,∃ z:ℂ,F x=z • 1 ∧ ‖z‖≤c
lemma pays_scalar {N:Side}(M:Op (Single N))(h:IsStarProjection M){F:Mark N}{c:ℝ}(p:FoilMark F c)(x:Fields N)(k:ℕ) : upPrice N M h k (F x) c:=by
 intro g X; obtain ⟨s,e,u⟩:= p x; rw [e,Shaft.glow_free,Shaft.glow_nil,norm_smul,norm_one,mul_one]; exact u
lemma foil_nonneg {N:Side}(F:Mark N){c:ℝ}(p:FoilMark F c):0≤c:=by obtain ⟨s,e,h⟩:=p (1,1); exact (norm_nonneg _).trans h

def BoltCharge : Prop:=∀ᶠ s:ℕ in atTop,∃ q b C δ a,0<b∧0<C∧0<a∧0<δ∧∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick≤k→s≤Y.uv k→ let V:=gram Y s i k; let N:=count Y s i
   Gust Y s q b a C δ i ∧ -- Gust n worked, use Gust with i threshold from n? Gust mono
   ∀ (R:GramM N)(α ν κ:ℝ)(f: Arc_r R P.h α ν κ),ProperT V R → ∀ (F:Mark N) (D:ℝ),0≤ D →(∀ (y:Orbit N),let S:=spar 4 R.J.M (1:Pane N);∀ p:IsStarProjection S, upPrice N S p q (F (y.1,Papal.room Y s i y)) D)→
             WeightedMark Y s i k R F (flagCup V.p P.K.top.clip V.beta/2) ≤ D*Real.exp ((α+ν+κ+6*parcelF (ℶ s))*sites N)
lemma earns_foil {δ C a b:ℝ}(p:P.d≤δ)(hs:0<δ)(v:0<C)(c:0<b)(h:0<a)(E:∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val → Sow 4 N a C δ)(f:CF.Papyrus.Franc.postage 4 b)(Z:(b+1)*180*(1+C)≤P.h)(H:∀ᶠ s in atTop,∀ i k,(Y.voyage i).kick≤k→s≤Y.uv k→ closeDen Y s i k) : BoltCharge Y:=by
 unfold BoltCharge
 filter_upwards [gust_e Y p hs v c h E f Z,H,prong_first Y 1, (turnover P).eventually_ge_atTop 1] with s ⟨q,n,iH⟩ hx hm hg
 refine ⟨q,b,C,δ,a,c,v,h,hs,(eventually_ge_atTop n).mono (fun i e k u t=> ?_)⟩; intro V N
 exact ⟨⟨fun _ y=>iH.bill ‹_› (e.trans y)⟩,fun R α ν κ f g F D h v=>hull_pressure Y s i k t q n b a C δ iH e (hm i k t) (closeV Y _ _ _ (hx i k u t)) R f g F h v hg⟩ -- tune binder name

end Papal
end LocalLimit
end Rate
end YM.CF.Py
