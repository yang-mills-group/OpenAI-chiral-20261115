import GaugeFieldConstruction.Kuriso
import GaugeFieldConstruction.Kans
import GaugeFieldConstruction.Trump
import GaugeFieldConstruction.IconF
import YM.SU5.Selected.Lantern.Petrol
import YM.SU5.Celeste.Pass
import GaugeFieldConstruction.Payola
import GaugeFieldConstruction.Lycoris
import GaugeFieldConstruction.Pelota
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Postmark
import GaugeFieldConstruction.Harries
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open scoped YM.CF.Mew
open Fock.Flux Girt TableF TableF.Lenten.Layout Gleam.Guide CF.XGarden CF.XGarden.MastTin ArtCart Zpress ScopeU Buffered
open FrameP
open Violets ProbabilityTheory Regis.Head Regis.Head.Brecht
open Gleam.Guide.Pitcher Coins Pacts Prims
-- notation state.
open Lamour.Bridge.Celeste (liftMoney)
open Vale.Veins Exterior Matrix
variable (s:ℕ) (i k:ℕ→ℕ)(h:Tendsto i atTop atTop)(g:Tendsto k atTop atTop)
local notation "NT" z:max => count Y s (i z)
local notation "Nr" z:max => More (NT z)
local notation "Tę" z:max => prayO Y s (k z)
def κg (x y:Wα):ℂ:= if x.2.2=y.2.2 then ∑ r:TypeFace 1,gridQ (LensO x) (LensO y) r else 0
abbrev κF (x y:Wφ):ℂ:=if y.2.2=x.2.2 then RomT (y.1-x.1) x.2.1 y.2.1 else 0
-- h binds i implicit but include
include h
lemma ownPack : Tendsto (fun j=> NT j) atTop atTop:=tendsto_atTop.mpr fun k=> ((count_grows Y s).comp h).eventually_ge_atTop k.val
lemma pad_T : ∀ᶠ j:ℕ in atTop,Kea.Pad 4 (NT j):=by obtain ⟨n,h⟩:=Kea.gave 4 (by decide); exact (((count_grows Y s).comp ‹Tendsto i atTop atTop›).eventually_ge_atTop n).mono (fun j p=>h _ (even_with Y s (i j)) p)
include g
def RingW (x y:Wα)(j:ℕ):ℂ:=if p:s≤ Y.uv (k j) then GaWin Y s (i j) (k j) p x y else 0
def Gutter (x y: Cover): Prop:=42< Signal.Interval.separationCost x y
lemma Salmon (x y:Wα)(p:Gutter x.1 y.1): Tendsto (RingW Y s i k x y) atTop (𝓝 (κg x y)):=by
 have hh : Tendsto (fun j=> Y.uv (k j)) atTop atTop:=Y.uv_grows.tendsto_atTop.comp g; let N:=fun j=>NT j; let C':=fun j=> More (N j); let q:=fun j=> Tę j; have hp:Tendsto N atTop atTop:=ownPack Y s i h
 have hz:Tendsto C' atTop atTop:=tendsto_atTop_mono (fun j=> (show (N j).val≤ (N j).val*2 from (by omega))) hp
 have hL:Tendsto q atTop atTop:=by
    apply Filter.tendsto_atTop.mpr; intro T; filter_upwards [hh.eventually_ge_atTop (s+T.val)] with j p; let l:= Y.uv (k j)-s; change T.val ≤ (P.R.L ^l).val; have hv:l≥ T.val:= by unfold l; omega
    have hb:2≤P.R.L.val:=(show 2≤3 by decide)|>.trans P.R.coarse; exact hv.trans ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hb l))
 let Zs:Finset Cover:= {x.1,y.1}; have ht:= pier_S (LensO x) (LensO y) hz hL (fun t=>even_two.mul_left _) (fun i=>P.R.odd_side.pow) -- tune def Ar
 have he:∀ᶠ z:ℕ in atTop,Gutter (x.1) (y.1) ∧ 42 < separation (wrap (C' z) x.1) (wrap (C' z) y.1):=by filter_upwards [hp.eventually (liftMoney Zs)] with i t; exact ⟨p,(by unfold C'; rw [t _ (mem_insert_self ..) _ (mem_insert_of_mem (mem_singleton_self _))]; exact p)⟩
 let L:= if x.2.2=y.2.2 then (1:ℂ) else 0; unfold κg; split_ifs with H
 · refine ht.congr' ?_; filter_upwards [he, hh.eventually_ge_atTop s] with j p hp; unfold RingW; rw [dif_pos hp,WtrP Y s (i j) (k j) _ x y p.2,if_pos H]
 refine (tendsto_const_nhds (x:= (0:ℂ))).congr' ?_; filter_upwards [he,hh.eventually_ge_atTop s] with j t p; unfold RingW; rw [dif_pos p,WtrP Y s (i j) (k j) p x y t.2,if_neg H]
def RugF (x y:Wφ)(j:ℕ):ℂ:= Pcω (NT j) ((gram Y s (i j) (k j)).J.M) x y
lemma Swalin (x y:Wφ): Tendsto (RugF Y s i k x y) atTop (𝓝 (κF x y)):=by
 let T:=fun j:ℕ=> (gram Y s (i j) (k j)).J.M; have hp:Tendsto (Subtype.val∘ T) atTop atTop:= tendsto_atTop.mpr (fun d=> (g.eventually (Mileage.backs Y s d)).mono fun j v=> v (i j))
 have he:=dourC (ownPack Y s i h) (fun j=> even_with Y ..) (M:=T) hp x.1 y.1 x.2.1 y.2.1; unfold κF; have ht(j)(t:Kea.Pad 4 (NT j)): RugF Y s i k x y j = if y.2.2=x.2.2 then (stageVolume (NT j))⁻¹*∑ v:Site (NT j),tellerP x.1 y.1 x.2.1 y.2.1 (NT j) (T j) v else 0:= matΘ (M:= (gram Y s (i j) (k j)).J.M) t x.1 y.1 x.2.1 y.2.1 y.2.2 x.2.2
 split_ifs with H; · exact he.congr' ((pad_T Y s i h).mono fun i p=>((ht i p).trans (if_pos H)).symm)
 refine tendsto_const_nhds.congr' ?_; filter_upwards [pad_T Y s i h] with j p; rw [ht j p,if_neg H]
#print axioms Swalin
#print axioms Salmon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
