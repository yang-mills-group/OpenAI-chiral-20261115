import GaugeFieldConstruction.Dockets
import GaugeFieldConstruction.Weepers
-- Variant schedule of D3 P3
set_option autoImplicit false
set_option maxHeartbeats 200000
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
def tagged_B (Q : LocalLimit.Badge) : LocalLimit.Badge :=fun K L R V B d U W M J F I A C P k γ v t D T h n=> Q K L R V B d U W M J F I A C P k γ v t D T h n ∧ Cash_T V d h
lemma cards {Q:LocalLimit.Badge}(p:Marketable Q): Marketable (tagged_B Q):=by
 constructor; intro K L k e u z A C Pay kc Γ w c g a b Tξ d; obtain ⟨l,H⟩:= p.extra _ _ k e u z A C Pay kc Γ w c g a b Tξ d; refine ⟨l,fun R y v₁ j m V T=>?_⟩
 obtain ⟨E,ht,t⟩:= order_T V (by rw [k]; decide)
 filter_upwards [H _ y v₁ j m V T] with B σ; obtain ⟨X,g,i⟩:=σ; refine ⟨min E X,lt_min ht g,fun d s f U W j F I M S t₀=>?_⟩
 obtain ⟨r,l,w,hg,h⟩:= i d s (f.trans (min_le_right ..)) U W j F I M S t₀; refine ⟨r,l,w,hg,fun M J A' Hv D' z pZ=>?_⟩
 filter_upwards [h M J A' Hv D' z pZ,t d s (f.trans (min_le_left ..))] with h v he; filter_upwards [v] with N hN; exact ⟨hN,he⟩
-- manifest P2-3 installation on any licensed height. P4 added later. All same phase & density throughout.
lemma paid_inches {N:ℕ}{Q:LocalLimit.Badge}{X:TintDemand}(p:LicensedHeight (tagged_B Q) N X P): Cash_T P.V P.d P.h∧ Geometry P∧ Spicing P:=by
 refine ⟨?_,p.geom,p.toll⟩; obtain ⟨Pay,kC,Γ,Tξ,hX,hKc,hΓ,Dg,Pv,P1,P2,P3,T,F,I,mo,A,C',v,V₃,D,c,hD,w,h,e,p,u,Z,E⟩:=p.store; exact E.2
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
