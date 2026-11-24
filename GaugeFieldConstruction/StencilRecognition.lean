import GaugeFieldConstruction.StencilSieve
import GaugeFieldConstruction.StencilLease
/-!
# Recognition lemma. Actual operator prices after subtracting off vanishing APPROXIMATION error from stamp.
-/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace Discipline
open RosterJ BoonsθJ SignetS Patrons ChSigFe Shower SelectionAnalysis Repertoire InterR
open OS.Semigroup MacroGrid
open Complex SignetS
open GaugeFieldConstruction.Phys GaugeFieldConstruction GaugeFieldConstruction.Ember
open Calibration.Floor Calibration
open QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
open CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers CF.Papyrus.Franc.Loaves
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper Abacus CheckerFlag SlopeCharge Maxwell
open Fame.Regulator Fame.Regulator.Internal
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade Papal.SkyTax _root_.YM.Regis.Head
open Tabletop Shrine Ione.Clock Moto
open XGarden.MastTin.ArtCart SpaΘ Fathom Ember
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble MarbleFace
open MezzoBill ConsoleθN Discipline
variable {P:Spine}{R:Signed × Bool}{C:Clip→ℝ}{O:PinRack→Py.Rate.LocalLimit.Badge}{r:TintDemand}{N:ℕ}
variable {πQ:YardμN P C O r N}{J:InterR}{α:finsJ}{m:ℕ}(Y:ConsoleθN πQ R α J m)
variable {Z:ℕ→ℕ}{f0:ℕ}{η:Type}[Fintype η][Nonempty η]{M:P.par.R.L.val%16=1}{H A a b φ:ℝ}
local notation "Λ"=> P.par.R.L
variable (W:HeartClock P f0 H A a b φ P.jump128 M Z η)(e:Melodic P η A f0 Z)(L:P.NightCop)(h:Tendsto Z atTop atTop) (sC:SocietyNX P πQ.p)
local notation "q"=> ΤbandR three
local notation "∆"=> ScaleμJ P.par (ΤbandR three).val
local notation "vx"=> unitX P
open Dovetail
open Lead
open Submodule
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable (i:Axis)(x:P.Spectrum0 3)
local notation "χ" j:max=> P.advocate 3 x j
local notation "H'" j:max=> P.ManyF j (χ j)
local notation "T₀" j:max=> P.seasons j (χ j)
local notation "Π" j:max=> projectPrice P j x
-- package BSOT criterion holding also for all pads moving. Starting from pp norm rite.s0.
section
variable (p:Cover)(hp:ResidualPermit p)
include hp
lemma moves_zero : Tendsto (fun v:ℕ=> home P p v) atTop (𝓝 0):=by
 rw [tendsto_pi_nhds]; intro i; rw[tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ P.macroStep_zero; exact Eventually.of_forall (fun s=> by simpa [Real.norm_eq_abs] using home_room P hp s i)

lemma at_stamp (K:ℕ→ P.Apron)(T:ℝ→ℝ→(P.ManyF i (P.advocate 3 x i)).Op)(c:ℕ→ℂ)(w: (T₀ i).Credits 0 T)
    (u:Tendsto (fun t=> (K t).realWidth P i) atTop (𝓝 0))
    (hz:∀ l r:ℝ,0<l→0<r→Tendsto (fun t=> c t • annoFace P i (P.advocate 3 x i) t (home P p t) (K t) l r) atTop (𝓝 (T l r)))
    {l r:ℝ}{α β:ℕ→ℝ}(hv:0<l)(hk:0<r)(a:Tendsto α atTop (𝓝 l))(b:Tendsto β atTop (𝓝 r)):
 BSOT (fun t=> c t • P.base i (χ i) (K t) (α t) (β t)) atTop (T l r):=by
 exact neutralStampSt P i (χ i) _ (moves_zero (P:=P) p hp) K T c w u (fun l r p t=> BSOT.fromNorm (hz _ _ p t)) hv hk a b
variable (k:Cover)
local notation "Υ"=> trueKey P h e L
noncomputable abbrev payOriginSt (j:Axis)(U:Soul) (s:ℕ): P.Apron := JpriceApp P p M hp ((Υ s) U) j s
variable (U:Soul)(j:Axis)
local notation "Ζ" j:max=>priceX P h e i p M L hp j (χ j) U
include e W h x L
lemma floor_price (l r:ℝ)(hL:0<l)(hR:0<r): BSOT (fun v:ℕ=> P.base j (χ j) (payOriginSt (M:=M) e L h p hp i U v) l r) atTop (priceX P h e i p M L hp j (P.advocate 3 x j) U l r):=by -- Π header i then x. 
 apply BSOT.congr' (at_stamp (P:=P) (i:=j) x p hp _ _ (fun k:ℕ=>(1:ℂ)) (conto_lag P h e i p M L hp j _ U W) (?_) (?_) hL hR tendsto_const_nhds tendsto_const_nhds)
 · exact Eventually.of_forall fun _=>one_smul ..
 · simp_rw[Hmu_width]; simpa using P.macroStep_zero.const_mul (kinWidth P:ℝ)
 intro l r hL hR; simp only [one_smul]; exact powerColor P h e i p M L hp j _ U W hL hR
local notation "Ω_(" j ")"=> P.advocate 3 x j -- comment
-- the singular padded operator shelf row. Notice comparison on ALL gates at time-axis not comparing all stance axioms. Pays stencil convergence even across all axes projections in the statement (C Emma).
include Y sC
set_option maxHeartbeats 430000 in
lemma chargedCurrentAndIfLevel (k:ℕ)(t:Y.LeaseVU k) : ∃ V:UV three, (∀ j (l r:PermWallJ P), projectPrice P j x (Y.RoomsVU (Y.DeckLiftVU k V) j l r) = priceX P h e i p M L hp j (P.advocate 3 x j) U (StallJ P l) (StallJ P r)) ∧
           ((∀ Z0: UV three, (∀ j (l r:PermWallJ P), projectLine P j x (Y.RoomsVU (Y.DeckLiftVU k Z0) j l r)=0)→Z0=0)→ VistaX 0 (Y.RoomsVU (Y.DeckLiftVU k V)) (fun s=> (payOriginSt (M:=M) e L h p hp i U s).F)) :=by
 -- restore approx representation on A_i. q0 deck chart.
 obtain ⟨F,Hf,hF⟩:=can_stamp Y W e L h sC U i p hp -- tune
 let V(s:ℕ):=payOriginSt (M:=M) e L h p hp i U s
 have hb(j:Axis):Tendsto (fun s=> (V s).realWidth P j) atTop (𝓝 0):= by unfold V payOriginSt; simp_rw[Hmu_width]; simpa using P.macroStep_zero.const_mul (kinWidth P:ℝ)
 exact sieveSt Y x V _ (fun s=>rfl) hb (fun j a b=>floor_price (P:=P) W e L h i x p hp U j (StallJ P a) (StallJ P b) a.2 b.2) k t F Hf hF
lemma chargedCurrent (k:ℕ)(t:Y.LeaseVU k) : ∃ V:UV three, ∀ j (l r:PermWallJ P), projectPrice P j x (Y.RoomsVU (Y.DeckLiftVU k V) j l r) = priceX P h e i p M L hp j (P.advocate 3 x j) U (StallJ P l) (StallJ P r):= by
 obtain ⟨V,b,h⟩:= chargedCurrentAndIfLevel Y W e L h sC i x p hp U k t; exact ⟨V,b⟩
#print axioms chargedCurrentAndIfLevel
end
end Discipline
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
