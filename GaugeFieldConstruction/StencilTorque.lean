import GaugeFieldConstruction.StencilSite
import GaugeFieldConstruction.StencilPaintLevel
import YM.SU5.SatinWard.Resolution.Meetup
import YM.SU5.SatinWard.Resolution.Verano
import GaugeFieldConstruction.StencilWidget
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
open RosterJ BoonsθJ SignetS Patrons
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
open SoulField Verdance Mezzo
open OS.Semigroup
variable {P:Spine} {M:P.par.R.L.val%16=1}
open Jubilee
open CF.Sour CF.Salt CF.Hive CF.Levier
lemma buysShiftSt (R:Signed)(y:Cover)(hp:ResidualPermit y): ResidualPermit (R.act y):=by
 unfold Signed.act; constructor
 · intro i; split <;> first | exact (hp.odd _).neg|exact hp.odd _
 intro i; split <;> simpa using hp.cost (R.perm.symm i)
variable (p:Cover)(hp:ResidualPermit p)(μ:Axis)(C:Signed)
local notation "D" => (C⁻¹.act p)
local notation "d" => buysShiftSt C⁻¹ p hp
local notation "𝓣" => tauprint P M hp
local notation "𝔲" => tauprint P M d
local notation "u" => P.jump128
lemma stampPoseSt (x:Cover): C.act (nodeC (𝔲+ P.jump128 • C⁻¹.act x))= nodeC (𝓣+ P.jump128 • x):=by
 have actN (x:Cover)(n:ℕ): C.act (n • x)=n • C.act x:= map_nsmul C.actEquiv n x
 rw [relation_core,relation_core,show nodeC (𝔲)=homeTag P D from (nodeHome P M _ d).choose_spec, show nodeC (𝓣)=homeTag P p from (nodeHome P M _ hp).choose_spec]; unfold homeTag; rw[Signed.act_add,actN,actN,Signed.act_inv,Signed.act_inv] -- tune
-- supports actual Civic travel.Of HEIGHT
local notation "cμ" => ((↑(StressFlux.sign C μ):ℂ))
lemma stampGrowthSt (z:Soul)(s:ℕ)(y:Cover): VogueκS P (PrimeScriptR C 0) false
      (P.chartAll y (JpriceApp P p M hp z (C.perm μ) s).F)
      (P.chartAll (C⁻¹.act y) (cμ • (JpriceApp P D M d z μ s).F)):=by
 rw [map_smul]; intro n; let F:=P.chartAll y (JpriceApp P p M hp z (C.perm μ) s).F; let G:=P.chartAll (C⁻¹.act y) (JpriceApp P D M d z μ s).F; let R:= P.calibration.c n;
 let S:= Levier.ray (N:=R) false (PrimeScriptR C 0); let Q(t:Cover)(i:Axis):= letterShape (J:=P.calibration) (Λ:=P.par) i s z
 let UZ:= 𝓣+ P.jump128 • y; let VZ:=𝔲 + P.jump128 • C⁻¹.act y; let U:= wrap R UZ; let V:= wrap R VZ; let K(i:Axis)(x:Site R):= onsiteSensor x (CF.Tap.petal i ⊗ₖ dynamicSpin z); let w:= vigorΩ P.par s
 have hx(x y':Cover)(i:Axis): ((P.chartAll y' (chapterFoot P (Q x i) x)).val n)= w • K i (wrap R (x+P.jump128 • y')):= by
    rw [calendar_moves]; change spineField P.par P.calibration s i z (x+P.jump128 • y') n= _; rw [colorsHere]; rfl
 have he: Earlier S U V:= wakeAxisSt C _ _ (stampPoseSt (P:=P) (M:=M) p hp C y) R
 have ht: ChiralX 0 (dynamicSpin z) := (Θc.equivFun.symm z).property
 change YM.CF.Buffered.Jubilee.SweepTurn R S ((P.chartAll y (chapterFoot P (Q 𝓣 (C.perm μ)) 𝓣)).val n) ( (cμ) • ((P.chartAll (C⁻¹.act y) (chapterFoot P (Q 𝔲 μ) 𝔲)).val n))
 rw [hx 𝔲]; exact spinRecited_st μ R C _ _ (stampPoseSt (P:=P) (M:=M) p hp C y) w _ ht.herm _ (hx 𝓣 y _)
#print axioms stampGrowthSt
end Discipline
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
