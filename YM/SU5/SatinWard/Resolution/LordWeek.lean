import YM.SU5.SatinWard.Resolution.Dovetail
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open MezzoBill
namespace Dovetail

open Preparation.Tabletop LitCurrent.Chamber StressFlux
open Tilted
/-- Use this *single* sector. No flip-loop on WP. Keep MAIN separation in one plenum to take both ports eventually. Pose estimates work with only the axis-2 Ramsey sprint for averages before selection. -/
abbrev ac2:Tilted.Ramp:=⟨2,3,by decide⟩
-- root station with this orientation. retain K-joint. Need NoAlias.NewDomain comp after orientation. recover by canonical value. use SAME grid. for both fields can rotate that exact root qualification.
abbrev rayPost: Cover:=fun i:Axis=> if i=2 then -1 else 1
local notation "uT"=> ac2
local notation "root"=> rayPost
lemma rayP : ResidualPermit root:=by refine ⟨fun i=>?_,fun i=>?_⟩ <;> (unfold rayPost; split <;> simp)
lemma surveyCost : ac2.s.act rayPost=rayPost:=by funext i; revert i; decide +kernel
lemma aloom : ac2.s ∈ Loomed:= by
 have h:ac2.s= (Signed.mirror 2)*(Signed.mirror 3)*outPlane:=by apply Signed.ext; apply Equiv.ext; exact (by decide +kernel); apply funext; exact (by decide +kernel)
 exact h.symm ▸ mul_mem (mul_mem (mirror_l _) (mirror_l _)) out_l -- imports NS
lemma sweepK : localFace ac2.s (keynote pseV)= keynote pseV:=by unfold keynote; rw [mpse]; unfold cloverKey; rw [local_plus, locale_smul, locale_smul, FF_even.1 _ aloom,FF_even.2 _ aloom]
variable (p:Cover)
lemma actPost : ac2.s.act (homeTag P root+P.sidesPerTick • p)= homeTag P root+ P.sidesPerTick • ac2.s.act p:=by
 let U:= ac2.s.actEquiv (R:=ℤ); have u:ac2.s.act (homeTag P root)= homeTag P root:=by change U _ =_; unfold homeTag; rw [map_nsmul,show U root=root from surveyCost]
 change U _= _; rw [map_add,map_nsmul U P.sidesPerTick]; rw [show U _=homeTag P root from u]; rfl -- ambiguous _
variable (M:P.par.R.L.val%16=1)
local notation "ZQ"=> (tauprint P M rayP)
lemma turnHome : ac2.plan.flee (ZQ+P.jump128 • p)= ZQ+P.jump128 • ac2.s.act p:=by apply Satin.nodeC_inj; rw [←Tilted.Ramp.moved_wing, relation_core,relation_core,show nodeC ZQ=homeTag P root from (nodeHome P M root rayP).choose_spec,ac2.mode_motion]; exact actPost P p
-- spin rotation stamp: bill and Step sign. direction 3 -> 2. Use Spin.Shift and full label (herm, easily). Carrier.Sign.Real pd.
local notation "Π"=> P.calibration
local notation "Q"=> ac2.cuspF P.calibration
variable (z:Soul)
local notation "Gz"=> dynamicSpin z
lemma arcCost (t:Tilted.Ramp)(i:Axis)(x:Cover): t.cuspF P.calibration (gardenFlower P.calibration x (t.s.perm i) Gz)=StressFlux.sign t.s i • gardenFlower P.calibration (t.plan.flee x) i Gz:=by
 have h:ChiralX 0 Gz:=(Θc.equivFun.symm z).property; funext m; let N:= P.calibration.c m; let T'(x:Axis)(i:Site N):= SignSlot.onsiteSensor i (Tap.petal x ⊗ₖ Gz); have ht:Dirfield N T':=⟨fun s p a b w i=>spin_shift s i Gz h.herm _ _ w p⟩; change t.bill (T' (t.s.perm i) (wrap N x))=StressFlux.sign t.s i • T' i (wrap N _); rw [← Shape.mill]; exact ht.turned _ _ _ ((gardenShot P.calibration (t.s.perm i) Gz x).support m|>.mono (subset_univ _)) -- names space `Tap` etc.
lemma pay_arc : StressFlux.sign ac2.s (2:Axis)=(-1:ℝ):=by unfold StressFlux.sign; rw [if_pos (by decide +kernel)]
local notation "ν"=> P.sidesPerTick
variable {v:ℕ} (q:payable P v 2)
noncomputable def RunH(v:ℕ)(p:Cover)(j:Axis):P.Test:= P.chartAll p (JpriceApp P rayPost M rayP z j v).F
noncomputable abbrev RunK:= P.chartAll p (soloV P v q rayPost rayP pseV).F
local notation "Lζ" p:max j:max=> (RunH P M z v p j)
lemma run_stencil : Q (RunK P p q).val=(RunK P (ac2.s.act p) q).val:=by
 let o:= homeTag P root; have h(p:Cover): RunK P p q= τEnd P v (o+ν • p) pseV q:= temple_sweep ..; rw [h,h]; change Q (bumper P v (o+ν • p) (keynote _))=bumper P v _ _; rw [bump_tilt, sweepK, ac2.mode_motion]; unfold o; rw [actPost]
lemma literals (j:Axis): RunH P M z v p j= chapterFoot P (letterShape (J:=P.calibration) (Λ:=P.par) j v z) (ZQ+ P.jump128 • p):= calendar_moves ..
lemma run_billH : Q (Lζ p 3).val= -(Lζ (ac2.s.act p) 2).val:=by
 let o:= ZQ+ P.jump128 • p; let U:= Π; let F(x j):= gardenFlower P.calibration x j Gz; let h:= arcCost P z ac2 2 o; rw [show ac2.s.perm 2=3 from ac2.sab,pay_arc, neg_one_smul, show ac2.plan.flee o= _ from turnHome P p M] at h; rw [literals, literals]; change Q (spineField P.par P.calibration v 3 z o)= -(spineField P.par P.calibration v 2 z _); rw [colorsHere,colorsHere,← Complex.coe_smul, ← Complex.coe_smul, Tilted.Ramp.over_z,h,Complex.star_def,Complex.conj_ofReal,smul_neg] -- syntax Q notation parser loco
local notation "E"=>P.E
lemma paySatin(f:P.Test): E v (Q f.val) = star (E v f.val):= Tilted.step_Price P.run P.large ac2 v P.law (show TestFamily P.calibration true f.val from f.property)
lemma accounts (p' : Cover): star (P.E v ((RunH P M z v p 3)*(RunK P p' q)).val)= -(P.E v ((RunH P M z v (ac2.s.act p) 2)*(RunK P (ac2.s.act p') q)).val):=by
 rw [← paySatin]; change E v (Q ((Lζ p 3).val*(RunK P p' q).val))=_; rw [Tilted.Ramp.over_times, run_billH, run_stencil,neg_mul]; let X:P.Test:= (Lζ (ac2.s.act p) 2) * RunK P (ac2.s.act p') q; -- need E acts only on Family arbitrary maybe not linear unless on tests. `occupied recovery`. inspect
 have h: ∀ f:P.Test,P.E v (-f.val)= -(P.E v f.val):=by
    intro f; rw [←show E v (-f).val= E v (-f.val) from rfl, ←P.occupied 3 v (-f), ←P.occupied 3 v f, ←P.at_label, ←P.at_label, map_neg]; change inner ℂ _ (-(P.compressed 3 v f _) ) = -inner ℂ _ (P.compressed 3 v f _); rw [inner_neg_right]
 exact h X
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
