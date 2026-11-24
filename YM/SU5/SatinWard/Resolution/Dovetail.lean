import YM.SU5.SatinWard.Resolution.Awning
import YM.SU5.SatinWard.Resolution.Verano
import YM.SU5.SatinWard.Resolution.Gips
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
variable {v m:ℕ}(q:Cover)(p:ResidualPermit q)(M:P.par.R.L.val%16=1)(z:Soul)(i:Axis)(x:P.Spectrum0 i)
local notation "σ" v:max=> P.macroStep v
local notation "ℛ"=> P.locate i x
local notation "π"=> P.reprise i x
local notation "ℜ"=> P.charter i x
local notation "fee" i:max => home P q i
variable (mu:Axis)
abbrev colorPay (j k:Axis) :ℝ:= StressFlux.sign (Signed.mirror j) k
lemma colorPay_eq (a b: Axis) : colorPay a b= (if a=b then (-1:ℝ) else (1:ℝ)):=by unfold colorPay StressFlux.sign; by_cases h:a=b <;> simp [Signed.mirror,h, Ne.symm] -- tune
abbrev flipline(j:Axis)(q: Cover):= Function.update q j (-(q j))
local notation "q'"=> flipline i q
include p in
lemma makesColor : ResidualPermit q':=by
 refine ⟨fun x=>?_,fun v=>?_⟩
 · by_cases h:x=i; · subst x; simpa [flipline] using (p.odd i).neg
   simpa only [flipline,Function.update_of_ne h] using p.odd x
 by_cases h:v=i; · subst v; simpa [flipline] using p.cost i
 simpa only [flipline,Function.update_of_ne h] using p.cost v
lemma flip_Q (v:ℕ)(k:Axis): home P (flipline i q) v k= if i=k then -(home P q v k) else home P q v k:=by
 unfold home flipline geoAt gaugePosition homeTag; by_cases h:i=k
 · subst k; simp
 simp [h,Ne.symm h]
lemma flip_pay : (plane i 0).motion (homeTag P q)=homeTag P q':=by
 funext k; rw [fling_move]; unfold homeTag flipline; by_cases h:i=k<;> simp [h,Ne.symm]
include p
local notation "v'" => makesColor q p i -- maybe order
lemma phase : (plane i 0).flee (tauprint P M p) = tauprint P M v':=by
 apply Satin.nodeC_inj; rw [← MezzoBill.flutter (z:=tauprint P M p) i, show nodeC (tauprint P M p)=homeTag P q from (nodeHome P M _ p).choose_spec,flip_pay]; exact (nodeHome P M _ v').choose_spec.symm -- z field argument
local notation "N"=> P.Test
local notation "JV" u:max=> JpriceApp P q M p u mu v
local notation "Ju" u:max=> JpriceApp P (flipline i q) M (makesColor q p i) u mu v
local notation "Gz"=> dynamicSpin z
lemma harvest : (JpriceApp P q M p z mu v).F=(↑(vigorΩ P.par v):ℂ) • planC P (tauprint P M p) mu Gz:=by
 apply Subtype.ext; change spineField P.par P.calibration v mu z (tauprint P M p)= (↑(vigorΩ P.par v):ℂ) • gardenFlower P.calibration (tauprint P M p) mu Gz; rw [Complex.coe_smul]; exact colorsHere .. -- omit p cannot omit implicit used
lemma spunM : P.reflectTest i (JV z).F= (↑(colorPay i mu):ℂ) • (Ju z).F:=by
 let p':= (↑(colorPay i mu):ℂ); rw [harvest, harvest P (flipline i q)]; let h:ChiralX 0 Gz:= (Θc.equivFun.symm z).property; let vK:ℂ:=↑(vigorΩ P.par v)
 have k:P.reflectTest i (planC P (tauprint P M p) mu Gz)= p' • planC P (tauprint P M v') mu Gz:=by
    apply Subtype.ext; rw [←phase P q p M i]; change mirror P.calibration i 0 (gardenFlower P.calibration (tauprint P M p) mu Gz)= p' • _; unfold p'; rw [Complex.coe_smul]; exact mirrorE mu Gz _ h i 0
 rw [P.scale_mirror,k,Complex.star_def,Complex.conj_ofReal,smul_comm]
variable {s f0:ℕ}{Z:ℕ→ℕ}{C H A:ℝ}{η:Type}[Fintype η](ρ:Piano P f0 C H A η Z) (q₂:payable P v 2)
local notation "K"=> soloV P v q₂ q p pseV
local notation "K'"=> soloV P v q₂ (flipline i q) (makesColor q p i) pseV
lemma glowM : P.reflectTest i (K).F= (K').F:=by change P.reflectTest i (τEnd P v (homeTag P q) pseV q₂)= _; rw [temple_reflect,flip_pay]; rfl -- notation parser needs (K).F
-- Supply h for chosen orientation, both padded through anchor qualifications. use rawBase_kiss then compare any shares. Price of K remains PSA after coefficient multiplication. Future Wick uses τv and const l,r external.
variable (X X':P.Apron)(d:ℝ)(w:0 ≤ d)(h:X.s=v)(eh:X'.s=v)(wu:X.realWidth P i=d)(wo:X'.realWidth P i=d)
variable (u:ℂ)(k:P.reflectTest i X.F=u • X'.F)(l r:ℝ)
local notation "Y"=> home P q v
local notation "qY"=> home P (flipline i q) v
include h eh wu wo k
omit p in
lemma recolor (hl:d+ home P q v i≤l)(hr:d-home P q v i ≤ r): star (annoFace P i x v Y X l r)= u • annoFace P i x v qY X' r l:=by
 let L:= l-home P q v i; let R:= r+home P q v i; let Xo:= X.kiss P i
 have hb:home P (flipline i q) v i= -(home P q v i):=(flip_Q P q i v i).trans (if_pos rfl)
 have hu:Xo.realWidth P i=d:= wu; have H0:Xo.s=v:= h; have H1:Xo.F=u • X'.F:=k
 have hK: (P.rawBase i x Xo R L)=u • P.rawBase i x X' R L:=by
    let t:= P.grasp_fixed i x Xo (a:=R) (by unfold R; linarith only [hr,hu]) (b:=L) (by unfold L; linarith only [hl,hu]); have hq:= P.grasp_fixed i x X' (a:=R) (b:=L) (by unfold R; linarith only [hr,wo]) (by unfold L; linarith only [hl,wo]); rw [H0,H1] at t; rw [eh] at hq; exact t.unique (hq.smul u) -- signatures check
 unfold annoFace; rw [← P.reprise_rawBase, ←P.reprise_rawBase,P.locate_star,P.reprise_star]; rw [hb, sub_neg_eq_add, ←sub_eq_add_neg]; change ℛ (-(home P q v)) ((π) (star (P.rawBase i x X L R)))= _; rw [show star (P.rawBase i x X L R)= P.rawBase i x Xo R L from ?_,hK,P.reprise_smul,P.locate_smul]
 · apply congrArg; apply P.locate_same; intro k e;
   simp only [Pi.neg_apply, flip_Q, if_neg (Ne.symm e)]
 unfold Xo; rw [P.rawBase_kiss]; rfl
#print axioms spunM
#print axioms glowM
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
