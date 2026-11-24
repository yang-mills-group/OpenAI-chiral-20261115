import GaugeFieldConstruction.EqualTrialAssembly
/-! # The two senses of generation current: certify differing time-reflection star even on UV3 orientation. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 7500
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
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace
namespace ContinuumConstruction
-- Data telescope. Naming concordance through the flagship API (QFT: E to Story,
-- L & G to continuity, calendars to labels and paths).
variable
  {nLeaf : ℕ}
  {process : Spine}
  {scale : process.Register}
  {production : YardμN process CostUpVU PolRun PriceArtVU nLeaf}
  {growth : InterR}
  {roles : ConsoleθN production ΓmotVU 0 growth ΓstageVU}
  {axes : Axis → GaugeFieldConstruction.Empire.Across}
  {comparison : Sheds roles.Crew_N axes}
  {approvals : Supplies comparison}
  {stress : Ticket roles.Gamma_N approvals}
  {vacuum : process.Spectrum0 3}
  {costAnalysis : process.Ellis 3 vacuum}
  {c : ℕ → ℕ}
  {collars : ℕ→ℕ}
  {layers : NSF.Boundary.Waves (roles.RadianceVU stress)}
  {response : NSF.Boundary.Surface (roles.RadianceVU stress)}
  {continued : NSF.Boundary.Surface.Aurora response NSF.LD.drapeL}
  {model : roles.GlowVU stress vacuum (le_refl _) layers response}
  {screens : process.Poll 3}
variable (Certificate : Assembled (scale:=scale) (costAnalysis:=costAnalysis) (c:=c) (collars:=collars)
   (continued:=continued) (model:=model) (screens:=screens))
open ConsoleθN
open NSF.Boundary
open YM.Boundary (Test4 Joint)
open GaugeFieldConstruction.Invoice.curvΝ
open Stage Stage.Cell
open Glaze CF.XGarden.MastTin.ArtCart.BluffV CF.XGarden.MastTin.ArtCart.BluffV.Fables
open MacroGrid

open SecondOrient
local notation "Φₐ"=> roles.PerD_VU stress (le_refl _)
local notation "φ"=> model.system.operators.field
namespace SceneLegend
open GaugeFieldConstruction.Stage
local notation "sF" i:max => roles.DeckLiftVU i
section
variable (a b:Axis)(m0:IdWitPV)(h:m0.2.1≠m0.2.2)(θ:ℂ)
local notation "Jφ" => (Calibration.spinFrame three (Signed.mirror a)).comp (Calibration.shade three)
include h
-- use time or another half mirror that SWITCHES m0, so no Herm slot
lemma slotNot_real_st (p:θ≠0): (Jφ) (SpinSlot3 m0 b) ≠ θ • SpinSlot3 m0 b:=by
 let j:=m0.2.1; let k:=m0.2.2
 let W:=SpinSlot3 m0 b
 have hs: Calibration.rev (Signed.mirror a) m0 ≠ m0:=by rintro E; unfold Calibration.rev at E; rw [signBit_mirror] at E; simp at E; exact h (congrArg (Prod.fst ∘ Prod.snd) E).symm
 intro u; change (Calibration.spinFrame three (Signed.mirror a)) (Calibration.shade three W)=θ • W at u
 let V(v:CogPV):UF three:=v.2.2.1 m0
 have he:=congrArg V u; change (Calibration.matter three).moves (Signed.mirror a) ((Calibration.shade three W).2.2.1 (Calibration.rev _ _))= θ • W.2.2.1 m0 at he
 let F:= (Calibration.RawBank.DeckF three).issue (ket b); have hf:F≠0:= fun e=> ζτN b (by rw [← vValPV]; exact congrArg Subtype.val e)
 change (Calibration.matter three).moves (Signed.mirror a) (Calibration.flipT _ (W.2.2.1 _))= _ at he; unfold W at he; rw [show (SpinSlot3 m0 b).2.2.1 (Calibration.rev _ _)=(0:UF three) from ?_, map_zero,map_zero,show (SpinSlot3 m0 b).2.2.1 m0=F from ?_] at he
 · exact (smul_ne_zero p hf) he.symm
 · exact (riseInPV ..).trans (if_pos rfl)
 exact (riseInPV ..).trans (if_neg (Ne.symm hs))
variable {i:ℕ}(t:roles.LeaseVU i)
open _root_.YM.GaugeFieldConstruction.Ember.Volumetric.FirstPackMars.CloverRule
include t
lemma off_theta_st (p:θ≠0): TurnupMars a (roles.StaturePV i m0 b) ≠ θ • roles.StaturePV i m0 b:=by
 let F:= roles.BinSchVU i three t
 let x:=SpinSlot3 m0 b; let W:=Calibration.spinFrame three (Signed.mirror a) (Calibration.shade three x); let T:= sF i
 have e: roles.StaturePV i m0 b=LowIncPV (F.c x):= roles.BerylStepsPV i t _
 intro z; change TurnupMars a (T x)=θ • T x at z; rw [←map_smul] at z
 apply slotNot_real_st a b m0 h θ p; apply roles.DeckPortInvVU i t; change T W= _; have he:T W=TurnupMars a (roles.StaturePV i m0 b):=by
    dsimp only [T]; rw [roles.BerylStepsPV i t W, e,TurnupMars,fittedTurn_st]; change LowIncPV (F.c W)=_
    unfold W; rw [F.h,F.charge] -- pattern
 exact he.trans z
end
-- synth
lemma off_op_st {i:ℕ}{m₀:IdWitPV}(t:roles.LeaseVU i)(h:m₀.2.1≠m₀.2.2)(b:Axis) (V:UV four){θ:ℂ}(p:θ≠0)(u:TurnupMars 3 V= θ • V) : (φ) ((roles.PerD_VU stress (le_refl _)).TinCanL (roles.StaturePV i m₀ b)) ≠ (φ) ((roles.PerD_VU stress (le_refl _)).TinCanL V):=by
 let x:=roles.StaturePV i m₀ b; let F:=(roles.PerD_VU stress (le_refl _)).TinCanL; have hx:x≠V:=by rintro f; exact off_theta_st (roles:=roles) (i:=i) 3 b m₀ h _ t p (by change TurnupMars 3 x = θ • x; rw [f]; exact u)
 obtain ⟨z,h⟩:= model.course.faithful (F x - F V) (sub_ne_zero.mpr (fun k=>hx (F.injective k))); intro e; apply h; rw [map_sub,LinearMap.sub_apply]; exact sub_eq_zero.mpr (LinearMap.congr_fun e z)
#print axioms off_op_st
end SceneLegend
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
