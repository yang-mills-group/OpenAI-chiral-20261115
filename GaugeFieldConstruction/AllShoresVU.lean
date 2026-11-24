import GaugeFieldConstruction.BelleLotusL
import GaugeFieldConstruction.VisPriceVU
set_option autoImplicit false
set_option maxHeartbeats 300000
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
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
variable {cost:ℕ→P.Test→ℂ} {j: Axis}(C:Porch P cost j)
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable {n:ℕ}{S: City} {P0:Axis→Empire.Across} {L:Sheds S P0} {Cu: Supplies L} {u:ℕ→Carat}
-- axis carried thru. CPI covariance proper. Suit has ALL axes declared, no H3 tilt for phase yet
variable (Cw:∀ j:Axis,Porch P cost j)
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P) (G:CloudsL) (t:Ticket u Cu)
open NSF.Boundary NSF.OS.Semigroup -- no OS namespace clash
open NSF.LD
variable (cp:CalRL Cw G R)(h:SurfCheckL G)
local notation "jΤΛ" => timeAxis
open NSF.Work.C20
open Invoice.curvΝ
abbrev PermitAxisVU := timeAxis
abbrev HurtVU (k:ℝ):E4:=k • basis PermitAxisVU
abbrev ManeuverVU (k:ℝ):Points 1:=PinVU (HurtVU k)
lemma manLightVU (k:ℝ)(v:0<k): Nonempty (StallLeadMars PermitAxisVU (ManeuverVU k) P):=by
 apply ReefBedL; constructor
 · intro i j p; exact (p.ne (Subsingleton.elim i j)).elim
 intro i; fin_cases i; change 0< (HurtVU k) _; simpa [HurtVU]
-- stance
abbrev ReefTouchVU (x y:Points 1): Points 2:= closedUp PermitAxisVU x y
lemma reefTouchVU (k:ℝ)(b:OS.Cross PermitAxisVU): ReefTouchVU (ManeuverVU k) (ReefMapL 0 b (ManeuverVU k))= PinsVU (-(HurtVU k)) (HurtVU k+b.val):=by
 let P:=ManeuverVU k; let X:=P 0; let Q:=ReefMapL 0 b P
 apply PiLp.ext; intro i; fin_cases i
 · change closedUp PermitAxisVU P Q (Fin.castAdd 1 (0:Fin 1))=-(HurtVU k); apply (WithLp.equiv 2 _).injective
   have hp:= enterLeftMars P Q PermitAxisVU 0
   change ΦplanR (1+1) (closedUp PermitAxisVU P Q) (Fin.castAdd 1 0) = (-(HurtVU k)).ofLp; rw[hp]; ext1 j; by_cases v:j=PermitAxisVU; subst j; simp [P,ΦplanR,ManeuverVU,PinVU,flipTactMars,HurtVU]; simp [P,ΦplanR,ManeuverVU,PinVU,flipTactMars,HurtVU, v,Ne.symm v] -- v issue
 change closedUp PermitAxisVU P Q (Fin.natAdd 1 (0:Fin 1))=HurtVU k+b.val; rw [leave]; change HurtVU k+ReefOutL 0 b= _; rw[ReefOutL]; simp
lemma mirAppendVU (x:ΧiMars): Fin.append (TurnupMars PermitAxisVU ∘ ( ![x]:Fin 1→ΧiMars)) (![x]:Fin 1→ΧiMars)= ![TurnupMars PermitAxisVU x,x]:=by
 ext1 i; fin_cases i
 · exact Fin.append_left (TurnupMars PermitAxisVU ∘ (![x]:Fin 1→ΧiMars)) (![x]:Fin 1→ΧiMars) 0 -- tune
 exact Fin.append_right (TurnupMars PermitAxisVU ∘ (![x]:Fin 1→ΧiMars)) (![x]:Fin 1→ΧiMars) 0
include cp
lemma ChargeDeepVU(k:ℝ)(hp:StallLeadMars PermitAxisVU (ManeuverVU k) P)(z:OS.Cross PermitAxisVU)(X:ΧiMars): GulfPriceL Cw R (![X]:Fin 1→ΧiMars) (![X]:Fin 1→ΧiMars) PermitAxisVU (ManeuverVU k) (ReefMapL 0 z (ManeuverVU k))= NetΛVU G (PinsVU (-(HurtVU k)) (HurtVU k+z.val)) (TurnupMars PermitAxisVU X) X:=by
 unfold NetΛVU; rw [←reefTouchVU]; rw[cp.salute]; unfold GulfPriceL; rw[mirAppendVU]; rfl -- tune
 exact WrapL hp (ReefShedsL (ManeuverVU k) hp 0 z) -- tune
include h
lemma MapTouchVU (k:ℝ)(v:0<k)(X:ΧiMars)(z:OS.Cross PermitAxisVU): let x:= HurtVU k; let b:=TurnupMars PermitAxisVU X; (DeeVK G (PinsVU (-x) (x+z.val)) b X).re ≤ (DeeVK G (PinsVU (-x) x) b X).re:=by
 intro x b; obtain ⟨p⟩:=manLightVU (P:=P) k v; have hM:0≤ MapFareL Cw R PermitAxisVU (ManeuverVU k) ![X] z 0:= by rw[mapMeshL Cw R _ _ (![X]:Fin 1 →ΧiMars) p cp.toCheckΩL]; positivity
 unfold MapFareL at hM; rw [zero_add,ChargeDeepVU Cw R G cp k p 0 X,ChargeDeepVU Cw R G cp k p z X] at hM; rw[show ((0:OS.Cross PermitAxisVU).val)=0 from rfl,add_zero] at hM
 unfold DeeVK; rw[precision_shiftVU G h (PinVU (PinsVU _ _ 0)) b,precision_shiftVU G h (PinVU (PinsVU _ _ 0)) b,precision_shiftVU G h (PinVU (PinsVU _ _ 1)) X,precision_shiftVU G h (PinVU (PinsVU _ _ 1)) X,Complex.sub_re,Complex.sub_re]
 apply sub_le_sub_right; exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by norm_num : (0:ℝ)<2)).mp hM)
#print axioms ChargeDeepVU
#print axioms MapTouchVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
