import GaugeFieldConstruction.AllShoresVU
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
variable (x y:E4) (v:x PermitAxisVU < y PermitAxisVU)
abbrev EnvelopeVU := (y PermitAxisVU-x PermitAxisVU)/2
include v in
lemma SealPosVU : 0<EnvelopeVU x y:=div_pos (sub_pos.mpr v) zero_lt_two
noncomputable def RiverExtVU : OS.Cross PermitAxisVU:=⟨(y-x)-2 • HurtVU (EnvelopeVU x y),by
   change ((y-x)-(2:ℕ) • _) _=0; rw [two_nsmul]; simp [HurtVU,EnvelopeVU]⟩ -- tune nsmul
noncomputable def BaseMoVU := let a:=HurtVU (EnvelopeVU x y); PinsVU (-a) (a+(RiverExtVU x y).val)
noncomputable def AquaVU (k:ℝ):= PinsVU (-(HurtVU k)) (HurtVU k)
include v in
lemma baseColdVU: BaseMoVU x y∈conf 2:=by
 let d:= PermitAxisVU; let t:=EnvelopeVU x y; have hp:=SealPosVU x y v
 have h:PinsVU (-(HurtVU t)) (HurtVU t+(RiverExtVU x y).val) 0 d < (BaseMoVU x y) 1 d:=by
    change (-(HurtVU t)) d< (HurtVU t+(RiverExtVU x y).val) d; rw [PiLp.add_apply,show (RiverExtVU x y).val d=0 from (RiverExtVU ..).property]; simp [d,HurtVU,t] <;> linarith -- tune
 have hv:BaseMoVU x y 0≠BaseMoVU x y 1:= fun p=> h.ne (congrArg (fun Z:E4=>Z d) p)
 intro i j k; fin_cases i <;> fin_cases j<;> first|rfl|exact (hv k).elim|exact (hv k.symm).elim
lemma bendVU:NSF.Points.across (x+ HurtVU (EnvelopeVU x y)) (BaseMoVU x y)= PinsVU x y:=by
 apply PiLp.ext; intro i; let a:= HurtVU (EnvelopeVU x y)
 fin_cases i; change -a+(x+a)=x; abel
 change (a+((y-x)-2 • a))+(x+a)= y; abel
include v cp h
lemma BaseMarksVU (M:ClanZN→ΧiMars)(δ:ℝ)(k:XPriceVU G (TurnupMars PermitAxisVU ∘ M) M (PinsVU x y)∈PrecisionYN δ): XPriceVU G (TurnupMars PermitAxisVU ∘ M) M (AquaVU (EnvelopeVU x y))∈ PrecisionYN δ:=by
 intro z p; have hp:=k z p; rw [PayTrueVU, ← bendVU,benefit_shiftVU G h _ (baseColdVU x y v)] at hp; rw [PayTrueVU]; exact hp.trans_le (MapTouchVU Cw R G cp h _ (SealPosVU x y v) _ (RiverExtVU x y))
#print axioms BaseMarksVU
omit v cp h
-- proper signed rotate AFTER. σ from sw. time→physical0 positive.
abbrev TerrainVU:= Stage.Count.sw 0 PermitAxisVU -- reversed, maps τ→0 with wanted sign
lemma PermitLShiftVU: signBit TerrainVU=false:= Stage.Count.sw_pos ..
noncomputable abbrev PearlShapeVU:= Stage.signMot TerrainVU PermitLShiftVU
lemma BindShipVU:suitAxL PearlShapeVU PermitAxisVU 0:=by
 intro x; change (Signed.ortho TerrainVU).move x _ = _; rw [Signed.ortho_move]
 simp [Signed.act,show TerrainVU.perm.symm 0= PermitAxisVU by decide,show TerrainVU.flip PermitAxisVU=false by decide] -- tune
noncomputable abbrev RhoExtVU(k:ℝ):= k • basis (0:Axis)
lemma bendHueVU(k:ℝ): motionMoonMars PearlShapeVU (AquaVU k)=PinsVU (-(RhoExtVU k)) (RhoExtVU k) :=by
 have hp:=suitsPoleL BindShipVU; have he:PearlShapeVU.val.motion (HurtVU k)=RhoExtVU k:=by rw[HurtVU,LinearIsometryEquiv.map_smul, hp]
 apply PiLp.ext; intro i; fin_cases i; change PearlShapeVU.val.motion (-_) = -_; rw [map_neg]; exact congrArg _ he; exact he
lemma PillarsColdVU(k:ℝ)(h:0<k): AquaVU k∈ conf 2:=by
 let d:=PermitAxisVU; have hp: (AquaVU k) 0 d< (AquaVU k) 1 d:=by change (-(HurtVU k)) d< HurtVU k d; simp [d,HurtVU] <;> linarith
 have hv:AquaVU k 0≠AquaVU k 1:= fun p=> hp.ne (congrArg (fun Z:E4=> Z d) p)
 intro i j p; fin_cases i <;> fin_cases j<;> first|rfl|exact (hv p).elim|exact (hv p.symm).elim
noncomputable abbrev ZodiacVU(k:ℝ):= PinsVU (-(RhoExtVU k)) (RhoExtVU k)
lemma zodiacColdVU(k:ℝ)(h:0<k): ZodiacVU k∈conf 2:= by rw [ZodiacVU,←bendHueVU]; exact NSF.Points.move_in PearlShapeVU.val (PillarsColdVU k h)
lemma timeZodVU(k:ℝ): readings (ZodiacVU k)=0:=by ext1 i; fin_cases i <;> simp [RhoExtVU,ZodiacVU,PinsVU,readings,time, show timeAxis ≠(0:Axis) by decide,Ne.symm (show timeAxis ≠(0:Axis) by decide)] -- tune time ambiguity
lemma zodiacSpVU(k:ℝ)(h:0<k): ZodiacVU k ∈ Gate2VU.gap:=by
 let x:=ZodiacVU k; change x 1 - x 0∈ Mink.spacelike; let t:=x 1-x 0
 have h0(i:Fin 2): YM.time (x i)=0:= congr_fun (timeZodVU k) i
 have hv : YM.time t=0:=by simp only [t,sub_eq_add_neg,Mink.clock_add,Mink.clock_neg,h0]; simp
 have hg:t≠0:= sub_ne_zero.mpr (Injective.ne (zodiacColdVU k h) (by decide))
 rw [Mink.lateral]; change |time t|<‖YM.spatial t‖; rw [hv,abs_zero,norm_pos_iff]; intro u; apply hg; exact Mink.ext_by u hv -- tune
variable (w:SurfCheckL.boisterL t G)
include w
lemma ZodiacPoseVU(k:ℝ)(a:0<k) (X Y:ClanZN→ΧiMars): XPriceVU G (spinFrame four TerrainVU ∘ X) (spinFrame four TerrainVU ∘ Y) (ZodiacVU k)= XPriceVU G X Y (AquaVU k):=by
 ext1 i; ext1 j; have hp:= TimeProfitVU G w _ (PillarsColdVU k a) (X i) (Y j) PearlShapeVU; rw [bendHueVU, show PearlShapeVU=Stage.signMot TerrainVU PermitLShiftVU from rfl, PiProperMoon,PiProperMoon] at hp; exact hp
#print axioms ZodiacPoseVU
#print axioms zodiacSpVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
