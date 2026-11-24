import GaugeFieldConstruction.CairnAngleL
import Mathlib.MeasureTheory.Function.L2Space
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
-- (137)-->(138) variant: projection joint on actual POS. norm displacement criterion; everything commutes on same Hil. use E2 costs, no invocation of L1 for chosen x until after L3!
variable (a:Axis)(p: Points n)(v:eastL n a p)(F:Fin n→ ΧiMars)(J:StallLeadMars a p P)
variable (χ:P.Spectrum0 3)(U:CheckΩL R)
open Set Complex
variable (J0: SunlitL P.publicH R G)(f: SurfCheckL.boisterL t G)
variable (E:∀ᵐ x∂P.pillars 3,P.lodestar 3 x) (Z:∀ᵐ x∂P.pillars 3, CriteriaL (P.privateH x) R)
open PlaneL
abbrev BasinL (a:Axis)(n:ℕ):=(Fin n→ ΧiMars) × MettleL a n
noncomputable abbrev ConchL {a:Axis}(X:BasinL a n) (x:P.Spectrum0 3):= pearlL R x X.1 X.2.val
noncomputable abbrev DiveL {g:SO}{a b:Axis}(u:suitAxL g a b)(X:BasinL a n): BasinL b n:= (compassPiMars t g ∘ X.1,⟨motionMoonMars g X.2.val,DeltaEastL _ _ X.2.property u⟩)
lemma suitTimesL {s g:SO} {a b c: Axis}(p:suitAxL s b c)(t:suitAxL g a b):suitAxL (s*g) a c:=fun x=> (congrArg (fun v:E4=>v c) (Ortho.move_mul s.val g.val x)).trans ((p _).trans (t x))
lemma DiveMulL {s g:SO}{a b c:Axis}(p:suitAxL s b c)(v:suitAxL g a b)(X:BasinL a n): DiveL t (suitTimesL p v) X=DiveL t p (DiveL t v X):= Prod.ext (funext fun i=>sailMulMars t _ _ _) (Subtype.ext (WindyMissionMars _ _ _))
lemma DiveOneL {a:Axis}(X:BasinL a n)(p:suitAxL 1 a a): DiveL t p X=X:= Prod.ext (funext fun i=>sailOneMars t _) (Subtype.ext (calend_oneMars _))
lemma DiveCongL {s g:SO}{a b:Axis}(p:suitAxL s a b)(v:suitAxL g a b)(e:s=g)(X:BasinL a n):DiveL t p X=DiveL t v X:=by subst g; rfl
local notation "μL"=> P.pillars 3
include U
lemma ConchL_mem {a:Axis}(X:BasinL a n): MemLp (ConchL R X) 2 μL:=by
 let h:= joyEarthL R a X.2.val X.1 (CanSwimL a P X.2) U
 exact memLp_two_iff_integrable_sq_norm h.2.aestronglyMeasurable|>.2 h.1
noncomputable abbrev LagoonL {a:Axis}(X:BasinL a n) : MeasureTheory.Lp ℂ 2 μL:=(ConchL_mem R U X).toLp _
lemma AleConchL {a b:Axis}(X:BasinL a n)(Y:BasinL b n): LagoonL R U X= LagoonL R U Y ↔ ConchL R X=ᵐ[μL] ConchL R Y:= MemLp.toLp_eq_toLp_iff ..
lemma LagoonG_L {m:ℕ}{a:Axis}(X:BasinL a n)(Y:BasinL a m): inner ℂ (LagoonL R U X) (LagoonL R U Y)= ∫ x, (Star.star (ConchL R X x)) * ConchL R Y x∂μL:=by
 rw [L2.inner_def]; apply integral_congr_ae
 filter_upwards [(ConchL_mem R U X).coeFn_toLp, (ConchL_mem R U Y).coeFn_toLp] with x h p; rw [show LagoonL R U X x=_ from h, show LagoonL R U Y x=_ from p]; change ConchL R Y x * _=_; exact mul_comm ..
lemma LagoonH_L {i k a:Axis}(p:suitAxL (QκL i k) a a)(X:BasinL a n): LagoonL R U (DiveL t p X)=LagoonL R U X:=
 (AleConchL R U _ _).mpr (Eventually.of_forall fun b=> CoralHalfL (P.privateH b) R t X.2.val X.1 U i k (westBlueL a X.2.2.1.injective))
include Z E f J0
lemma L_PowerL {m:ℕ}{a b:Axis}{g:SO}(p:suitAxL g a b)(X:BasinL a n)(Y:BasinL a m) : inner ℂ (LagoonL R U X) (LagoonL R U Y)= inner ℂ (LagoonL R U (DiveL t p X)) (LagoonL R U (DiveL t p Y)):=by
 let T:= DiveL t p X; let W:=DiveL t p Y; rw [LagoonG_L,LagoonG_L]
 refine tendsto_nhds_unique_of_eventuallyEq (juiceEarthL R a U E Z X.1 Y.1 X.2 Y.2) (juiceEarthL R b U E Z T.1 W.1 T.2 W.2) (Eventually.of_forall fun i=>?_)
 let D:= CanSwimL a P X.2; let V:=CanSwimL a P Y.2; let q:ℝ≥0:=i; have he:= OroLineL P.publicH R G t J0 f D (ReefShedsL Y.2.val V q 0) p X.1 Y.1
 rw [DistantL p,Pliss0L] at he; exact he
lemma LagoonI_L {a b:Axis}{g:SO}(p:suitAxL g a b)(X Y:BasinL a n)(u':LagoonL R U X= LagoonL R U Y): LagoonL R U (DiveL t p X)= LagoonL R U (DiveL t p Y):=by
 apply sub_eq_zero.mp; apply inner_self_eq_zero (𝕜:=ℂ)|>.1
 rw [inner_sub_left,inner_sub_right,inner_sub_right,←L_PowerL R G t U J0 f E Z p,←L_PowerL R G t U J0 f E Z p,←L_PowerL R G t U J0 f E Z p,←L_PowerL R G t U J0 f E Z p,u',sub_self] -- tune
omit U Z E f J0
lemma hemSuitL {a i k:Axis}(u:a≠i)(v:a≠k):suitAxL (QκL i k) a a:=by intro x; change Ortho.move _ x a=_; rw [hemiKeyL,Ortho.move_mul,Signed.mirrored, Signed.mirrored]; split_ifs <;> simp_all [Jj] -- rw
lemma AxisKeyL {a i k:Axis}(h:i≠k)(u:a≠i)(v:a≠k)(r:ℝ):suitAxL (PlaneL.Ψ i k r) a a:=fun x=> (YM.Work.A13.plane_givens h x r).2.2 a u v
lemma moreKeyL (a i j:Axis):∃ k:Axis,k≠i ∧ k≠j∧ a≠k:=by
 have e:( {a,i,j} : Finset Axis )≠ Finset.univ:=by
    intro w; have h :(Finset.univ:Finset Axis).card ≤3:=by rw [←w]; exact le_trans (card_insert_le ..) (by have hp:= Finset.card_insert_le i ({j} : Finset Axis); simp only[Finset.card_singleton] at hp; omega)
    rw [show (Finset.univ:Finset Axis).card=4 from by simp [Axis]] at h; omega
 have hw: ((↑({a,i,j} :Finset Axis)): Set Axis) ≠ Set.univ:=fun h=> e (Finset.coe_injective (h.trans (Finset.coe_univ).symm))
 obtain ⟨k,h⟩:= (Set.ne_univ_iff_exists_notMem _).mp hw
 simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton,not_or] at h; exact ⟨k,h.2.1,h.2.2,Ne.symm h.1⟩
include U J0 f E Z
lemma residuallightL {a i j:Axis}(h:i≠j)(u:a≠i)(v:a≠j)(s:ℝ)(X: BasinL a n): LagoonL R U (DiveL t (AxisKeyL h u v (-s)) X)=LagoonL R U (DiveL t (AxisKeyL h u v s) X):=by
 obtain ⟨k,hp,hq,hv⟩:= moreKeyL a i j; have F:= hemSuitL u hv; have H:= suitTimesL F (suitTimesL (AxisKeyL h u v s) F)
 rw [←DiveCongL t H (AxisKeyL h u v (-s)) (doorSphereL h hp hq s), DiveMulL t F (suitTimesL (AxisKeyL h u v s) F),DiveMulL t (AxisKeyL h u v s) F,LagoonH_L]
 exact LagoonI_L R G t U J0 f E Z _ _ _ (LagoonH_L R t U _ _)
lemma MuseL {a i j:Axis}(h:i≠j)(u:a≠i)(v:a≠j)(s:ℝ)(X:BasinL a n): ConchL R X=ᵐ[μL] ConchL R (DiveL t (AxisKeyL h u v s) X):=by
 let r:=s/2; have H:= AxisKeyL h u v r; have H':=AxisKeyL h u v (-r); have p:= residuallightL R G t U J0 f E Z h u v r (DiveL t H X)
 have g: PlaneL.Ψ i j (-r) * PlaneL.Ψ i j r =1:=by rw[dreamSphereL,neg_add_cancel,basicSphereL]
 have u': suitAxL 1 a a:=fun x=> congrArg (fun y:E4=> y a) (Ortho.move_one x)
 rw [←DiveMulL t H' H, ←DiveMulL t H H,DiveCongL t (suitTimesL H' H) u' g,DiveOneL t _ u',DiveCongL t (suitTimesL H H) (AxisKeyL h u v s) (by rw [dreamSphereL]; unfold r; rw[show s/2+s/2=s from by ring])] at p
 exact (AleConchL ..).mp p
#print axioms MuseL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
