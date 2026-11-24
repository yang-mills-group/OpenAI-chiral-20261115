import GaugeFieldConstruction.BrambleEarthL
import GaugeFieldConstruction.RadGuardL
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
-- Estimate independent C χ for any one fixed-pad choice. Enables Fubini/L2 (137), L3.
lemma costVignL (z:Axis→ℝ)(k:P.Slabs j)(w:C.DegreeHab): ‖StampActMars C z k w‖ ≤ ‖k‖*‖w‖:=by
 let A:= C.BrightHab; change ‖A.U (diameter z) ((LadderRackMars C k) (A.U _ w))‖ ≤ _; rw [A.unitary]; apply le_trans ((LadderRackMars ..).le_opNorm _); rw [A.unitary]; gcongr; exact liftRackL C k
lemma costBillL {I:Type}[Fintype I][DecidableEq I] (V:I→ P.Slabs j)(K:I→ PermWallJ P)(T:List I)(x:I→ Axis→ℝ)(b: Option ℝ): ‖ActorMars C.BrightHab C.groundHab b (billActMars C K V x T)‖ ≤ (T.map fun i=> ‖V i‖).prod:=by
 induction T generalizing b with
 | nil=> exact C.normΩ.le
 | cons i L ih=>
    unfold billActMars; rw [List.map_cons,ActorMars]; let A:= C.BrightHab
    refine (ContinuousLinearMap.le_opNorm _ _|>.trans (mul_le_of_le_one_left (norm_nonneg _) (A.shrinks _))).trans ((costVignL C (x i) (V i) _).trans ?_); exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)
noncomputable def HoldThreshL (a:Axis)(S:Fin n→ScreensJ P)(p:Points n)(J:StallLeadMars a p P):= (J.L.map (fun i=> ‖(S i) a (J.σ i) (J.σ i)‖)).prod
lemma riverFareL: ‖RiverBoreL Cw R a F p J‖ ≤ HoldThreshL a (R ∘ F) p J:= costBillL (Cw a) _ _ _ _ _
-- analysis on χ. All agreements for ANY X. Norm independent of axis only need strict. aim extends charges later.
variable (x: P.Spectrum0 3)(U:CheckΩL R)
local notation "κx" x:max=> P.privateH x
local notation "ΤP"=> P.publicH
local notation "Ψ" Φ:max a:max=> LightLiftL (Φ a)
local notation "Αx"=>P.Spectrum0 3
local notation "μX"=>P.pillars 3
noncomputable def BerryEarthL (p:ℝ≥0)(z:OS.Cross a){n m:ℕ}(F:Fin n→ ΧiMars)(G:Fin m→ ΧiMars)(k:Points n)(y:Points m)(eχ:P.Spectrum0 3):= GulfPriceL (P.privateH eχ) R F G a k (ReefMapL p z y)
include U
lemma metersL (q:ℝ≥0)(z:OS.Cross a){n m:ℕ}(F:Fin n→ ΧiMars)(A:Fin m→ΧiMars)(k:Points n)(y: Points m)(L:StallLeadMars a k P)(V:StallLeadMars a y P):
 ‖BerryEarthL R a q z F A k y x‖≤ HoldThreshL a (R ∘ F) k L * HoldThreshL a (R ∘ A) y V:=by -- `a` notation macro Berry local? verify
 unfold BerryEarthL; rw [←ReefRealL _ R U F A a _ y L V]
 apply (norm_inner_le_norm ..).trans; let E:= HoldThreshL a (R∘ F) k L; let δ:=Ψ (κx x) a
 let f:= RiverBoreL (κx x) R a F k L; let g:= RiverBoreL (κx x) R a A y V
 have h:‖δ.E q (δ.U z g)‖≤‖g‖:= by refine le_trans ((δ.E q).le_opNorm _ |>.trans (mul_le_of_le_one_left (norm_nonneg _) (δ.shrinks _))) ?_; rw[δ.unitary]
 exact mul_le_mul (riverFareL _ _ a _ _ L) (h.trans (riverFareL (κx x) _ _ _ _ V)) (norm_nonneg _) (le_trans (norm_nonneg f) (riverFareL ..)) -- tune
lemma bergLikeL (q:ℝ≥0)(z:OS.Cross a){n m:ℕ}(F:Fin n→ ΧiMars)(A:Fin m→ΧiMars)(k:Points n)(y: Points m)(L:StallLeadMars a k P)(V:StallLeadMars a y P):
 Integrable (BerryEarthL R a q z F A k y) μX∧ (∫ x,BerryEarthL R a q z F A k y x ∂μX)= GulfPriceL (ΤP) R F A a k (ReefMapL q z y):=by
 let J:=R ∘ Fin.append (TurnupMars a∘ F) A; let v:= ΦplanR (n+m) (NSF.Table.Pairing.closedUp a k (ReefMapL q z y))
 have he:= BronteR J (fun i=> U.showL _) v
 refine ⟨?_,he.2.symm⟩
 exact (integrable_const (μ:=P.pillars 3) (HoldThreshL a (R∘F) k L*HoldThreshL a (R∘A) y V)).mono' he.1.aestronglyMeasurable (Eventually.of_forall (fun x=> metersL R a x U q z F A k y L V))
local notation "νL" x:max z:max q:max=> MapFareL (κx x) R a p F z q
include J
lemma BergRollL(q:ℝ≥0)(z:OS.Cross a): Integrable (fun x=>νL x z q) μX ∧ (∫ x,νL x z q ∂μX)=MapFareL (ΤP) R a p F z q:=by
 let V(z): Αx → ℂ:= BerryEarthL R a (q+q) z F F p p
 obtain ⟨u,e⟩:=bergLikeL R a U (q+q) 0 F F p p J J -- positional tune
 obtain ⟨w,g⟩:=bergLikeL R a U (q+q) z F F p p J J
 refine ⟨(u.re.sub w.re).const_mul 2,?_⟩
 change (∫ x,2*(RCLike.re (V 0 x)-RCLike.re (V z x))∂μX)=_
 rw[integral_const_mul, integral_sub u.re w.re,integral_re u,integral_re w,g,e]; rfl -- tune direction/names
lemma BergCapL(q:ℝ≥0)(z:OS.Cross a): let k:=HoldThreshL a (R ∘ F) p J; ∀ x:Αx,|νL x z q| ≤ (k+k)^2:=by
 dsimp only; intro x
 rw [mapMeshL _ _ _ _ _ J U,abs_of_nonneg (sq_nonneg _)] -- tune x notation
 let v:= RiverBoreL (κx x) R a F p J; let E:=Ψ (κx x) a; let k:=HoldThreshL a (R ∘ F) p J
 have hu: ‖E.E q v‖ ≤ k:= ((E.E q).le_opNorm _|>.trans (mul_le_of_le_one_left (norm_nonneg _) (E.shrinks _))).trans (riverFareL ..)
 refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) _; exact add_le_add hu ((E.unitary z _).le.trans hu)
#print axioms BergCapL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
