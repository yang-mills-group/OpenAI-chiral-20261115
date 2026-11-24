import GaugeFieldConstruction.OrchardFastYL
import GaugeFieldConstruction.EldStarVUV
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
-- REGIONAL positive spectral on orthogonal subspace. `lamp_fixed` known.F. Proof before boost.
abbrev FlavorSkyVU (j:Axis):Set E4:= {x|0<x j}
local notation "Γm" => LightLiftL C
lemma flameEUVU (x:C.DegreeHab)(hp:(Γm).ℚmeasure.region (FlavorSkyVU j)ᶜ x=x): x∈ (Γm).ground:=by
 let T:= Γm; let μ:=T.ℚmeasure; have m:IsOpen (FlavorSkyVU j):= isOpen_lt continuous_const (PiLp.continuous_apply 2 _ _)
 have hv:μ.diagonal x (FlavorSkyVU j)=0:=by
    apply (μ.null_pair m.measurableSet x).2
    conv_lhs => arg 2; rw [← hp]
    change μ.region _ (μ.region _ _)=_; rw [←ContinuousLinearMap.comp_apply, μ.joins m.measurableSet m.measurableSet.compl, inter_compl_self,μ.none]; rfl
 have hb:∀ᵐ y∂μ.diagonal x, y j=0:=by
    filter_upwards [T.bright x, show ∀ᵐ y∂ μ.diagonal x,¬ 0<y j by rw[ae_iff]; simpa only [Classical.not_not] using hv] with i u p; exact le_antisymm (le_of_not_gt p) u
 apply (T.fixed _).2; exact (SelectionAnalysis.lamp_fixed C.BrightHab x).1 fun s=>by
    have he: T.unit.translation (s • basis j) x=x:=by
       let q:= s • basis j
       have hc: inner ℂ x (T.unit.translation q x)=inner ℂ x x:=by
          rw [← T.joint,show inner ℂ x x= charFun (μ.diagonal x) 0 from ?_,charFun_apply,charFun_apply]; refine integral_congr_ae (hb.mono fun i e=>?_); have hi: inner ℝ i q=0:= by rw[real_inner_comm]; unfold q; rw[real_inner_smul_left,YM.basis_inner,e,mul_zero]; -- tune
          dsimp only; rw[hi,inner_zero_right]; -- tune
          rw [show charFun (μ.diagonal x) (0:E4)= inner ℂ x (T.unit.translation 0 x) from T.joint x _,T.unit.origin]; rfl
       have hh:inner ℂ (T.unit.translation q x) x=inner ℂ x x:=(inner_conj_symm _ x).symm.trans ((congrArg (starRingEnd ℂ) hc).trans (inner_conj_symm ..))
       change T.unit.translation q x=x; apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw[inner_sub_left,inner_sub_right,inner_sub_right,hc,hh]; rw[inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K, T.unit.unitary]; ring
    have hZ:NSF.OS.Semigroup.SEP j (s • basis j)=0:= Subtype.ext (show s • basis j-_=_ by simp)
    change T.edge ((s • basis j) j) (T.U _ x)=_ at he; rw [hZ, show (s • basis j : E4) j=s from (by simp),T.uZero,ContinuousLinearMap.id_apply] at he; exact he
lemma zeroEnergyActVU (x:C.DegreeHab)(p:(Γm).orth x=0): (Γm).ℚmeasure.region (FlavorSkyVU j) x=x:=by
 let T:= Γm; let μ:=T.ℚmeasure; let X:=FlavorSkyVU j; have h:IsOpen X:= isOpen_lt continuous_const (PiLp.continuous_apply 2 _ _); have m:=h.measurableSet.compl; let y:=μ.region Xᶜ x
 have hz: y∈ T.ground:= flameEUVU C _ (μ.idempotent m _)
 have ht:Tendsto (fun t=> inner ℂ (T.E t x) y) atTop (𝓝 0):= show _ from (inner_zero_left (𝕜:=ℂ) y) ▸ (((p ▸ (show Tendsto (fun t=>T.E t x) atTop (𝓝 (T.orth x)) from T.emerges x)): Tendsto (fun t=> T.E t x) atTop (𝓝 0)).inner (tendsto_const_nhds (x:=y))) -- tune
 have hp:inner ℂ x y=0:= tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds ht (Eventually.of_forall (fun i=> Eq.symm (by dsimp only; rw [T.swing,(T.fixed y).1 hz i]))) -- tune
 have hv:inner ℂ y y=0:=by
    change inner ℂ (μ.region Xᶜ _) y=0
    conv_lhs=> arg 2; arg 1; rw[← μ.real m]
    rw [ContinuousLinearMap.adjoint_inner_left,show μ.region Xᶜ y=y from μ.idempotent m _]; exact hp
 simpa only [compl_compl] using PasLeavesVU μ m x (show μ.region Xᶜ x=0 from inner_self_eq_zero.mp hv)
#print axioms zeroEnergyActVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
