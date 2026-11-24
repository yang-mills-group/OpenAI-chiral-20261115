import GaugeFieldConstruction.ChasmLightYL
import GaugeFieldConstruction.IvoryCapVU
import GaugeFieldConstruction.VisPriceVU
import GaugeFieldConstruction.CanyonPoseVU
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
-- general ACT EU. `a` Proof no projection uniqueness for all (untouched fields), but THESE.
variable (h: P.lodestar 3 χ) (vC: CriteriaL (P.privateH χ) R)
variable (hV: CalRL (P.privateH χ) G R)
variable (hT:∀ n (F:Fin n→ΧiMars) x,ΦplanR n x∈CardsR (Fin n)→ G n x F = CoralL (P.privateH χ) R F x)
variable {x y:E4}(j:Axis)(X Y:ΧiMars)
local notation "PΨ"=> P.privateH χ
local notation "GKO"=> LightLiftL (P.privateH χ j)
noncomputable abbrev StarPinVU (j:Axis)(x:E4):= MirrorPoseL j (PinVU x)
lemma turnMirrorVU : closedUp j (StarPinVU j x) (PinVU y) = PinsVU x y:=by
 apply PiLp.ext; intro i; fin_cases i
 · change closedUp j (StarPinVU j x) (PinVU y) ((0:Fin 1).castAdd 1)=x
   -- leg: reflect (Ortho motion)
   have he:= enterLeftMars (StarPinVU j x) (PinVU y) j 0; apply (WithLp.equiv 2 _).injective; change ΦplanR 2 (closedUp j (StarPinVU j x) (PinVU y)) ((0:Fin 1).castAdd 1)=x.ofLp; rw [he,StarPinVU,flipAtL j]; ext1 v; by_cases u:v=j; subst v; rw[flipTactMars,update_self,flipTactMars,update_self,neg_neg]; rfl; rw [flipTactMars,update_of_ne u, flipTactMars, update_of_ne u]; rfl
 exact leave j (StarPinVU j x) (PinVU y) 0 -- tune
lemma PinEarthVU (x:E4)(t:0<x j): Nonempty (StallLeadMars j (PinVU x) P):=by
 apply ReefBedL; constructor; intro i j u; exact (u.ne (Subsingleton.elim i j)).elim; intro i; fin_cases i; exact t
lemma PinWestVU (x:E4)(t:x j<0): Nonempty (StallLeadMars j (StarPinVU j x) P):=by
 apply ReefBedL; refine ⟨fun _ _ p=>(p.ne (Subsingleton.elim ..)).elim,?_⟩; intro i; fin_cases i; change 0< ΦplanR 1 (StarPinVU j x) 0 j; rw[StarPinVU,flipAtL j,flipTactMars,update_self]; exact neg_pos.mpr t
variable (u0:StallLeadMars j (StarPinVU j x) P)(u1:StallLeadMars j (PinVU y) P)
noncomputable abbrev SkinnyRayVU{n:ℕ}{y:Points n} (B:StallLeadMars j y P)(A:Fin n→ΧiMars): (P.privateH χ j).DegreeHab:= RiverBoreL (P.privateH χ) R j A y B
noncomputable abbrev NorthVigVU:= SkinnyRayVU R χ j u1 (![Y]: Fin 1→ ΧiMars)
noncomputable abbrev SouthVigVU:= SkinnyRayVU R χ j u0 (TurnupMars j ∘ ( ![X]: Fin 1→ ΧiMars))
include hV hT
lemma SnowPriceVU: inner ℂ (SouthVigVU R χ j X u0) (NorthVigVU R χ j Y u1) = NetΛVU G (PinsVU x y) X Y:=by
 rw [SouthVigVU,NorthVigVU,SkinnyRayVU,SkinnyRayVU,GulfSignL _ R hV.toCheckΩL,NetΛVU,← turnMirrorVU j,hT,CoralL, GulfPriceL]; swap; · exact mem_iUnion.mpr ⟨j, WrapL u0 u1⟩
 congr 1; ext1 i; fin_cases i
 · change R (Fin.append _ _ ((0:Fin 1).castAdd 1))=_; rw [Fin.append_left]; congr 1; exact Turn2AxYL j X
 change R (Fin.append _ _ (Fin.natAdd 1 (0:Fin 1)))=_; rw [Fin.append_right]; rfl
lemma RevenueInVU: inner ℂ (SouthVigVU R χ j X u0) (PΨ j).groundHab = SoloΛVU G (PinVU x) X :=by
 -- general.PearlMir proof
 have hp:= PearlMirL (PΨ) R j (PinVU x) (![X]:Fin 1→ΧiMars) hV.toCheckΩL (Set.mem_iUnion.mpr ⟨j,fun i k _=> Subsingleton.elim ..⟩)
 have ht:inner ℂ (PΨ j).groundHab (SouthVigVU R χ j X u0)= Star.star (CoralL PΨ R (![X]:Fin 1→ ΧiMars) (PinVU x)):= (ConquerL _ R _ _ _ _ hV.toCheckΩL).trans hp
 have hU:ΦplanR _ (PinVU x) ∈ VplaneR (Fin 1) j:= fun i k h=>Subsingleton.elim ..
 unfold SoloΛVU; rw [← inner_conj_symm, ht]; have hi:= star_star (CoralL PΨ R (![X]:Fin 1→ ΧiMars) (PinVU x)); rw [show starRingEnd ℂ _ = _ from hi,hT _ _ _ (mem_iUnion.mpr ⟨j,hU⟩)] -- tune
lemma RevenueOutVU : inner ℂ (PΨ j).groundHab (NorthVigVU R χ j Y u1) = SoloΛVU G (PinVU y) Y:=by
 rw [NorthVigVU,SkinnyRayVU,ConquerL _ R _ _ _ _ hV.toCheckΩL,SoloΛVU,hT _ _ _ (mem_iUnion.mpr ⟨j,StallWestYL _ _ u1⟩)] -- tune
noncomputable abbrev ApolloVU(d:(P.privateH χ j).DegreeHab):= d-(GKO).orth d
omit hV hT
lemma starHabVU (d:(PΨ j).DegreeHab):(GKO).orth (ApolloVU χ j d)=0:=by unfold ApolloVU; rw[map_sub]; rw[show (GKO).orth ((GKO).orth d)=(GKO).orth d from ?_,sub_self]; exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
lemma AlphaAnVU(d:(PΨ j).DegreeHab): (GKO).ℚmeasure.region (FlavorSkyVU j) (ApolloVU χ j d)=ApolloVU χ j d:= zeroEnergyActVU (PΨ j) _ (starHabVU χ j d)
include hV hT h vC
lemma AlpineVU : DeeVK G (PinsVU x y) X Y= inner ℂ (ApolloVU χ j (SouthVigVU R χ j X u0)) (ApolloVU χ j (NorthVigVU R χ j Y u1)):=by
 let Φ:= (PΨ j).groundHab; let W:= SouthVigVU R χ j X u0; let Z:= NorthVigVU R χ j Y u1
 have hw:(GKO).orth W=inner ℂ Φ W • Φ:= RankEstHereL j χ h _ (fun b=> StallRidsYL _ R j _ _ u0 vC b)
 have he:(GKO).orth Z=inner ℂ Φ Z • Φ:= RankEstHereL j χ h _ (fun b=> StallRidsYL _ R j _ _ u1 vC b)
 change NetΛVU _ _ _ _-SoloΛVU _ (PinVU x) X*SoloΛVU _ (PinVU y) Y=inner ℂ (W- (GKO).orth W) (Z- (GKO).orth Z); rw[←SnowPriceVU R G χ hV hT j X Y u0 u1,←RevenueInVU R G χ hV hT j X u0,←RevenueOutVU R G χ hV hT j Y u1,hw,he,inner_sub_left,inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_left,inner_smul_left,inner_smul_right,inner_conj_symm,inner_self_eq_norm_sq_to_K,show ‖Φ‖=1 from (PΨ j).normΩ]; change inner ℂ W Z-inner ℂ W Φ*inner ℂ Φ Z= _; simp; ring
#print axioms AlpineVU
#print axioms AlphaAnVU
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
