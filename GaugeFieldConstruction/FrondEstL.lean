import GaugeFieldConstruction.NixEstL
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
open TopologicalSpace Set
abbrev MettleL (a:Axis)(n:ℕ):= {x:Points n//eastL n a x}
noncomputable def CanSwimL (P:Spine)(q:MettleL a n):StallLeadMars a q.val P:= Classical.choice (ReefBedL _ q.2)
noncomputable def RideBoatL (x:MettleL a n):= RiverBoreL Cw R a F x.val (CanSwimL a P x) -- order tune
private theorem pioneerL {I:Type*}[TopologicalSpace I]{J:Hilbert}(c:I→J)(g:I×I →ℂ)(hp:Continuous g)(h:∀ i j,inner ℂ (c i) (c j)=g (i,j)):Continuous c:=by
 apply continuous_iff_continuousAt.mpr; intro x; apply Metric.tendsto_nhds.mpr; intro ε he
 have hh:Tendsto (fun y=>dist (c y) (c x)^2) (𝓝 x) (𝓝 0):=by
    let f:I→ℝ:= fun q=> (g (q,q)).re+(g (x,x)).re-2*(g (q,x)).re
    have ho(y): dist (c y) (c x)^2=f y:=by
       have hm(v): (inner ℂ (c v) (c v)).re=‖c v‖^2:= inner_self_eq_norm_sq (𝕜:=ℂ) _
       unfold f; rw [←h,←h,←h, dist_eq_norm, norm_sub_sq (𝕜:=ℂ), hm,hm]; change ‖c y‖^2-2*(inner ℂ (c y) (c x)).re+‖c x‖^2=_; ring
    have hu:= (show Continuous f by unfold f; fun_prop).tendsto x
    simp_rw [ho]; rw [←show f x=0 from ((ho x).symm.trans (by simp))]; exact hu
 exact (hh.eventually (gt_mem_nhds (pow_pos he 2))).mono fun i e=> (sq_lt_sq₀ dist_nonneg he.le).1 e
include U
lemma entranceL : Continuous (RideBoatL Cw R a F) :=by
 let X:= R ∘ (Fin.append (TurnupMars a ∘ F) F); let c:=RideBoatL Cw R a F
 let d(y z:MettleL a n):=ΦplanR _ (NSF.Table.Pairing.closedUp a y.val z.val); let g:= SπR Cw X
 have hp(y z): inner ℂ (c y) (c z)=g (d y z):= GulfSignL Cw R U F F a _ _ (CanSwimL a P y) (CanSwimL a P z) -- tune e
 have hv(y z): d y z∈ CardsR _:= Set.mem_iUnion.mpr ⟨_,WrapL (CanSwimL a P y) (CanSwimL a P z)⟩
 have hq:Continuous (uncurry d):=by

    exact (ΦlegR (n+n)).comp ((NSF.Table.Pairing.pairIso (n:=n) (m:=n) a).symm.continuous.comp (continuous_subtype_val.prodMap continuous_subtype_val)) -- tune
 have hu: Continuous (fun p:MettleL a n × MettleL a n=> g (d p.1 p.2)):= continuous_iff_continuousAt.2 (fun p=> (((groundPlotR Cw X (fun i=>U.showL _) _ (hv p.1 p.2)).continuousAt ((prosc_R _).mem_nhds (hv p.1 p.2))).comp (f:=uncurry d) (hq.continuousAt))) -- defeq d
 exact pioneerL (J:=(Cw a).DegreeHab) c _ hu hp
omit U
lemma atmStampL (K:PermWallJ P)(x:Axis→ℝ):Continuous (fun t:grainMars=>StampActMars C x (R (FreightMars.symm t) j K K)):=by
 let L:grainMars→ₗ[ℂ] C.DegreeHab.Op:={
  toFun:=fun t=>StampActMars C x (R (FreightMars.symm t) j K K)
  map_add' t s:=by simp [StampActMars, LadderRackMars,mul_add, add_mul]
  map_smul' c t:=by simp [StampActMars,LadderRackMars] }
 exact L.continuous_of_finiteDimensional
lemma usageBoatL (x:MettleL a n): Continuous (fun v:Fin n → grainMars=> RideBoatL Cw R a (FreightMars.symm ∘ v) x):=by
 let σ:= (CanSwimL a P x).σ; let F(u:Fin n → grainMars):=R ∘ FreightMars.symm ∘ u; let C':=Cw a
 let T (u):= BodyΘ P (fun i=>F u i) a σ; let p:= ΦplanR n x.val
 suffices h:∀ (L:List (Fin n))(b:Option ℝ), Continuous (fun v=> ActorMars C'.BrightHab C'.groundHab b (billActMars C' σ (T v) p L)) from h ..
 intro L; induction L with
 | nil=> exact fun _=> continuous_const
 | cons i L ih=>
    intro b; unfold billActMars; simp_rw [List.map_cons,ActorMars]
    exact (ContinuousLinearMap.continuous _).comp (((atmStampL C' R (σ i) (p i)).comp (continuous_apply i)).clm_apply (ih (some (p i a+ StallJ P (σ i))))) -- clm function
abbrev CriteriaL (C:∀ j:Axis,Porch P cost j)(R:ΧiMars→ₗ[ℂ]ScreensJ P) :Prop:=∀ (n:ℕ)(a:Axis)(p: Points n)(J:StallLeadMars a p P), eastL n a p→∀ (F:Fin n→ΧiMars)(z:OS.Cross a),(LightLiftL (C a)).U z ((LightLiftL (C a)).orth (RiverBoreL C R a F p J))=(LightLiftL (C a)).orth (RiverBoreL C R a F p J)
private theorem upL {X Y:Type*}[TopologicalSpace X][TopologicalSpace Y][T2Space Y][SeparableSpace X]{I:Type}{K:Filter I}[CountableInterFilter K] (v w:I→X→Y)(hv:∀ i,Continuous (v i))(hw:∀ i,Continuous (w i))(h:∀ x,∀ᶠ i in K,v i x=w i x):∀ᶠ i in K,∀ x,v i x=w i x:=by
 cases isEmpty_or_nonempty X with
 | inl p=>exact Eventually.of_forall fun _ x=> isEmptyElim x
 | inr u=>
    filter_upwards [eventually_countable_forall.mpr (fun i:ℕ=> h (denseSeq X i))] with i p'; exact congr_fun ((denseRange_denseSeq X).equalizer (hv i) (hw i) (funext p'))
-- use simpler scalar discrepancy ℝ
variable (L0:SunlitL P.publicH R G)(f: SurfCheckL.boisterL t G)
variable (A:AllocatedL P)(D:SurfCheckL G){Z:NSF.Boundary.Waves (SurfRimL G)}{W:NSF.Boundary.Surface (SurfRimL G)}{S': Spins (SurfRimL G)}
variable (g:LoreL Z S' W (SurfRimL G))(c: (SurfRimL G).RealSpin)
local notation "ζ" x:max=>P.privateH x
local notation "κx" x:max a:max=>LightLiftL ((ζ x) a)
local notation "μL"=> P.pillars 3
include L0 f A D g c
lemma flowsFullL : ∀ᵐ x∂μL, CriteriaL (ζ x) R:=by
 let U:= L0.toCheckΩL
 apply ae_all_iff.mpr; intro n; -- goal reduce
 apply ae_all_iff.mpr; intro a
 let y(x:P.Spectrum0 3)(F:Fin n → grainMars)(k:MettleL a n):= (κx x a).orth (RideBoatL (ζ x) R a (FreightMars.symm∘ F) k)
 let M(x)(F:Fin n → grainMars)(k:MettleL a n)(z:NSF.OS.Cross a):= dist ((κx x a).U z (y x F k)) (y x F k)
 have he:∀ᵐ x∂μL,∀ (F:Fin n → grainMars) (k:MettleL a n)(z:NSF.OS.Cross a), M x F k z=0:=by -- successive ae via dense F, k sets. upL swaps one needing ∀ rest; iterate using dependent function Continuous via continuous_pi
    let T:= M
    have hm: ∀ F,∀ᵐ x∂μL,∀ k z, M x F k z=0:=by
        intro F
        have hp:∀ (k:MettleL a n),∀ᵐ x∂μL,∀ z:NSF.OS.Cross a, M x F k z=0:=by
           intro k
           refine upL (K:=ae (P.pillars 3)) (fun x=> M x F k) (fun _ _=>0) (fun x=> ((κx x a).continuousU _).dist continuous_const) (fun _=>continuous_const) ?_
           intro z; filter_upwards [Z_RiverL R a k.val (FreightMars.symm ∘ F) (CanSwimL a P k) U z (argentL P.publicH R G t a _ k.2 _ (CanSwimL a P k) L0 f A D g c z)] with x t; exact dist_eq_zero.2 t
        refine (upL (fun x k=> M x F k) (fun _ _ _=>0) ?_ (fun _=>continuous_const) (fun k=>(hp k).mono (fun _ z=>funext z))).mono fun i z k=> congr_fun (z k)
        intro x; apply continuous_pi; intro z; let E:=(κx x a)
        have hw:=E.orth.continuous.comp (entranceL (ζ x) R a (FreightMars.symm ∘ F) U)
        exact (((E.U z).continuous.comp hw).dist hw)
    refine (upL M (fun _ _ _ _=>0) ?_ (fun _=>continuous_const) (fun i=> (hm i).mono (fun x t=> funext fun k=>funext (t k)))).mono fun i z k p q=> congr_fun (congr_fun (z k) p) q
    intro x; apply continuous_pi; intro k; apply continuous_pi; intro z; let E:=(κx x a)
    have hp:= E.orth.continuous.comp (usageBoatL (ζ x) R a k)
    exact ((E.U z).continuous.comp hp).dist hp
 filter_upwards [he] with x h p e k F z
 let yQ:MettleL a n:=⟨_,k⟩
 have hp:=dist_eq_zero.1 (h (FreightMars∘ F) yQ z)
 have hu:FreightMars.symm ∘ (FreightMars∘ F)=F:= funext fun i=> FreightMars.symm_apply_apply _
 rw [FeelRiverL _ R U a F _ e (CanSwimL a P yQ)]; dsimp only[y] at hp; rw[hu] at hp -- let definitions
 -- tune
 exact hp
#print axioms flowsFullL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
