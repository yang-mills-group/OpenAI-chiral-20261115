import GaugeFieldConstruction.SkeldL
import GaugeFieldConstruction.SummitFromStars
import GaugeFieldConstruction.SunfireCell
/-!
 # Rotation source.S.Region & contour char marks. Use on p=(AUTH Ticket) only apart from generic tally lemmas.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C)(Y:AreaQc S)
variable {Z F:CloudsL}
open FirstPackMars
namespace SurfCheckL
lemma windDoneL (V:Views S atTop u)(H:FirstPackMars p Y): SurfCheckL (CloudMeanL p Y) where
 clean x F:= (CoronaPL p Y _ _ (fun i j h=> Fin.elim0 i)).trans (H.clean F x)
 coin F x h:=by rw[CoronaPL p Y _ x h, H.coin F x h, CoronaPL p Y F _ (NSF.Points.tail_in h)]
 symmetry s F x h:=by rw[CoronaPL p Y _ _ (NSF.Points.rearrange_in _ h), H.symm s F x h, CoronaPL p Y F _ h]
 even t F x h:=by rw [CoronaPL p Y _ _ (NSF.Points.across_in t h),H.even t F x h,CoronaPL p Y F _ h]
 radar:= sunnyProbeL p Y V
 sm F:= (TerraSm p Y F).congr (fun x e=> CoronaPL p Y F x e)
-- Mean real orientation independent.
lemma SpinnerL (H:FirstPackMars p Y): (SurfRimL (CloudMeanL p Y)).RealSpin where
 mirror {n} s x h v:=by
    rw [surfReadL,surfReadL,CoronaPL p Y _ _ (NSF.Points.move_in _ h), CoronaPL p Y _ x h]; rw [← H.spin s _ _ h]; congr 1; ext1 i; exact TracksMirrorL ..
 real {n} x h v:=by
    rw [surfReadL,surfReadL,CoronaPL p Y _ x h, CoronaPL p Y _ x h, ← H.shade _ x h]; congr 1; ext1 i; exact TracksStarL ..
-- for all systems cloud total. 
variable (D:SurfCheckL Z)(B:SurfCheckL F)
open Loft Mink Cell NSF.Boundary NSF.LD
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
noncomputable def TurnEquivL {g:Type*}[Group g](T:g→* Module.End ℂ ΧiMars) (a:g):ΧiMars≃ₗ[ℂ]ΧiMars where
 __:= T a
 invFun:=T a⁻¹
 left_inv i:=by change T a⁻¹ (T a i)=_; rw [←Module.End.mul_apply, ←map_mul,inv_mul_cancel,map_one]; rfl
 right_inv i:=by change T a (T a⁻¹ i)=_; rw [←Module.End.mul_apply, ←map_mul,mul_inv_cancel,map_one]; rfl
noncomputable def BucketPL (d:ℕ): Ortho.Skew→ₗ[ℝ](Module.End ℂ ((SurfRimL Z).Field d)) where
 toFun x:= (D.HingeL d).symm.toLinearMap ∘ₗ (p.path.pi x four) ∘ₗ (D.HingeL d).toLinearMap
 map_add' x y:=LinearMap.ext fun i=> by simp
 map_smul' a x:= by
    apply LinearMap.ext; intro i; rw [map_smul]; change _= a • (D.HingeL d).symm _; change (D.HingeL d).symm ((a:ℝ) • (scorePathL p x) _) = _; exact map_smul ((D.HingeL d).symm.toLinearMap.restrictScalars ℝ) a _ -- tune
noncomputable def VesselPL: (SurfRimL Z).Rotation where
 act d x:= if e:x.val.det=1 then ((D.HingeL d).trans (TurnEquivL (compassPiMars p) (⟨x,(covers_all _).2 e⟩:SO))).trans (D.HingeL d).symm else LinearEquiv.refl ..
 lie :=BucketPL p D
lemma BucketApplyL d Ω f: (VesselPL p D).lie d Ω f=(D.HingeL d).symm (p.path.pi Ω four (D.HingeL d f)):=rfl
lemma prepareL (a: SO) d i: (VesselPL p D).act d a.val i=(D.HingeL d).symm (compassPiMars p a (D.HingeL d i)):=by unfold VesselPL; dsimp only; rw[dif_pos (show a.val.val.det=1 from (covers_all _).1 a.property)]; rfl
include D
lemma leafDerivL d (a:Ortho.Skew) (x:(SurfRimL Z).Field d)(t): HasDerivAt (fun t=> (VesselPL p D).act d (Ortho.oneParameter a t) x) ((VesselPL p D).lie d a ((VesselPL p D).act d (Ortho.oneParameter a t) x)) t :=by
 let E: grainMars →L[ℝ] (SurfRimL Z).Field d:= LinearMap.toContinuousLinearMap (((D.HingeL d).symm.toLinearMap ∘ₗ FreightMars.symm.toLinearMap).restrictScalars ℝ)
 have h(s:ℝ): (VesselPL p D).act d (Ortho.oneParameter a s) x = (D.HingeL d).symm (compassPiMars p (Angles.rise a s) (D.HingeL d x)):= prepareL p D (Angles.rise a s) d x
 simp_rw[h]; rw [BucketApplyL,LinearEquiv.apply_symm_apply]; let U:= p.path.pi a four; let F'(t):= compassPiMars p (Angles.rise a t) (D.HingeL d x)
 have hp :HasDerivAt (fun t=> E (FreightMars (F' t))) (E (FreightMars (U (F' t)))) t := E.hasFDerivAt.comp_hasDerivAt t (shipPioMars p _ a t)
 simp_rw[show ∀ x, E (FreightMars x)= (D.HingeL d).symm x from fun x=>congrArg (D.HingeL d).symm (FreightMars.symm_apply_apply x)] at hp; exact hp
lemma ValueOneL (d:ℕ)(f): (VesselPL p D).act d 1 f=f:= by change (VesselPL p D).act d (1:SO).val f=_; rw [prepareL,sailOneMars, LinearEquiv.symm_apply_apply] -- tune
lemma HullOrientL (s: (SurfRimL Z).RealSpin) : (VesselPL p D).Horizon D.RiseFrameL s where
 inOrbit Ω t:= (covers_all _).1 (Angles.rise Ω t).property
 fixes:= ValueOneL p D
 group d g k q x f:=by
    let G:SO:=⟨g,(covers_all _).2 q⟩; let K:SO:=⟨k,(covers_all _).2 x⟩; change (VesselPL p D).act d (G*K).val f= (VesselPL p D).act d G.val ((VesselPL p D).act d K.val f); rw [prepareL, prepareL,prepareL, sailMulMars]; rw [LinearEquiv.apply_symm_apply]
 infinitesimal d Ω v:=by
    have h:=leafDerivL p D d Ω v 0; rw[show Ortho.oneParameter Ω 0=1 from YM.Work.A13.oneParameter_zero _,ValueOneL] at h; exact h
-- Horizon and T-axis
omit D
abbrev boisterL (F:CloudsL):Prop:=∀ (n:ℕ)(v:Fin n→ΧiMars) x, x∈conf n→ ∀ a:SO,F n (motionMoonMars a x) (compassPiMars p a ∘ v)= F n x v
lemma MeanVitaL (H:FirstPackMars p Y)(R:NSF.Table.Hierarchy (BellTableMars p Y)):boisterL p (CloudMeanL p Y):= fun i x y h a=>by rw [CoronaPL _ _ _ _ (NSF.Points.move_in _ h), VitaPiiotMars H R a _ x y h,CoronaPL _ _ x y h]
include D
lemma boatTiltsL (v:boisterL p F) : (VesselPL p D).OrientedL (SurfRimL F):=by
 intro n w x e i q; let g:SO:=⟨i,(covers_all _).2 q⟩; rw [D.chartAngleL,D.chartAngleL]; refine Eq.trans ?_ (v n _ x e g); congr 1; ext1 j; change D.HingeL (w j).1 ((VesselPL p D).act (w j).1 g.val _)=(compassPiMars p _ (D.HingeL _ _)); rw [prepareL,LinearEquiv.apply_symm_apply]
omit D
-- Lor turns
noncomputable def HeightsKL : Spins (SurfRimL Z) where
 rail x:=(D.TinCanL.symm.trans (TurnEquivL (SpheruleL p) x)).trans D.TinCanL
 shell d x:= ((D.HingeL d).trans (TurnEquivL (SpheruleL p) x)).trans (D.HingeL d).symm
local notation "ΡHold"=> HeightsKL p D
include D
lemma KSpunL (g x): (ΡHold).rail g (D.TinCanL x)=D.TinCanL (SpheruleL p g x):= by change D.TinCanL (SpheruleL p g (D.TinCanL.symm _))=_; rw [LinearEquiv.symm_apply_apply]
variable (s: (SurfRimL Z).RealSpin)
lemma HonAdjL (d x): D.HingeL d ((SurfRimL Z).adj s d timeAxis x)=asterL (D.HingeL d x):=by
 obtain ⟨x,rfl⟩:= (SurfRimL Z).onto d x
 rw [NSF.Table.adj_project,D.HingeRiseL,D.HingeRiseL]
 change TracksEL _ (LoftRimL.mirrorGroup d _ (star x))=_; rw[TracksMirrorL,TracksStarL]; rfl
private noncomputable def KrunL (d:ℕ): grainMars→L[ℝ] (SurfRimL Z).Field d:= LinearMap.toContinuousLinearMap (((D.HingeL d).symm.toLinearMap ∘ₗ FreightMars.symm.toLinearMap).restrictScalars ℝ)
private lemma KrunKnownL d x: D.KrunL d (FreightMars x)=(D.HingeL d).symm x:=congrArg _ (FreightMars.symm_apply_apply _)
lemma warmKL : (ΡHold).Descends (VesselPL p D) s where
 ties g d v:=by rw[← D.tinRiseL, KSpunL]; rw[←D.tinRiseL]; change _=D.TinCanL (D.HingeL d ((D.HingeL d).symm _)); rw [LinearEquiv.apply_symm_apply]; rfl -- tune
 identity x:=by obtain ⟨x,rfl⟩:= D.TinCanL.surjective x; rw[KSpunL,map_one]; rfl
 representation a b x:=by obtain ⟨x,rfl⟩:= D.TinCanL.surjective x; rw[KSpunL,KSpunL,KSpunL,map_mul]; rfl
 spin d v:=by
    let U(g):= SpheruleL p g (D.HingeL d v)
    have h:Continuous (fun g=> FreightMars (U g)):= continuous_pi fun i=>keepAL p (D.HingeL d v) ((LinearMap.proj (φ:=fun _ :SpeckMars=>ℂ) i) ∘ₗ FreightMars.toLinearMap)
    exact ((D.KrunL d).continuous.comp h).congr (fun x=>D.KrunKnownL ..)
 boosts d j q:=by
    let U:= D.HingeL d q; let F'(t):= SpheruleL p (γBeamL j t) U
    have h:HasDerivAt (fun t=> FreightMars (F' t)) (FreightMars (ThriveL p j U)) 0:=hasDerivAt_pi.mpr (fun i=>(glowersL p U j) ((LinearMap.proj (φ:=fun _ :SpeckMars=>ℂ) i) ∘ₗ FreightMars.toLinearMap))
    have he: HasDerivAt (fun t=> D.KrunL d (FreightMars (F' t))) (D.KrunL d (FreightMars (ThriveL p j U))) 0:= (D.KrunL d).hasFDerivAt.comp_hasDerivAt _ h
    simp_rw[D.KrunKnownL] at he; rw [ThriveL, LinearMap.smul_apply, LinearEquiv.map_smul] at he; exact he
 spatial K h d q:=by
    change (D.HingeL d).symm (SpheruleL p _ _)= (VesselPL p D).act d (parkLorL K h).val q; rw [prepareL,SpheruleParkL]; rfl
 commutes g d v:=by
    apply (D.HingeL d).injective; rw [D.HonAdjL]; change asterL (D.HingeL d ((D.HingeL d).symm _))= D.HingeL d ((D.HingeL d).symm (SpheruleL _ _ (D.HingeL d _))); rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,D.HonAdjL s]; exact LinearMap.congr_fun (balanceL p g) _
include B
lemma FocusL (V:boisterL p F): FitsL (SurfRimL Z) (SurfRimL F) (VesselPL p D) s D.RiseFrameL (HeightsKL p D):=⟨D.PlannerL.toSymmetric,B.PlannerL,fun i=>le_of_eq ((D.FlagsL i).trans (B.FlagsL i).symm),D.RiseKnownL _,B.FairWindL,boatTiltsL p D V,HullOrientL p D s,warmKL p D s,B.LagoonL⟩
omit B
noncomputable def AsterBackL : StarOp (SurfRimL Z):= D.TinCanL.toLinearMap ∘ₛₗ asterL ∘ₛₗ D.TinCanL.symm.toLinearMap
lemma AsterLiberL: starRead D.AsterBackL s:=by intro d v; change D.TinCanL (asterL (D.TinCanL.symm _))=_; rw [D.tinPayL,← D.HonAdjL s, D.tinRiseL]
#print axioms FocusL
end SurfCheckL
end YM.GaugeFieldConstruction.Ember.Volumetric
