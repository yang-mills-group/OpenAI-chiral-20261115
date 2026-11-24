import GaugeFieldConstruction.IvyMajorL
/-!
# Constant-grade rooms, NOT a raw/dummy Union. Isomorphism to U₄ when seen in actual S two-costs.

 In L libraries use rise maps, NOT any 4→4 derivatives! U∂/M on bigger derivative register only.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {n m:ℕ} {S: City}
-- simpler register Reg timelines: use ΡeaderMars 0. UniMars map.
noncomputable def LoftRimL : NSF.Register Unit.unit where
 dim _:= ΡeaderMars.dim 0
 scalar _:= ΡeaderMars.scalar 0
 mirrorGroup _:= ΡeaderMars.mirrorGroup 0
 bar_scalar d:= ΡeaderMars.bar_scalar 0
 star_mirror s d x:= ΡeaderMars.star_mirror s 0 _
 mirror_mul s k d x:= ΡeaderMars.mirror_mul s k 0 _
 mirror_one d x:= ΡeaderMars.mirror_one 0 _
 mirror_scalar s d:= ΡeaderMars.mirror_scalar s 0
noncomputable def TracksEL (d:ℕ): LoftRimL.Ref d→ₗ[ℂ] ΧiMars:= (∑ i:LabelMars 0,(LinearMap.proj i).smulRight (MCoreMars (ChaseMars 0 i).1))
lemma tracksApplyL (d x):TracksEL d x=∑ i:LabelMars 0,x i • MCoreMars (ChaseMars 0 i).1:=by unfold TracksEL; rw[LinearMap.sum_apply]; rfl
lemma tracksSingleL (d:ℕ)(i:LabelMars 0):TracksEL d (coneOneMars _ i)=MCoreMars (ChaseMars _ i).1:=by rw[tracksApplyL]; simp [coneOneMars,Pi.single_apply]
lemma TracksMirrorL (d:ℕ)(x: LoftRimL.Ref d)(s:Signed): TracksEL d (LoftRimL.mirrorGroup d s x)=spinFrame four s (TracksEL d x):=by
 have ht(i:LabelMars 0): TracksEL d (LoftRimL.mirrorGroup d s (coneOneMars 0 i))=spinFrame four s (TracksEL d (coneOneMars _ i)):=by
    change TracksEL d (writeArcMars 0 s _)=_; rw [tracksSingleL,writeArcOneMars]; change TracksEL _ (coneOneMars _ _)=_; rw [tracksSingleL]; simp [arcActsMars,ChaseMars,coreActsMars, MActsAtMars] -- tune
 let w:FlyerMars 0:=x
 have hz:x= ∑ i:LabelMars 0,w i • coneOneMars 0 i:=by change w=_; ext i; simp [coneOneMars,Pi.single_apply]
 conv_lhs=>arg 2; arg 2; rw [hz] -- tactic tune rw right all
 conv_rhs=>arg 2; arg 2; rw[hz]
 let T: FlyerMars 0→ₗ[ℂ]ΧiMars:=TracksEL d
 have h(i:LabelMars 0):T (writeArcMars 0 s (coneOneMars 0 i))=spinFrame four s (T (coneOneMars 0 i)):=ht i
 change T (writeArcMars 0 s _) = spinFrame four s (T _)
 simp_rw [map_sum,map_smul,h]
lemma TracksStarL (d:ℕ)(x: LoftRimL.Ref d): TracksEL d (star x)=Calibration.shade four (TracksEL d x):=by rw [tracksApplyL, tracksApplyL,map_sum]; apply sum_congr rfl; intro i _; rw[map_smulₛₗ,MFixedMars]; rfl
lemma TracksCleanL (d:ℕ):TracksEL d (LoftRimL.scalar d)=Empire.one four:=by change TracksEL d (coneOneMars 0 (arcBlankMars 0))=_; rw [tracksSingleL]; simp [arcBlankMars,ChaseMars,MCoreMars]
noncomputable def BookRimL (d:ℕ):ΧiMars→ₗ[ℂ] LoftRimL.Ref d:= FirstPackMars.mintUnoMars 0 (TrailBlankMars 0)
lemma BookRichL (d:ℕ)(x):TracksEL d (BookRimL d x)=x:=by
 change TracksEL d (FirstPackMars.mintUnoMars _ _ _)=_
 conv_rhs=> rw[← FirstPackMars.valueUnoAtMars x,UniAtMars];
 let T : FlyerMars 0→ₗ[ℂ]ΧiMars:=TracksEL d
 have ht(i:LabelMars 0):T (coneOneMars 0 i)=MCoreMars (ChaseMars 0 i).1:= tracksSingleL d i
 change T (FirstPackMars.mintUnoMars _ _ _) = _; rw[FirstPackMars.mintUnoMars,LinearMap.sum_apply,map_sum]; apply sum_congr rfl; intro i _; simp only [LinearMap.smulRight_apply,map_smul,ht]; unfold ChaseMars; rw[Equiv.symm_apply_apply]; rfl
variable (Z:CloudsL)
noncomputable def SurfRimL : NSF.Table LoftRimL where value {n} d x:=(Z n x).compLinearMap (fun i=> TracksEL (d i))
abbrev elementalL (p:LoftRimL.Token): ΧiMars:= TracksEL p.1 p.2
lemma surfReadL (F:Fin n→ LoftRimL.Token)(x:Points n):(SurfRimL Z).read x F=Z n x (elementalL ∘ F):=rfl
structure SurfCheckL (Z:CloudsL): Prop where
 clean (x:Points 0)(F:Fin 0→ΧiMars): Z 0 x F=1
 coin {n:ℕ}(F:Fin n→ΧiMars)(x:Points (n+1))(h:x∈conf (n+1)): Z (n+1) x (Fathom.add (Empire.one four) F)=Z n (Points.tail x) F
 symmetry {n:ℕ}(s:Equiv.Perm (Fin n))(F:Fin n→ΧiMars) (x:Points n)(h:x∈conf n): Z n (NSF.Points.rearrange s x) (F ∘ s)=Z n x F
 even {n:ℕ}(t:E4)(F:Fin n→ΧiMars)(x:Points n)(h:x∈conf n): Z n (NSF.Points.across t x) F=Z n x F
 radar: uncloudL Z
 sm {n:ℕ}(F:Fin n→ ΧiMars): ContDiffOn ℝ ∞ (fun x=>Z n x F) (conf n)
variable {Z}
namespace SurfCheckL
variable (P: SurfCheckL Z)
local notation "ΤR"=> SurfRimL Z
include P
lemma PlannerL: (ΤR).Basic where
 same p x h w:=P.symmetry p (elementalL ∘ w) _ h
 trivial f x:= P.clean x _
 unital {n} x h d v:=by
    rw [surfReadL, surfReadL,show elementalL ∘ (Fin.cons (α:=fun _=> LoftRimL.Token) (LoftRimL.one d) v)= Fathom.add (Empire.one four) (elementalL ∘ v) from ?_]; exact P.coin (elementalL ∘ v) _ h
    ext1 i; refine Fin.cases ?_ (fun j=>rfl) i; exact TracksCleanL d
lemma FairWindL: (ΤR).Homogeneous:= fun i x t d v=> P.even d _ x t
lemma LagoonL : (ΤR).Smooth where on_conf {i} d v:=P.sm (fun j=>TracksEL (d j) (v j))
lemma FlagsL (d:ℕ): (ΤR).null d=LinearMap.ker (TracksEL d):=by
 refine le_antisymm (fun x h=>?_) (fun x h=>?_)
 · apply P.radar
   intro b y hy
   let F:Fin 2→LoftRimL.Token:=![⟨0,BookRimL 0 b⟩,⟨d,x⟩]
   have t:=(ΤR).each_place P.PlannerL.toSymmetric h hy F front rfl
   rw[surfReadL] at t
   have hz:elementalL∘ F=![b,TracksEL d x]:=by ext1 i; fin_cases i; exact BookRichL ..; rfl
   rw [hz] at t; exact t
 rw [(ΤR).criterion]; intro i F y hy; rw[surfReadL]; exact (Z (i+1) y).map_coord_zero 0 h
#print axioms FlagsL
-- all grade links
noncomputable def HazeL (d:ℕ):(ΤR).Field d→ₗ[ℂ]ΧiMars:= ((ΤR).null d).liftQ (TracksEL d) (Eq.le (P.FlagsL d))
lemma HazeRiseL (d x):P.HazeL d ((ΤR).project d x)=TracksEL d x:=rfl
lemma PillHL (d):Bijective (P.HazeL d):=by
 refine ⟨LinearMap.ker_eq_bot.mp (((ΤR).null d).ker_liftQ_eq_bot (TracksEL d) (Eq.le (P.FlagsL d)) (Eq.ge (P.FlagsL d))),fun x=>⟨(ΤR).project d (BookRimL d x),BookRichL d x⟩⟩
noncomputable def HingeL (d:ℕ): (ΤR).Field d≃ₗ[ℂ] ΧiMars:= LinearEquiv.ofBijective (P.HazeL d) (P.PillHL d)
lemma HingeRiseL (d x): P.HingeL d ((ΤR).project d x)=TracksEL d x:= P.HazeRiseL ..
lemma chartAngleL (Y:CloudsL)(x:Points n)(v:Fin n→(SurfRimL Z).Tag): (ΤR).useAt (SurfRimL Y) x v= Y n x (fun i=> P.HingeL (v i).1 (v i).2):=by
 change Y n x _= _; congr 1; ext1 i
 change TracksEL (v i).1 ((SurfRimL Z).representative _ _) =_; rw [← P.HingeRiseL]; congr; exact (ΤR).rep .. -- tune
noncomputable def RiseFrameL:NSF.DiffPlan (ΤR) where
 rise {d e} _:= (P.HingeL e).symm.toLinearMap ∘ₗ (P.HingeL d).toLinearMap
 deriv d a:=0
lemma RiseKnownL (Y:CloudsL): P.RiseFrameL.Inclusions (SurfRimL Y) where
 kernels {d e} h B n x hx w:=by
    rw [P.chartAngleL,P.chartAngleL]; congr 1; ext1 i
    refine Fin.cases ?_ (fun j=>rfl) i; change P.HingeL e ((P.HingeL e).symm _) =_; rw[LinearEquiv.apply_symm_apply]; rfl -- tune
noncomputable def tossL: ΧiMars→ₗ[ℂ](ΤR).Union:= (ΤR).pin 0 ∘ₗ (P.HingeL 0).symm.toLinearMap
lemma tossRiseL (d x): P.tossL (P.HingeL d x)=(ΤR).pin d x:=by
 change (ΤR).pin _ _=_; rw [← P.RiseFrameL.stays P.PlannerL.toSymmetric (P.RiseKnownL _) (Nat.zero_le d)]; congr 1; change (P.HingeL d).symm (P.HingeL 0 ((P.HingeL 0).symm _)) = _ ; simp
lemma tossKnownL : Bijective P.tossL:=by
 refine ⟨((ΤR).pin_inj 0).comp (P.HingeL 0).symm.injective, fun w=>?_⟩
 obtain ⟨i,x,rfl⟩:= P.RiseFrameL.covered P.PlannerL.toSymmetric (P.RiseKnownL _) w; exact ⟨P.HingeL _ x,P.tossRiseL ..⟩
noncomputable def TinCanL: ΧiMars ≃ₗ[ℂ](ΤR).Union:= LinearEquiv.ofBijective P.tossL P.tossKnownL
lemma tinRiseL (d x): P.TinCanL (P.HingeL d x)=(ΤR).pin d x:= P.tossRiseL ..
lemma tinPayL (d x): P.TinCanL.symm ((ΤR).pin d x)=P.HingeL d x:= P.TinCanL.symm_apply_eq.mpr (P.tinRiseL d x).symm -- tune
#print axioms TinCanL
end SurfCheckL
end YM.GaugeFieldConstruction.Ember.Volumetric
