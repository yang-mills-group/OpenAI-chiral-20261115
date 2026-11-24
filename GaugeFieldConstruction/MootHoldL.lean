import GaugeFieldConstruction.CherubL
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
open Complex Mink SignetS YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric NSF.Boundary
variable {n:ℕ}{cost:ℕ→P.Test→ℂ} (C:Porch P cost timeAxis)
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {X F:CloudsL}
open NSF.Work.C22 -- uses Types aliases in YM.Boundary need namespace qualified
local notation "Ξ"=> C.groundHab
local notation "Eχ"=> C.BrightHab.E
local notation "Uₛ"=> C.BrightHab.U
local notation "Bφ" x:max=> Small.bufferF x
variable (A:AllocatedL P) (R:ΧiMars →ₗ[ℂ]ScreensJ P)
lemma CurtainTimeL (v:OS.Cross timeAxis)(u:ℝ≥0)(x:C.DegreeHab): Uₛ v ((Eχ u) x)= Eχ u (Uₛ v x):= (congrArg (fun i:C.DegreeHab.Op=>i x) (C.BrightHab.independent u v)).symm
lemma CurtainSpaceL (v w:OS.Cross timeAxis)(x:C.DegreeHab): Uₛ v (Uₛ w x)= Uₛ (v+w) x:= (congrArg (fun i:C.DegreeHab.Op=>i x) (C.BrightHab.space v w)).symm
lemma CurtainNegL (v:Axis→ℝ): diameter (a:=timeAxis) (-v)= -(show OS.Cross timeAxis from diameter v):=by unfold diameter; exact map_neg ..
lemma B_OpeningL : (Bφ (0:Space3))=(0:NSF.OS.Cross timeAxis):=by
 have h:=keepingL 0 0; rw [sub_zero,sub_self] at h; exact h
-- Gabriel conversion
variable (X)
local notation "θport"=> ShallowPortL C X
variable (D:SurfCheckL F)
abbrev MarksTieL {F:CloudsL} (v:Fin n→(SurfRimL F).Tag): Fin n → (SurfRimL F).Union:= pinned ∘ v
abbrev stampsEL (v:Fin n→ (SurfRimL F).Tag): Fin n→ ΧiMars := fun i => D.HingeL (v i).1 (v i).2
local notation "pHκ"=> SmallRimL C R A X D
abbrev RutterL (p:ℝ≥0)(y:YM.Boundary.Heights n)(x:SpacePoints n)(v: Fin n→(SurfRimL F).Tag):= List.ofFn (fun i:Fin n=> TrolleyMars C ((position (x i) (y i)).ofLp) ((R (stampsEL D v i)) timeAxis (A.pad p) (A.pad p)) (StallJ P (A.pad p)))
lemma RidgeTimeL p (y:YM.Boundary.Heights n)(x:SpacePoints n)(v: Fin n→(SurfRimL F).Tag) t (h:∀ i, t ≤ y i - StallJ P (A.pad p)) : AheadActorMars t (RutterL C A R D p y x v):=by
 intro i hi; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi; change _≤(position (x j) (y j)) timeAxis -_; simpa [position] using h j
local notation "PΣ" s:max l:max=> ActorMars C.BrightHab Ξ (some s) l
-- Hoist
lemma FromRawL p q (y:YM.Boundary.Heights n)(x:SpacePoints n)(w:Fin n→ (SurfRimL F).Tag)(t:ℝ)(T:Space3)(hp:0<p)(h:Room p q y t):
    fromRef (pHκ) p q (iz ∘ y) x (pinned ∘ w) (iz t) T=Uₛ (- (Bφ T)) (PΣ (t+q) (RutterL C A R D p y x w)):=by
 induction n generalizing q t T with
 | zero=>
    rw[show RutterL C A R D p y x w=[] from rfl]; exact (waxSureL C _).symm
 | succ n ih=>
    let i:=x 0; let u:=y 0; let l:=RutterL C A R D p (Fin.tail y) (Fin.tail x) (Fin.tail w)
    let d:=A.pad p; let f:=stampsEL D w 0; let N:=R f timeAxis d d; let K:= LadderRackMars C N; let D':=StallJ P d
    have he:RutterL C A R D p y x w = TrolleyMars C ((position i u).ofLp) N D':: l :=by unfold RutterL; rw[List.ofFn_succ]; rfl
    have hv:Fin.tail (iz ∘ y)= iz ∘ Fin.tail y:=rfl; have hz:Fin.tail (pinned ∘ w)= pinned ∘ Fin.tail w:=rfl
    rw [nextRef, hv,hz]; dsimp only [Function.comp_apply]; rw [show Small.rip (C:=ShallowPortL C X) _ _ _= _ from flyL C X (y 0) t _ (h.1 0) _, ih _ (Fin.tail y) _ _ (y 0) _ (tailRoom h), he]
    have hb :(SmallRimL C R A X D).bar p (pinned (w 0))=(Eχ (slitL A p)).comp (K.comp (Eχ (slitL A p))):=by
       change RimTimeL C R A p (D.TinCanL.symm _) = _
       rw [pinned, D.tinPayL]; rfl
    rw[hb]
    let S':=slitL A p; let Y:=PΣ (u+(p:ℝ)) l
    let B:=(u-t-((q+p:ℝ≥0):ℝ)).toNNReal
    have hI :AheadActorMars (u+(p:ℝ)) l:=by
       refine RidgeTimeL C A R D _ _ _ _ _ fun i=>?_; have ha:= (tailRoom h).1 i; change ((p+p:ℝ≥0):ℝ)< Fin.tail y i-u at ha; rw[NNReal.coe_add] at ha; linarith only [ha, A.cent hp]
    have h₁:D' < (p:ℝ):=A.cent hp
    have hw: (Eχ S') Y= PΣ (u+D') l:=by rw [LedgeActMars C.BrightHab Ξ (SpireHTMars C) l _ (u+p) hI (by linarith),show u+(p:ℝ)-(u+D')=(p:ℝ)-D' from by ring]
    have ht: (B+S')=(u-D'-(t+q)).toNNReal :=by
       apply NNReal.eq; rw [NNReal.coe_add]; unfold B S'; have hp': 0 < u-t-((q+p:ℝ≥0):ℝ):=sub_pos.mpr (h.1 0)
       rw [Real.coe_toNNReal _ hp'.le,slotPayL A hp,Real.coe_toNNReal]; swap; · rw [NNReal.coe_add] at hp'; linarith
       rw[NNReal.coe_add]; unfold D' d; ring
    let R':= position i u; have hX:(R'.ofLp timeAxis)=u:= by simp [R',position]
    have hZ: (StampActMars C (R'.ofLp) N) (PΣ (u+D') l)= Uₛ (Bφ i) (K (Uₛ (-(Bφ i)) (PΣ (u+D') l))):=by rw[StampActMars,CurtainNegL, crossRunL]; rfl
    rw [ActorMars];
    -- lhs sizes includes powers B then Upt T neg.
    change Eχ B (Uₛ (Bφ (i-T)) (Eχ S' (K (Eχ S' (Uₛ (-(Bφ i)) Y)) )) ) = Uₛ (- (Bφ T)) (Eχ ((R'.ofLp timeAxis-D'-(t+q)).toNNReal) (StampActMars C R'.ofLp N (PΣ (R'.ofLp timeAxis+D') l)))
    rw[← CurtainTimeL C (-Bφ i), hw, hX, hZ, CurtainTimeL C, CurtainTimeL C, CurtainSpaceL C,← ht,C.BrightHab.time, keepingL]
    let V:= Bφ T; let W:= Bφ i; have hv : (-(V:OS.Cross timeAxis)+W : OS.Cross timeAxis)= W-V := (show (-V)+W=W-V from (by abel)); exact congrArg (fun w:OS.Cross timeAxis=> Eχ B (Eχ S' (Uₛ w (K (Uₛ (- (Bφ i)) (PΣ (u+D') l)))))) hv.symm
-- specialize matrix and kernel.
lemma EchoRimL p (y:YM.Boundary.Heights n)(x:SpacePoints n)(w:Fin n→(SurfRimL F).Tag)(h:Small.enough y p):
 (pHκ).matrix p n (iz ∘ y) x (pinned ∘ w) = inner ℂ Ξ (ActorMars C.BrightHab Ξ none (RutterL C A R D p y x w)):=by
 have hz:=h.1
 have ht :∃ t:ℝ,Room p 0 y t:=by
    obtain ⟨z,fz⟩:= (Set.finite_range y).bddBelow
    refine ⟨z-2*(p:ℝ),fun i=>?_,fun i j hij=>?_⟩
    · have e:z≤ y i := fz ⟨_,rfl⟩; rw [zero_add]; have hp:0<(p:ℝ):=hz; linarith
    rw [NNReal.coe_add]; linarith [h.2.2 i j hij, show 0<(p:ℝ) from hz]
 obtain ⟨t,T⟩:=ht
 rw [CueActorMars C.BrightHab Ξ (SpireHTMars C) _ (t+((0:ℝ≥0):ℝ))]
 have hv:= FromRawL C X A R D p 0 y x w t 0 hz T
 rw [B_OpeningL,neg_zero] at hv; change fromRef (pHκ) p 0 (iz ∘ y) x (pinned ∘ w) (iz t) 0= Uₛ (0:OS.Cross timeAxis) (PΣ (t+↑(0:ℝ≥0)) (RutterL C A R D p y x w)) at hv; rw [C.BrightHab.uZero,ContinuousLinearMap.id_apply] at hv; rw[←hv]
 cases n with
 | zero=>rfl
 | succ n=>
    rw [fromRef]; dsimp only [Function.comp_apply]; rw [flyL C X (y 0) t (0+p) (T.1 0)] -- composition
    let K:=(Bφ (x 0-0)); let o:=(y 0-t-((0+p:ℝ≥0):ℝ)).toNNReal
    change inner ℂ Ξ _= inner ℂ Ξ ((Eχ o) (Uₛ K _)); rw[← MirrorHeatMars _ o Ξ, SpireHTMars C]
    have e(z:C.DegreeHab):inner ℂ Ξ (Uₛ K z)=inner ℂ Ξ z:=by
       nth_rw 1 [←waxSureL C K]; exact LinearIsometry.inner_map_map (𝕜:=ℂ) (show C.DegreeHab →ₗᵢ[ℂ] C.DegreeHab from { (Uₛ K).toLinearMap with norm_map':=C.BrightHab.unitary _}) _ _
    rw[e]; rfl
#print axioms EchoRimL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
