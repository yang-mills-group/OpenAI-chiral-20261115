import GaugeFieldConstruction.MistEarthL
import GaugeFieldConstruction.LucySphereL
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
-- open charts. costs agree and covary densely. plain continuity enough first.
abbrev blueL (n:ℕ): Set (Points n):= ΦplanR n ⁻¹' (CardsR (Fin n))
abbrev westL (n:ℕ)(a:Axis): Set (Points n):=ΦplanR n ⁻¹' VplaneR _ a
lemma westBlueL : westL n a ⊆ blueL n := preimage_mono (subset_iUnion _ a)
lemma basicWestL (a:Axis)(s:E4): NSF.Points.across s p ∈ westL n a ↔ p∈ westL n a:=by
 change Function.Injective _ ↔ Function.Injective _
 -- tune whether across order v x
 constructor
 · intro h i j q; apply h; change p i a+s a=p j a+s a; exact congrArg (fun u:ℝ=>u+s a) q
 intro h i j q; apply h; change p i a+s a=p j a+s a at q; exact add_right_cancel q
lemma spikeWestL (h:p∈westL n a):∃ s:E4, Nonempty (StallLeadMars a (NSF.Points.across s p) P):=by
 have he:∀ᶠ t:ℝ in atTop,∀ i:Fin n,0<t+p i a:= eventually_all.mpr fun i=> (eventually_gt_atTop (-p i a)).mono fun k u=>by linarith
 obtain ⟨b,hp⟩:=he.exists; let s:= b • basis a
 have hm:= (basicWestL p a s).mpr h -- tune order
 refine ⟨s,AppointsMars a _ ⟨hm,?_⟩ P⟩; intro i; change 0<(p i+s) a; simp [s]; linarith [hp i]
lemma clearL (n:ℕ):IsOpen (blueL n):=(prosc_R _).preimage (ΦlegR _)
include U
lemma BlueL : ContinuousOn (CoralL Cw R F) (blueL n):= (groundPlotR Cw _ (fun i=> U.showL _)).comp (ΦlegR _).continuousOn fun i=> id
lemma BlueAtL (v:p∈ blueL n):ContinuousAt (CoralL Cw R F) p:= (BlueL Cw R F U).continuousAt ((clearL _).mem_nhds v)
lemma WestOpensL (h:p∈westL n a):∃ L:List (Fin n),∃ σ:Fin n→PermWallJ P, PolesR L ∧ ΦplanR n p∈OpenR a σ L:=by -- omit U below
 obtain ⟨L,u,y⟩:= vplane_w (show ΦplanR _ p∈ VplaneR _ a from h)
 obtain ⟨r,z⟩:= (OpenPatR L (ΦplanR _ p) P a y).exists; exact ⟨L,_,u,z⟩
lemma CoralAcrossL (e:p∈ blueL n)(s:E4): CoralL Cw R F (NSF.Points.across s p)=CoralL Cw R F p:=by
 let v:= NSF.Points.across s p
 rcases mem_iUnion.mp (show ΦplanR _ p∈CardsR _ from e) with ⟨b,h⟩
 obtain ⟨l,σ,t,w⟩:=WestOpensL (P:=P) R b p U h
 have hu: ΦplanR n v= fun i=>ΦplanR n p i+s.ofLp:=by ext i j; simp [v,NSF.Points.across,ΦplanR,add_comm]
 have he: ΦplanR n v∈ OpenR b σ l:=by rw[hu]; refine (show RollBestR _ _ from w).imp fun {j k} t=>?_ ; simp only [Pi.add_apply]; linarith
 unfold CoralL; rw[ηTenderR Cw l _ (fun i=> U.showL _) b _ _ t he,ηTenderR Cw l _ (fun i=>U.showL _) b _ _ t w,hu]
 let A:=StageR σ (Cw b) (BodyΘ P (fun i=> R (F i)) b σ)
 have hA(v:OS.Cross b): (Cw b).BrightHab.U v (Cw b).groundHab=(Cw b).groundHab:=waxSureL ..
 exact Repertoire.homogeneous A hA l (ΦplanR n p) s.ofLp
-- perm
lemma CoralCardsL {m:ℕ}(d:Fin m ≃ Fin n)(p:Points n)(h:p∈ blueL n): CoralL Cw R (F ∘ d) (WithLp.toLp 2 (p.ofLp ∘ d))= CoralL Cw R F p:=by
 rcases mem_iUnion.mp (show ΦplanR _ p∈CardsR _ from h) with ⟨b,h⟩
 let p':Points m:=WithLp.toLp 2 (p.ofLp ∘ d)
 obtain ⟨l,σ,e,t⟩:=WestOpensL R b p U h
 let M:= l.map d.symm; let τ:= σ ∘ d
 have hz(i:Fin n): ΦplanR m p' (d.symm i)= ΦplanR n p i:=by unfold ΦplanR; dsimp [p']; rw [d.apply_symm_apply] -- tune
 have ht(i): τ (d.symm i)=σ i:=by simp [τ]
 have hp: ΦplanR m p'∈ OpenR b τ M:=by refine List.pairwise_map.mpr ((show RollBestR _ _ from t).imp fun {k j} a=>?_); rw [hz,hz,ht,ht]; exact a
 have hv:PolesR M:=⟨e.1.map d.symm.injective,fun i=> List.mem_map.mpr ⟨d i,e.2 _,d.symm_apply_apply i⟩⟩
 unfold CoralL; rw[ηTenderR Cw M _ (fun i=> U.showL _) b _ _ hv hp,ηTenderR Cw l _ (fun i=>U.showL _) b _ _ e t,EarningActorMars,EarningActorMars]
 apply congrArg (inner ℂ (Cw b).groundHab); apply congrArg (ActorMars _ _ _); unfold billActMars; rw[List.map_map]; apply congrArg (fun u:Fin n→VignMars (Cw b).DegreeHab=> l.map u); ext1 i; simp only [Function.comp_apply,hz,ht,BodyΘ,Equiv.apply_symm_apply] -- tune maybe apply link
omit U
abbrev MirrorPoseL (a:Axis)(p:Points n):= CalendarMoon (Signed.reflect a) p
lemma flipAtL(i:Fin n):ΦplanR n (MirrorPoseL a p) i=flipTactMars a (ΦplanR n p i):=by
 funext k; by_cases h:k=a
 · subst k; rw [flipTactMars,Function.update_self]; simp [ΦplanR,MirrorPoseL,CalendarMoon,NSF.Points.move] -- tune
 rw [flipTactMars,Function.update_of_ne h]; simp [ΦplanR,MirrorPoseL,CalendarMoon,NSF.Points.move,h]
lemma MirTravelsL(s:E4): MirrorPoseL a (NSF.Points.across s p)= NSF.Points.across ((Signed.reflect a).motion s) (MirrorPoseL a p):=by ext1 i; exact (Signed.reflect a).motion.map_add _ _
lemma mirWideL(b:Axis)(v:p∈ westL n b):MirrorPoseL a p∈ westL n b:=by
 intro i j h; change ΦplanR n (MirrorPoseL a p) i b= ΦplanR n (MirrorPoseL a p) j b at h; rw [flipAtL,flipAtL] at h ; by_cases r:b=a
 · subst b; exact v (neg_injective (by simpa only [flipTactMars,update_self] using h))
 rw [flipTactMars, Function.update_of_ne r,flipTactMars,Function.update_of_ne r] at h; exact v h
lemma miresL (v:p∈ blueL n):MirrorPoseL a p∈ blueL n:=by
 obtain ⟨k,t⟩:=Set.mem_iUnion.mp (show ΦplanR n p∈CardsR _ from v); exact westBlueL k (mirWideL a p k t)
include U
include J
lemma CoralStarryL : CoralL Cw R (TurnupMars a ∘ F) (MirrorPoseL a p)=Star.star (CoralL Cw R F p):=by -- include J below
 let z:= TurnupMars a ∘ F; let y:= MirrorPoseL a p; let c:=Cw a
 let l:=J.L; let A:= c.BrightHab; let S:=R ∘ F; let S':= R ∘ z
 let ζ:= queueActMars Cw a p J S
 rw [←ConquerL Cw R a p F J U]; change CoralL Cw R z y= Star.star (inner ℂ c.groundHab _)
 have e: PolesR l.reverse:= by refine ⟨List.nodup_reverse.mpr J.pol.1,fun i=> List.mem_reverse.mpr (J.pol.2 i)⟩
 have hp:ΦplanR n y∈ OpenR a J.σ l.reverse:=by
    apply List.pairwise_reverse.mpr; refine (show RollBestR _ _ from J.pays).imp fun {k i} e=>?_ ; unfold y; rw [flipAtL,flipAtL,flipTactMars,flipTactMars,Function.update_self,Function.update_self]; linarith
 have he: billActMars c J.σ (BodyΘ P S' _ J.σ) (ΦplanR n y) l.reverse= ζ.reverse.map ReflectActorMars ++ []:=by
    unfold ζ queueActMars billActMars; rw [List.append_nil,←List.map_reverse,List.map_map] -- wrong direction
    congr 1; ext1 i; unfold y; rw [flipAtL]; exact (Eq.trans (congrArg (fun k:P.Slabs a=> TrolleyMars c _ k _) (U.warmL (F i) a _)) (LoopActMars ..)) -- tune
 change SπR Cw S' (ΦplanR n y)=_;  rw [ηTenderR Cw l.reverse S' (fun i=> U.showL _) a _ _ e hp,EarningActorMars, he]
 rw [FoldActorMars A c.groundHab (SpireHTMars c) ζ [] 0 (ForwardReadyMars Cw S p J) (by simp [AheadActorMars]) (OrderedReadyMars Cw S p J) (WidthReadyMars Cw S p J)]
 exact (inner_conj_symm ..).symm
omit J
lemma PearlInGlassL (v:p∈westL n a) : CoralL Cw R (TurnupMars a ∘ F) (MirrorPoseL a p)=Star.star (CoralL Cw R F p):=by
 obtain ⟨s,J⟩:= spikeWestL (P:=P) a p v; obtain ⟨k⟩:=J
 have hu:= CoralStarryL Cw R a (NSF.Points.across s p) F k U
 rwa [MirTravelsL,CoralAcrossL Cw R _ _ U (miresL a p (westBlueL _ v)),CoralAcrossL Cw R _ F U (westBlueL _ v)] at hu
omit U
lemma lensClearL (a:Axis) {n:ℕ} {s:Set (Points n)}(v:IsOpen s)(b:Points n)(e:b∈s): b ∈ closure (s∩ westL n a):=by
 exact v.inter_closure ⟨e,closure_mono (show YM.generic n ⊆ westL n a from fun i h=>h a) (Dash.full n b)⟩
include U
lemma PearlMirL (e:p∈ blueL n): CoralL Cw R (TurnupMars a ∘ F) (MirrorPoseL a p)= Star.star (CoralL Cw R F p):=by
 let i(y:Points n):=MirrorPoseL a y; let g:=CoralL Cw R (TurnupMars a ∘ F); let s:= blueL n∩westL n a
 have hm: Continuous i:=by
    let h(p:Points n)(b:Fin n):E4:=Ortho.move (Signed.reflect a) (p b)
    have H : Continuous h:= continuous_pi (fun k:Fin n=> (Signed.reflect a).motion.continuous.comp (show Continuous (fun p:Points n=> p k) by fun_prop))
    exact (PiLp.continuous_toLp 2 _).comp H
 haveI := mem_closure_iff_nhdsWithin_neBot.mp (lensClearL a (clearL n) p e)
 have H: Tendsto (g ∘ i) (𝓝[s] p) (𝓝 (CoralL Cw R (TurnupMars a∘ F) (MirrorPoseL a p))):= (((BlueAtL Cw R _ (TurnupMars a∘ F) U (miresL a p e)).tendsto.comp (hm.tendsto p)).mono_left nhdsWithin_le_nhds)
 have V:ContinuousAt (fun i=>Star.star (CoralL Cw R F i)) p:= ContinuousAt.star (BlueAtL Cw R p F U e)
 exact tendsto_nhds_unique_of_eventuallyEq H (V.continuousWithinAt (s:=s)) ((show ∀ᶠ i in 𝓝[s] p, i∈s from self_mem_nhdsWithin).mono fun i h=> PearlInGlassL Cw R a i F U h.2)
lemma CoralHalfL(i j:Axis)(h:p∈blueL n): CoralL Cw R ((compassPiMars t (PlaneL.QκL i j)) ∘ F) (motionMoonMars (PlaneL.QκL i j) p)=CoralL Cw R F p:=by
 have hv: compassPiMars t (PlaneL.QκL i j) ∘ F= TurnupMars i ∘ (TurnupMars j ∘ F):=by
    ext1 k; unfold Function.comp; rw [PlaneL.QκL,PiProperMoon,map_mul]; unfold TurnupMars; rw [Calibration.comp_s,Calibration.clear]; rfl
 rw [hv,motionMoonMars,PlaneL.hemiKeyL,calend_mulMars]
 rw [show CoralL _ _ _ _=Star.star _ from PearlMirL Cw R i _ _ U (miresL j p h),PearlMirL Cw R j p F U h, star_star]
#print axioms CoralHalfL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
