import GaugeFieldConstruction.VoyLightL
import GaugeFieldConstruction.AngelItL
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
abbrev adoreL (a:Axis)(p:Points n)(u:p∈westL n a): Set (Points n):= westL n a -- reserve unused?
lemma razeWestL {g:SO}{a b:Axis}(h:suitAxL g a b){p:Points n}(v:p∈ westL n a): motionMoonMars g p∈westL n b:= fun _ _ e=> v ((h _).symm.trans (e.trans (h _))) -- eta tune
lemma constWestL (q:Equiv.Perm (Fin n))(a:Axis)(k:p∈westL n a):NSF.Points.rearrange q p∈ westL n a:=fun _ _ h=> q.injective (k h)
lemma TurnFolioL (g:SO)(s:E4) : motionMoonMars g (NSF.Points.across s p)=NSF.Points.across (g.val.motion s) (motionMoonMars g p):=by ext1 i; exact g.val.motion.map_add _ _
include U E Z f J0
lemma FoldGlamorL {a i j:Axis}(h:i≠j)(u:a≠i)(v:a≠j)(s:ℝ)(p:Points n)(e:p∈ westL n a) : ∀ᵐ x∂P.pillars 3, CoralL (P.privateH x) R F p=CoralL (P.privateH x) R (compassPiMars t (Ψ i j s) ∘ F) (motionMoonMars (Ψ i j s) p):=by
 let c:=Ψ i j s; have T':=AxisKeyL h u v s
 obtain ⟨δ,W⟩:=spikeWestL (P:=P) a p e
 obtain ⟨W⟩:=W; let y:= NSF.Points.across δ p; let q:Equiv.Perm (Fin n):= Tuple.sort (fun k=> y k a)
 let z:=NSF.Points.rearrange q y; have hz: z∈ westL n a:=constWestL y q a ((basicWestL p a δ).mpr e)
 have hp: eastL n a z:=by
    refine ⟨?_,fun k=>?_⟩
    · exact Monotone.strictMono_of_injective (Tuple.monotone_sort (fun k=> y k a)) hz -- tune
    let P':= W.toll (q k); change 0< y _ a; have W': 0<y (q k) a-StallJ P (W.σ (q k)):=P'; exact lt_of_lt_of_le W' (sub_le_self _ (W.σ (q k)).2.le)
 let A:BasinL a n:= (F∘ q,⟨z,hp⟩)
 filter_upwards [MuseL R G t U J0 f E Z h u v s A] with x a
 let C':= P.privateH x; let P':=motionMoonMars c p; let F':=compassPiMars t c ∘ F
 have hQ:P' ∈ blueL n:=westBlueL _ (razeWestL T' e)
 change CoralL C' R F p= CoralL C' R F' P'
 change CoralL C' R (F ∘ q) z=CoralL C' R (F' ∘ q) (motionMoonMars c z) at a
 rw [← CoralAcrossL C' R p F U (westBlueL _ e) δ,← CoralAcrossL C' R P' F' U hQ (c.val.motion δ), show NSF.Points.across (c.val.motion δ) P'=motionMoonMars c y from (TurnFolioL p c δ).symm]
 exact (CoralCardsL C' R F U q y (westBlueL _ ((basicWestL p _ _).mpr e))).symm.trans (a.trans (CoralCardsL C' R F' U q _ (westBlueL _ (razeWestL T' ((basicWestL p _ _).mpr e))))) -- b variable shadow tune Y
omit U E Z f J0
open TopologicalSpace
lemma DenseEdgeL {X Y:Type*}[TopologicalSpace X][TopologicalSpace Y][T2Space Y][SeparableSpace X]{I:Type}{K:Filter I}[CountableInterFilter K] (v w:I→X→Y)(hv:∀ i,Continuous (v i))(hw:∀ i,Continuous (w i))(h:∀ x,∀ᶠ i in K,v i x=w i x):∀ᶠ i in K,∀ x,v i x=w i x:=by
 cases isEmpty_or_nonempty X with
 | inl p=>exact Eventually.of_forall fun _ x=> isEmptyElim x
 | inr u=>
    filter_upwards [eventually_countable_forall.mpr (fun i:ℕ=> h (denseSeq X i))] with i p'; exact congr_fun ((denseRange_denseSeq X).equalizer (hv i) (hw i) (funext p'))
-- separate cont
lemma motionθL (g:SO) : Continuous (motionMoonMars (n:=n) g):=by
 let A(p:Points n)(j:Fin n):= g.val.motion (p j)
 have h:Continuous A:= continuous_pi (fun i=> g.val.motion.continuous.comp (show Continuous (fun p:Points n=>p i) by fun_prop))
 exact (PiLp.continuous_toLp 2 _).comp h
lemma pineSureL {a:Axis}(s:SO){b:Axis}(h:suitAxL s a b) : Continuous fun k:westL n a=> (⟨motionMoonMars s k.val,razeWestL h k.property⟩: westL n b):= (((motionθL s).comp continuous_subtype_val).subtype_mk fun k=>razeWestL h k.property) -- check Voyage namespace/import may not in Stack.
lemma followΚL (s:SO): Continuous (fun v:Fin n → grainMars=> FreightMars ∘ ((compassPiMars t s) ∘ (FreightMars.symm ∘ v))):=by
 apply continuous_pi; intro b
 let T':grainMars→ₗ[ℂ] grainMars:= FreightMars.toLinearMap ∘ₗ compassPiMars t s ∘ₗ FreightMars.symm.toLinearMap
 exact T'.continuous_of_finiteDimensional.comp (continuous_apply b)
include U
lemma AgitateWestL (p:Points n)(e:p∈blueL n): Continuous (fun k:Fin n → grainMars=> CoralL Cw R (FreightMars.symm∘ k) p):=by
 let L(k: Fin n → grainMars):Points n ×(Fin n → grainMars):=(p,k)
 let W(k:Points n ×(Fin n → grainMars)):= CoralL Cw R (FreightMars.symm∘ k.2) k.1
 change Continuous (W ∘ L); refine continuous_iff_continuousAt.mpr fun k=>?_ 
 have hp:ContinuousAt W (L k):= AtollLightL Cw R U k p e
 exact hp.comp (show ContinuousAt L k from (continuous_const.prodMk continuous_id).continuousAt)
omit U
lemma angleθL(i j:Axis) (p:Points n):Continuous (fun s:ℝ=> motionMoonMars (Ψ i j s) p):=by
 let A(s:ℝ)(k: Fin n):= Ortho.move (Ortho.oneParameter (Ortho.plane i j) s) (p k)
 have h:Continuous A:= continuous_pi (fun k=> continuous_iff_continuousAt.2 fun u=> (YM.Work.A13.hasDerivAt_move (Ortho.plane i j) (p k) u).continuousAt)
 exact (PiLp.continuous_toLp 2 _).comp h
lemma CompassStreamL(i j:Axis): Continuous (fun s:ℝ=> FreightMars ∘ (compassPiMars t (Ψ i j s) ∘ F)):= continuous_pi (fun k:Fin n=> continuous_iff_continuousAt.mpr fun u=> (shipPioMars t (F k) (Ortho.plane i j) u).continuousAt)
include U
lemma ballasteL {a i j:Axis}(h:i≠j)(u:a≠i)(v:a≠j)(p:Points n)(t':p∈westL n a): Continuous (fun s:ℝ=> CoralL Cw R (compassPiMars t (Ψ i j s) ∘ F) (motionMoonMars (Ψ i j s) p)):=by
 let M(s:ℝ):= motionMoonMars (Ψ i j s) p
 let T'':= fun s:ℝ=> compassPiMars t (Ψ i j s) ∘ F
 let L(s:ℝ): Points n ×(Fin n → grainMars):=(M s,FreightMars ∘ T'' s)
 let W(k:Points n ×(Fin n → grainMars)):= CoralL Cw R (FreightMars.symm∘ k.2) k.1
 have hp(x:ℝ):ContinuousAt W (L x):=AtollLightL Cw R U (FreightMars ∘ T'' x) (M x) (westBlueL _ (razeWestL (AxisKeyL h u v x) t'))
 have hm : Continuous L:= (angleθL i j p).prodMk (CompassStreamL t F i j)
 refine (show Continuous (W ∘ L) from continuous_iff_continuousAt.mpr fun x=>(hp x).comp hm.continuousAt).congr ?_
 intro x; change CoralL _ _ (FreightMars.symm ∘ (FreightMars ∘ T'' x)) (M x)= _; exact congrArg (fun T=> CoralL Cw R T (M x)) (show FreightMars.symm ∘ (FreightMars ∘ T'' x)=T'' x from funext fun i=> FreightMars.symm_apply_apply _)
include Z E f J0
lemma GlamorL {a i j:Axis}(h:i≠j)(u:a≠i)(v:a≠j)(s:ℝ)(n:ℕ) : ∀ᵐ x∂P.pillars 3,∀ (p:Points n), p∈westL n a→ ∀ F:Fin n→ΧiMars, CoralL (P.privateH x) R F p= CoralL (P.privateH x) R (compassPiMars t (Ψ i j s) ∘ F) (motionMoonMars (Ψ i j s) p):=by
 let A(x:P.Spectrum0 3)(p:westL n a)(F:Fin n → grainMars):= CoralL (P.privateH x) R (FreightMars.symm ∘ F) p.val
 let T':= fun v:Fin n→ grainMars => FreightMars ∘ (compassPiMars t (Ψ i j s) ∘ (FreightMars.symm ∘ v))
 let Y(k:westL n a): westL n a:= ⟨_,razeWestL (AxisKeyL h u v s) k.property⟩; let S x p F:= A x (Y p) (T' F)
 have hx(x) (F:Fin n → grainMars): Continuous (fun p=> A x p F) :=(continuousOn_iff_continuous_restrict.mp ((BlueL (P.privateH x) R _ U).mono (westBlueL a))) -- tune
 have hu(V:Fin n → grainMars): FreightMars.symm ∘ T' V= compassPiMars t (Ψ i j s) ∘ (FreightMars.symm ∘ V):= funext fun i=>FreightMars.symm_apply_apply _
 have e:∀ᵐ x∂P.pillars 3,∀ p: westL n a, A x p=S x p:=by
    apply DenseEdgeL A S (fun i=> continuous_pi fun F=>hx i F) (fun c=> continuous_pi fun F=> (hx c (T' F)).comp (pineSureL (Ψ i j s) (AxisKeyL h u v s)))
    intro p
    refine (DenseEdgeL (K:=ae (P.pillars 3)) (fun x=>A x p) (fun x=> S x p) (fun x=> AgitateWestL (P.privateH x) R U _ (westBlueL _ p.property)) (fun x=> (AgitateWestL (P.privateH x) R U _ (westBlueL _ (Y p).property)).comp (followΚL t _)) ?_).mono fun x y=> funext y
    intro F; filter_upwards [FoldGlamorL R G t (FreightMars.symm∘ F) U J0 f E Z h u v s _ p.property] with x e; unfold S A; rw [hu]; exact e
 filter_upwards [e] with x e p V F; have ht:= congr_fun (e ⟨p,V⟩) (FreightMars ∘ F); change A x _ _ = A x _ _ at ht; unfold A at ht; rw[hu,show FreightMars.symm ∘ (FreightMars∘ F)=F from funext fun i=> FreightMars.symm_apply_apply _] at ht; exact ht
lemma GlamorAllL {a i j:Axis}(h:i≠j)(u:a≠i)(v:a≠j)(n:ℕ):∀ᵐ x∂P.pillars 3,∀ (s:ℝ)(p:Points n), p∈ westL n a→ ∀ F:Fin n→ΧiMars, CoralL (P.privateH x) R F p= CoralL (P.privateH x) R (compassPiMars t (Ψ i j s) ∘ F) (motionMoonMars (Ψ i j s) p):=by
 filter_upwards [eventually_countable_forall.mpr (fun l:ℕ=> GlamorL R G t U J0 f E Z h u v (denseSeq ℝ l) n)] with x ht s p V F
 exact congr_fun ((denseRange_denseSeq ℝ).equalizer continuous_const (ballasteL (P.privateH x) R t F U h u v p V) (funext fun n=> ht n p V F)) s
#print axioms GlamorAllL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
