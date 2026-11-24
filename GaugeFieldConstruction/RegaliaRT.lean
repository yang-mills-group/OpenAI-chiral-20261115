import GaugeFieldConstruction.MantaRT
import GaugeFieldConstruction.SymposiumΛL
/-!
 # Universal Ward HATCH. no claim forming unstable global charges; retarded LOCAL.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Analysis MeasureTheory Complex Finset Distribution
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 Metric PortRT
open YM.Boundary (Joint Test4 Distn)
open NSF.LD
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable {R:(SurfRimL A).Rotation}{s:(SurfRimL A).RealSpin}{K:NSF.Boundary.Spins (SurfRimL A)}
variable (U:LoreL F K Y (SurfRimL Z))(Q:K.Descends R s)(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "Φ_H"=> H.TinCanL ∘ V
local notation "Τh" => TouchMΛ H (N:=N)
local notation "Ξ"=> CoffΜΛ H p
variable (k:Fin n)(a:Axis)
local notation "Nτ"=> τNearRT k
local notation "Xit"=> TxRT k (Ξ) (Φ_H) a
variable (h:Axis→Test4)(b:Test4)(wB:HatchRT b h)
noncomputable def CommΘRt (i:Axis): Distn (Points (n+1)):= Y.W (n+1) (TxRT k (CoffΜΛ H p) (H.TinCanL ∘ V) a i)- (τNearRT k).flipW (Y.W (n+1) (TxRT k (CoffΜΛ H p) (H.TinCanL ∘ V) a i ∘ (τNearRT k).s))
noncomputable abbrev FutureHandRT: Distn (Points n):= -(ΛSignXRt a) • ∑ i:Axis, CommΘRt p H (Y:=Y) V k a i ∘L χTestRT k (h i)
local notation "ΘH"=> FutureHandRT p H (Y:=Y)
lemma WorkWatchRT (ι:Joint n):FutureHandRT p H (Y:=Y) V k a h ι= -(ΛSignXRt a)* ∑ i:Axis, CommΘRt p H (Y:=Y) V k a i (χTestRT k (h i) ι):=by simp only [FutureHandRT, ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,smul_eq_mul]
-- issue visit
include G hv Q U
lemma VisitKnownRT: ∃ y:ℕ→Heights (n+1), Tendsto (dawn ∘ y) atTop (𝓝 0)∧ ∀ m:ℕ,(τNearRT k).Fleck (y m) ∧ ∃ N':∀ i:Axis,(τNearRT k).Panes N (TxRT k (CoffΜΛ H p) (H.TinCanL ∘ V) a i) (y m), (∀ i, (N' i).sameGround) ∧ (∀ i,(N' i).Forms):=by
 obtain ⟨y,hy,q⟩:= NSF.Work.C17.answer _ (Nτ)
 refine ⟨y,hy,fun m=>⟨(q m).1,?_⟩⟩
 let N'(i:Axis):=Classical.choice (NSF.Work.C19.answer K Y D F N U.habitat hv R s Q H.RiseFrameL H.PlannerL.toSymmetric (H.RiseKnownL _) (NSF.Work.C18.answer _ _ _ Q) (NSF.Work.C16.answer Y K D N F (glazeL D) U.habitat U.turns hv) _ (Xit i) (Nτ) (y m) (q m).1 (q m).2)
 exact ⟨N',fun i=> NSF.Work.C20.answer H.RiseFrameL F Y D N H.PlannerL.toSymmetric (H.RiseKnownL A) G.PlannerL.toSymmetric G.LagoonL (fun i=> le_of_eq ((H.FlagsL i).trans (G.FlagsL i).symm)) U.heat hv _ (Xit i) _ (Nτ) (N' i), fun i=> NSF.Work.C21.answer F Y D N (glazeL D) hv _ (Xit i) _ (Nτ) (N' i)⟩
include wB e
lemma REALΛRT : RotateCostΛL H Y V k a=FutureHandRT p H (Y:=Y) V k a h:=by
 ext1 τ
 obtain ⟨y,t,hx⟩:= VisitKnownRT p H G U Q hv V k a
 let T(m:ℕ):= ΘOculusRt k (y m) 0; let Bf (i:Axis)(m:ℕ):= LambdaStampRT (B:=D) (Y:=Y) k (Ξ) (Φ_H) a (y m) τ (h i) i
 have he(m:ℕ): PTΘRT H (Y:=Y) (D:=D) V k a (y m) τ= -(ΛSignXRt a)*∑ i:Axis, Bf i m:=by
    obtain ⟨J,p',e'⟩:=(hx m).2; rw [← mantaCurrentRT p H G U.heat hv e V k a (y m) (hx m).1 J p' h b wB (glazeL ..) e']; exact ΘhatchValueRT ..
 have ht:Tendsto (dawn ∘ y) atTop (𝓝[shores (n+1)] 0):= tendsto_nhdsWithin_iff.2 ⟨t, Eventually.of_forall fun m=>(hx m).1.here⟩
 have hu:Tendsto (fun m:ℕ=> dawn (αVertRT k (y m))) atTop (𝓝[shores n] 0):=by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m=> warmer _ (etched (ΘDawnsRt k (y m) (hx m).1))⟩
    let S:= (fun x:Points (n+1)=> (TulipΛL k.castSucc).symm x|>.2)
    have hc:Continuous S:=continuous_snd.comp (TulipΛL k.castSucc).symm.continuous; have hZ:S 0=0:=by unfold S; simp
    rw [← hZ]; exact (hc.tendsto 0).comp t -- tune
 have hp : Tendsto (fun m:ℕ=>PTΘRT H (Y:=Y) (D:=D) V k a (y m) τ) atTop (𝓝 ((RotateCostΛL H Y V k a) τ)):=by
    have p:= ((D n).tends (glazeL ..) (Y.W n (Φ_H)) (DriftΛL (NSF.Points.direction k a) τ) 0 (flat n)).tendsto.comp hu
    rw[(D n).flatD (glazeL D n) (U.habitat n _)] at p; exact p.neg
 have H'(i:Axis): Tendsto (Bf i) atTop (𝓝 (CommΘRt p H (Y:=Y) V k a i (χTestRT k (h i) τ))):=by
    let V:=Xit i; let Z:=χTestRT k (h i) τ
    have hp:= ((D (n+1)).tends (glazeL ..) (Y.W _ V) Z 0 (flat _)).tendsto.comp ht
    have hu:= ((D (n+1)).tends (glazeL ..) (Y.W _ (V ∘ (Nτ).s)) (YM.Boundary.Probe.along (Nτ).switch.toContinuousLinearEquiv Z) 0 (flat _)).tendsto.comp ht
    rw [(D (n+1)).flatD (glazeL ..) (U.habitat _ _)] at hp hu
    refine (hp.sub hu).congr fun z=>?_
    dsimp only [Function.comp_apply]; unfold Bf LambdaStampRT CtimeRt νRT μRT; simp only [sub_apply,heightTieRT k (y z) (hx z).1]; rfl
 rw [WorkWatchRT]; exact tendsto_nhds_unique_of_eventuallyEq hp (Tendsto.const_mul (-(ΛSignXRt a)) (tendsto_finsetSum _ fun i _=> H' i)) (Eventually.of_forall he) -- order
#print axioms REALΛRT
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
