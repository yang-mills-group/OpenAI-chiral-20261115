import GaugeFieldConstruction.DaymarkRT
/-!
 # Real-time Ward LOCAL flux generalized. Sch distribution on all compact/noncompact joint tests. Choosing true hatch.
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
open YM.Boundary (Joint Test4 Distn Distn.general_open Distn.from_compact)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable (p:Ticket u C)
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, NSF.Boundary.Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hu:F.NonTangentialFree Y)(hv:N.FullBody F)
variable (e: PathUL (TotalStarsMars p) (fun n V x => Z n x V))
variable {n:ℕ}(V:Fin n→ΧiMars)
local notation "Φ_H"=> H.TinCanL ∘ V
local notation "Τh" => TouchMΛ H (N:=N)
local notation "Ξ"=> CoffΜΛ H p
variable (k:Fin n)(a:Axis)(f:ContDiffBump (0:Space3))(y:Heights (n+1))(v:(τNearRT k).Fleck y)(x:Points n)
local notation "Nτ"=> τNearRT k
local notation "Xit"=> TxRT k (Ξ) (Φ_H) a
local notation "Ω" i:max=> ΘOculusRt k y i
variable (Pns:∀ i:Axis,(τNearRT k).Panes N (TxRT k (CoffΜΛ H p) (H.TinCanL ∘ V) a i) y)(sm:∀ i:Axis, (Pns i).sameGround)
local notation "$Ob"=> OrbitRT p H (N:=N) V k a f y
local notation "Yd"=> YardErosRT p H (N:=N) V k a f
variable (J:Bool→ZSideRt n→ℂ)
lemma mantaCapRt (u:$Ob x J): ∃ d:ℝ,0<d ∧ d<f.rIn ∧ (∀ z∈ closedBall x d, OrbitRT p H (N:=N) V k a f y z J) ∧ ∀ (g:Bool)(p':ℝ × PlateTRt n), p'∈CapRiseTRt x d → (YardErosRT p H (N:=N) V k a f J g (LuaιXRt k y g p'.1 p'.2.1 p'.2.2) ∧ SunStrRt (J false) (LuaιXRt k y g p'.1 p'.2.1 p'.2.2)= SunStrRt (J true) (LuaιXRt k y g p'.1 p'.2.1 p'.2.2)):=by
 let X:ℝ × PlateTRt n:=(0,(0,x))
 have he(g:Bool):∀ᶠ z:ℝ × PlateTRt n in 𝓝 X,YardErosRT p H (N:=N) V k a f J g (LuaιXRt k y g z.1 z.2.1 z.2.2)∧ SunStrRt (J false) (LuaιXRt k y g z.1 z.2.1 z.2.2)=SunStrRt (J true) (LuaιXRt k y g z.1 z.2.1 z.2.2):=by
    have hp:Tendsto (fun z:ℝ×PlateTRt n=>LuaιXRt k y g z.1 z.2.1 z.2.2) (𝓝 X) (𝓝 (ΛArchRt k x y)):= by rw [← LuaZeroRt k y g x]; exact (ContLuaRt k y g).tendsto X
    filter_upwards [hp.eventually u] with z hz; exact ⟨hz.1 g,hz.2⟩
 obtain ⟨r,t,h⟩:=Metric.nhds_basis_closedBall.mem_iff.mp (eventually_all.mpr he)
 obtain ⟨d,hd,hD⟩:=Metric.nhds_basis_closedBall.mem_iff.mp (orbitPersistsRt p H V k a f y x J u)
 let w:=min (min (f.rIn/2) r) d; refine ⟨w,lt_min (lt_min (half_pos f.rIn_pos) t) hd, ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (half_lt_self f.rIn_pos), fun z p=> hD (closedBall_subset_closedBall (min_le_right _ _) p),fun g x' hp=>?_⟩
 unfold CapRiseTRt at hp; rw [closedBall_prod_same] at hp; exact (h (closedBall_subset_closedBall (show w ≤ r from le_trans (min_le_left ..) (min_le_right ..)) hp)) g -- tune
noncomputable abbrev HatchFluxRT (h:Axis→Test4): Distn (Points n):= -(ΛSignXRt a) • ∑ i:Axis, (CtimeRt (B:=D) (Y:=Y) k (CoffΜΛ H p) (H.TinCanL ∘ V) a y i) ∘L χTestRT k (h i)
noncomputable abbrev PTΘRT : Distn (Points n):= -(partialXRT (B:=D) (Y:=Y) (H.TinCanL ∘ V) (dawn (αVertRT k y)) ∘L DriftΛL (NSF.Points.direction k a))
variable (h:Axis→Test4)(b:Test4)(wB:HatchRT b h)
variable (m:(D (n+1)).Modified)(fm:∀ i:Axis, (Pns i).Forms)
lemma ΘhatchValueRT (τ:Joint n): HatchFluxRT p H (Y:=Y) (D:=D) V k a y h τ= -(ΛSignXRt a) * ∑ i:Axis,LambdaStampRT (B:=D) (Y:=Y) k (CoffΜΛ H p) (H.TinCanL ∘ V) a y τ (h i) i:=by simp only [HatchFluxRT, ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,smul_eq_mul]
include G hz hv e v m wB Pns sm fm
local notation "$Fl"=> HatchFluxRT p H (Y:=Y) (D:=D) V k a y
local notation "Θk"=> PTΘRT H (Y:=Y) (D:=D) V k a y
lemma pointFuelRT (x:Points n):∃ r:ℝ,0<r∧∀ τ:Joint n, tsupport τ ⊆ ball x r → HasCompactSupport ⇑τ → (HatchFluxRT p H (Y:=Y) (D:=D) V k a y h- PTΘRT H (Y:=Y) (D:=D) V k a y) τ=0:=by
 let f : ContDiffBump (0:Space3):=⟨1,2,by norm_num,by norm_num⟩
 obtain ⟨J,U⟩:= licensedΛRT p H G hz hv e V k a f y x Pns sm
 obtain ⟨r,hR,t,h',W⟩:= mantaCapRt p H V k a f y x J U
 let B:= acornRt r hR; have hB: B.rOut<r:=half_lt_self hR
 refine ⟨r,hR,fun τ q z=>sub_eq_zero.mpr (show $Fl h τ= Θk τ from ?_)⟩
 rw[ΘhatchValueRT, pricesSteadyRt k (Ξ) (PureConsΛL p H G hz hv e) hv m (Φ_H) a y v (fun i=> NearPair.Panes.forgets _ (sm i) (fm i)) h (αWarmRt B f) b (padRt B f) wB (BornUnderRT B f (hB.trans t)) τ z, paidTuitionRT p H G hz hv e V k a f y v _ Pns sm J B τ _ hR hB.le (q.trans ball_subset_closedBall) W h' m]
 let w:= N.emit (Φ_H); let d:= NSF.Points.direction k a; let Lχ:=dawn (αVertRT k y); have u:Lχ∈fields n:=etched (ΘDawnsRt _ _ v)
 change (∫ x', MintSpΛ w d (glow x' Lχ)*τ x')= -(_); rw [FeeΛSpL u w (hv.hol _ _) τ d z]; exact congrArg Neg.neg (hv.builds _ (Φ_H) Lχ u (DriftΛL d τ)).symm -- tune let H shadow
lemma mantaCurrentRT: HatchFluxRT p H (Y:=Y) (D:=D) V k a y h=PTΘRT H (Y:=Y) (D:=D) V k a y:=by
 rw [← sub_eq_zero]; ext1 τ; let W:= $Fl h- Θk; change W τ=0
 refine ((Distn.general_open W isOpen_univ).2 ?_) τ (subset_univ _)
 apply Set.disjoint_left.mpr; intro x _ ht; obtain ⟨r,t,h⟩:= pointFuelRT p H G hz hv e V k a y v Pns sm h b wB m fm x; exact ((mem_dsupport_iff_not_isVanishingOn x).mp ht _ (mem_ball_self t) isOpen_ball) ((Distn.from_compact W).2 h)
#print axioms mantaCurrentRT
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
