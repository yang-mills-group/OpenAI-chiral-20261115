import GaugeFieldConstruction.EclipseTRt
/-!
 # Fleck. propagate monitor. This proves all flavours H neighbours as same scale. Relative at each observer x real chart height tie.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)(y:Heights (n+1))(v:(τNearRT k).Fleck y)
include v in
lemma ΘDawnsRt: αVertRT k y ∈ east n:=by
 intro i j h; apply v.willing.2 (k.castSucc.succAbove i) (k.castSucc.succAbove j) (k.castSucc.strictMono_succAbove h); exact Or.inl (k.castSucc.succAbove_ne i)
-- OOPS v include.
noncomputable abbrev ΘOculusRt (x:Points n):= glow x (dawn (αVertRT k y))
include v in
lemma ΘSentRt (x:Points n): ΘOculusRt k y x∈tube n:= by apply roseΛ; exact etched (ΘDawnsRt k y v)
-- Pen+ const
lemma ΘArchCapeRt : ΘOculusRt k y = fun x:Points n=>penΛ n x + I • penΛ n (dawn (αVertRT k y)) := by
 ext1 x; ext1 i; simp [ΘOculusRt,penΛ,glow,mul_comm] -- tune
lemma ΘArchARt (x:Points n):AnalyticAt ℝ (ΘOculusRt k y) x:=by
 rw [ΘArchCapeRt]; exact ((penΛ n).analyticAt x).add analyticAt_const -- tune
#print axioms ΘArchARt
noncomputable abbrev ΘManRt (k:Fin n)(y:Heights (n+1)): Points n:= place 0 (αVertRT k y)
lemma ΘMoodRt: wickSlice n (ΘManRt k y)=ΘOculusRt k y 0:=by
 rw [wick_glow]; simp only [ΘManRt,readings_place]; congr 1; ext1 i; refine Mink.ext_by ?_ ?_ <;> simp [NSF.Boundary.trace,place]
include v in
lemma ΘRideRt: ΘManRt k y ∈ ordered n:=by change readings (ΘManRt k y) ∈ east n; rw [ΘManRt, readings_place]; exact ΘDawnsRt k y v
lemma LoomAtRt (p:Points n)(u:p∈ordered n):∀ᶠ t:ℝ in 𝓝 0,∀ j,j≠k → t < |time (p j)-time (p k)| :=by
 refine eventually_all.mpr (fun j=>?_); by_cases h:j=k
 · exact Eventually.of_forall fun x H=> (H h).elim
 exact (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr (fun e=> h ((show StrictMono (readings p) from u).injective e))))).mono fun i w _=> w
noncomputable abbrev acornRt (d:ℝ)(h:0<d):ContDiffBump (0:ℝ):=⟨(d/2)/2,d/2,half_pos (half_pos h),half_lt_self (half_pos h)⟩
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 Metric PortRT
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
local notation "Oreal" i:max=> ΘOculusRt k y i
abbrev OrbitRT (y:Heights (n+1))(x:Points n)(J:Bool → ZSideRt n →ℂ): Prop:= ∀ᶠ z in 𝓝 (ΛArchRt k x y), (∀ g:Bool,YardErosRT p H (N:=N) V k a f J g z) ∧ SunStrRt (J false) z= SunStrRt (J true) z
variable (Pns:∀ i:Axis,(τNearRT k).Panes N (TxRT k (CoffΜΛ H p) (H.TinCanL ∘ V) a i) y)(sm:∀ i:Axis, (Pns i).sameGround)
local notation "$Ob"=> OrbitRT p H (N:=N) V k a f y
include Pns sm hz hv e G
lemma licensedΛRT :∃ J: Bool → ZSideRt n→ℂ, OrbitRT p H (N:=N) V k a f y x J:=by
 obtain ⟨J,Q,q,W⟩:= VestAuraRT k (Ξ) (PureConsΛL p H G hz hv e) hv (Φ_H) a x y Pns sm (φInXRt f) (ofRealCLM.contDiff.comp f.contDiff) (f.hasCompactSupport.comp_left (g:=ofRealCLM) (map_zero _)) (by filter_upwards [f.eventuallyEq_one] with x hx; change (f x:ℂ)=1; simp [show f x=1 from hx])
 have h(g:Bool): ∀ᶠ z in 𝓝 (ΛArchRt k x y), YardErosRT p H (N:=N) V k a f J g z:=by
    obtain ⟨he,a',v,h⟩:= W g; filter_upwards [he.eventually_analyticAt,eventually_nhdsWithin_iff.1 a',eventually_nhdsWithin_iff.1 v,h, roomXRt k x y ((Pns 0).permitted) g] with z u t q' i r; exact ⟨u, fun p'=>⟨r p',t p',i.trans (q' p').symm⟩⟩
 exact ⟨J,(eventually_all.mpr h).and ((W false).2.2.2.trans (W true).2.2.2.symm)⟩
omit e G hv hz sm Pns
noncomputable abbrev OrbitCostRT (a:Axis)(J:Bool→ ZSideRt n→ℂ)(z: ZSideRt n):= ΛSignXRt a * (J false z-J true z)
local notation "Yd"=> YardErosRT p H (N:=N) V k a f
variable (J:Bool→ZSideRt n→ℂ)
lemma orbitEqRt (W:Bool→ZSideRt n→ℂ)(t:$Ob x J)(w:$Ob x W)(g:Bool):J g (ΛArchRt k x y)= W g (ΛArchRt k x y):= by
 haveI := litCloseRt k x y g; let B:= 𝓝[ΛLitRT n g] (ΛArchRt k x y)
 have he: J g =ᶠ[B] W g:=by filter_upwards [t.filter_mono nhdsWithin_le_nhds,w.filter_mono nhdsWithin_le_nhds,@self_mem_nhdsWithin (ZSideRt n) _ (ΛArchRt k x y) (ΛLitRT n g)] with z a b c; exact ((((a.1 g).2 c).2).1.trans ((b.1 g).2 c).2.1.symm)
 exact tendsto_nhds_unique_of_eventuallyEq (((mem_of_mem_nhds t).1 g).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (((mem_of_mem_nhds w).1 g).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) he
-- base local germ proof
include G hz hv e v
lemma yardAtRT (x:Points n)(t:x∈NSF.Work.C20.ordered n)(w:∀ᶠ z: ZSideRt n in 𝓝 (0,wickSlice n x),∀ g,YardErosRT p H (N:=N) V k a f J g z): TouchMΛ H (N:=N) V k a (wickSlice n x)= OrbitCostRT a J (0,wickSlice n x):=by
 let T(s:ℝ):=PαXRT s (wickSlice n x); have hu:Tendsto T (𝓝 0) (𝓝 (0,wickSlice n x)):=by simpa [T,PαXRT] using ((show Continuous T from (continuous_ofReal.mul continuous_const).prodMk continuous_const).tendsto 0)
 obtain ⟨d,r,i⟩:= Metric.nhds_basis_closedBall.mem_iff.mp ((hu.eventually w).and (LoomAtRt k x t))
 have hd:d∈closedBall (0:ℝ) d:=by simp [abs_of_pos r]
 let B:= acornRt d r; have hB:B.rOut<d:= half_lt_self r
 refine FloodTrueRT p H G hz hv e V k a B f x (?_) t J d hB (fun g s v=> (i (show s∈closedBall 0 d by simpa using (abs_le.mpr v))).1 g) -- tune metre
 exact ΦinhaleRt B f k x (ΜConfΛL t) (fun j l p=>not_le.mpr (hB.trans ((i hd).2 j l)) (by simpa using p))
lemma UnderScriptRt (Jx:OrbitRT p H (N:=N) V k a f y 0 J): TouchMΛ H (N:=N) V k a =ᶠ[𝓝 (ΘOculusRt k y 0)] fun o=> OrbitCostRT a J (0,o):=by
 rw [← ΘMoodRt]
 let q:=ΘManRt k y; let U:= TouchMΛ H (N:=N) V k a; let j:=fun o=> OrbitCostRT a J (0,o)
 have ho : (0,wickSlice n q)= ΛArchRt k 0 y:= Prod.ext rfl (ΘMoodRt k y)
 have h (g:Bool): AnalyticAt ℂ (J g) (0,wickSlice n q):=ho.symm ▸ ((mem_of_mem_nhds Jx).1 g).1
 have hc:Continuous fun x: Points n=>((0:ℂ),wickSlice n x):=continuous_const.prodMk (wickSlice n).continuous
 apply complex_germ (ΥFeelΛL H hv _ _ _ _ (wick_tube (ΘRideRt k y v))) (analyticAt_const.mul (((h false).sub (h true)).comp (analyticAt_const.prod analyticAt_id))) (wick_span n); intro m
 apply EventuallyEq.eq_of_nhds (x:=ΘManRt k y) ((show U ∘ wickSlice n =ᶠ[𝓝 q] j ∘ wickSlice n from ?_).iteratedFDeriv ℝ m) -- tune
 have ht: ∀ᶠ x in 𝓝 q, ∀ᶠ z: ZSideRt n in 𝓝 (0,wickSlice n x),∀ g:Bool,Yd J g z:=by
    refine (hc.tendsto q).eventually (p:=fun z:ZSideRt n=>∀ᶠ z in 𝓝 z,∀ g:Bool,Yd J g z) ?_; rw[ho]; exact (eventually_eventually_nhds.mpr (Jx.mono fun z a=>a.1)) -- tune
 filter_upwards [ht, (ordered_open n).mem_nhds (ΘRideRt k y v)] with q h t; exact yardAtRT p H G hz hv e V k a f y v J _ t h
#print axioms UnderScriptRt
omit G e v hz hv
lemma orbitPersistsRt (Jx:$Ob x J): ∀ᶠ x in 𝓝 x,OrbitRT p H (N:=N) V k a f y x J:= ((analyticAt_const.prod (ΘArchARt k y x)).continuousAt.tendsto (f:=fun x=>(ΛArchRt k x y))).eventually (eventually_eventually_nhds.2 Jx) -- tune
include Pns sm e G v hz hv
lemma GlobeTRT (h:OrbitRT p H (N:=N) V k a f y x J): TouchMΛ H (N:=N) V k a (ΘOculusRt k y x)= OrbitCostRT a J (ΛArchRt k x y):=by
 choose W w using fun x => licensedΛRT p H G hz hv e V k a f y x Pns sm
 let D(x:Points n):= OrbitCostRT a (W x) (ΛArchRt k x y); let Hx:= TouchMΛ H (N:=N) V k a ∘ (ΘOculusRt k y)
 have he(R: Bool→ZSideRt n→ℂ)(x:Points n)(o:$Ob x R): D =ᶠ[𝓝 x] fun y'=> OrbitCostRT a R (ΛArchRt k y' y):=by
    filter_upwards [orbitPersistsRt _ H V k a f y x R o] with z t; unfold D OrbitCostRT; rw [orbitEqRt _ H V k a f y z (W z) R (w z) t false, orbitEqRt _ H V k a f y z (W z) R (w z) t true]
 have ht: AnalyticOnNhd ℝ D Set.univ:=by
    intro x _; let B:= W x; have hv(g:Bool): AnalyticAt ℂ (B g) (ΛArchRt k x y):=((mem_of_mem_nhds (w x)).1 g).1
    have hh: AnalyticAt ℝ (OrbitCostRT a B ∘ fun z=> ΛArchRt k z y) x:= by
       refine AnalyticAt.comp ?_ ((analyticAt_const.prod (ΘArchARt k y x)))
       exact (show AnalyticAt ℂ (OrbitCostRT a B) (ΛArchRt k x y) from analyticAt_const.mul ((hv false).sub (hv true))).restrictScalars
    exact hh.congr (he B x (w x)).symm
 have hh: AnalyticOnNhd ℝ Hx Set.univ :=fun x _=> ((ΥFeelΛL H hv V k a _ (ΘSentRt k y v x)).restrictScalars).comp (ΘArchARt k y x)
 have hn:Hx =ᶠ[𝓝 (0:Points n)] D:= ((UnderScriptRt p H G hz hv e V k a f y v (W 0) (w 0)).comp_tendsto ((ΘArchARt k y 0).continuousAt.tendsto)).trans (he (W 0) 0 (w 0)).symm
 exact ((hh.eqOn_of_preconnected_of_eventuallyEq ht isPreconnected_univ (Set.mem_univ _) hn) (Set.mem_univ x)).trans (he J x h).eq_of_nhds
#print axioms GlobeTRT
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
