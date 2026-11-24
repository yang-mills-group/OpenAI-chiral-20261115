import GaugeFieldConstruction.FlashworkRT
/-!
 # Sum of shutter and contour FORE, ret shell on genuine partial product(W) as distributions. independence.RiskSigns.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)(y:Heights (n+1))(v:(τNearRT k).Fleck y)(x:Points n)
local notation "Nτ"=> τNearRT k
lemma κRealCalcRt (o:Full n)(Q:ZSideRt n→ℂ)(s:ℝ)(h:AnalyticAt ℂ Q ((s:ℂ),o)): HasDerivAt (fun t:ℝ=> Q ((t:ℂ),o)) (SunStrRt Q ((s:ℂ),o)) s:=by
 have he:HasDerivAt (fun s:ℝ =>((s:ℂ),o)) (basisTRt n) s:=by
    refine HasDerivAt.prodMk ?_ (hasDerivAt_const s _); convert ofRealCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_id s) using 1 <;> first|rfl|simp
 exact ((h.differentiableAt.hasFDerivAt).restrictScalars ℝ).comp_hasDerivAt s he
variable (J K: ZSideRt n→ℂ)
lemma κEqualCalcRt (r:ℝ)(o:Full n)(u:∀ (s:ℝ),s∈ closedBall (0:ℝ) r → AnalyticAt ℂ J ((s:ℂ),o) ∧ AnalyticAt ℂ K ((s:ℂ),o) ∧ SunStrRt J ((s:ℂ),o)=SunStrRt K ((s:ℂ),o))(s:ℝ)(h:s∈closedBall (0:ℝ) r): J ((s:ℂ),o)-K ((s:ℂ),o)=J (0,o)-K (0,o):=by
 let B(t:ℝ):=J ((t:ℂ),o)-K ((t:ℂ),o)
 have hp(t:ℝ)(p:t∈uIcc (0:ℝ) s): HasDerivAt B 0 t:=by
    obtain ⟨a,q,e⟩:=u t (by
       rw [← segment_eq_uIcc] at p; exact convex_closedBall (0:ℝ) r|>.segment_subset (mem_closedBall_self ((abs_nonneg s).trans (show |s| ≤ r by simpa using h))) h p)
    rw [show (0:ℂ)= SunStrRt J ((t:ℂ),o)-SunStrRt K ((t:ℂ),o) from by rw[e,sub_self]]; exact (κRealCalcRt _ _ _ a).sub (κRealCalcRt _ _ _ q)
 have he:= intervalIntegral.integral_eq_sub_of_hasDerivAt (f':=fun x:ℝ => (0:ℂ)) hp (by simp)
 exact sub_eq_zero.mp (by simpa [B] using he.symm)
#print axioms κEqualCalcRt
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{D:∀ i, Blanket i}
variable (T:Axis→Axis→ S.Union)(V:Fin n→S.Union)(a:Axis)
variable (B:ContDiffBump (0:ℝ))(f:ContDiffBump (0:Space3))(τ:Joint n)
noncomputable abbrev LaminaCostRt (g:Bool):= partialXRT (B:=D) (Y:=Y) (CabinTRt k (TxRT k T V a timeAxis) g) ((PoleIogRt k g) (dawn y)) (MoχRt k g B f τ timeAxis)
lemma CorkValuesRt: (∑ i:Axis,LambdaStampRT (B:=D) (Y:=Y) k T V a y τ (αWarmRt B f i) i)= LaminaCostRt (D:=D) (Y:=Y) k y T V a B f τ false- LaminaCostRt (D:=D) (Y:=Y) k y T V a B f τ true:=by
 rw[sum_eq_single timeAxis]; swap
 · intro i _ p; rw [αWarmRt, if_neg p]; unfold LambdaStampRT; rw [show χTestRT k 0 τ=0 from ?_,map_zero]
   ext1 w; obtain ⟨x,rfl⟩:=(κMoverRT k).surjective w; rw [priceIRT]; simp
 rotate_left; · simp
 unfold LambdaStampRT CtimeRt LaminaCostRt; simp only [ContinuousLinearMap.sub_apply]; congr 1
#print axioms CorkValuesRt
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20 Metric PortRT
open YM.Boundary (Joint)
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
variable (J:Bool→ZSideRt n→ℂ)(B:ContDiffBump (0:ℝ))(τ:Joint n)
local notation "q₀" g:max => PlotLuaTRt k y g (J g) B τ 0
variable (r:ℝ)(t:0<r)(hB:B.rOut≤ r)(q:tsupport τ ⊆ closedBall x r)(w:∀ (g:Bool)(p':ℝ × PlateTRt n), p'∈CapRiseTRt x r→ (YardErosRT p H (N:=N) V k a f J g (LuaιXRt k y g p'.1 p'.2.1 p'.2.2) ∧ SunStrRt (J false) (LuaιXRt k y g p'.1 p'.2.1 p'.2.2)= SunStrRt (J true) (LuaιXRt k y g p'.1 p'.2.1 p'.2.2)))
variable (o:∀ z∈ closedBall x r, OrbitRT p H (N:=N) V k a f y z J)
variable (m:(D (n+1)).Modified)
include w t hB q m hv v
lemma paysFrontRT(g:Bool): LaminaCostRt (D:=D) (Y:=Y) k y (CoffΜΛ H p) (H.TinCanL ∘ V) a B f τ g= (∫ z:PlateTRt n, PlotLuaTRt k y g (J g) B τ 0 z):=by
 refine tendsto_nhds_unique_of_eventuallyEq (cashTRt k y v g hv m (Ξ) (Φ_H) a B f τ) ((MayPenRT k y g (J g) B τ x r t hB q (fun p z=> (w g _ z).1.1)).tendsto.mono_left nhdsWithin_le_nhds) ?_
 filter_upwards [(Eventually.filter_mono nhdsWithin_le_nhds (closedBall_mem_nhds (0:ℝ) t)), self_mem_nhdsWithin] with ε u e
 apply integral_congr_ae; filter_upwards with z; unfold ΡioPaymentRT PlotLuaTRt
 by_cases hp:z∈closedBall ((0:ℝ),x) r
 · exact congrArg (fun x=> PenCostRt B τ z*x) (((w g (ε,z) ⟨u,hp⟩).1.2 (dewierPRt k y g _ _ e _)).2.1.symm)
 rw [show PenCostRt B τ z=0 from image_eq_zero_of_notMem_tsupport (fun e=> hp ((closedBall_prod_same (0:ℝ) x r) ▸ PenCoverRt B τ x r r hB q e)),zero_mul,zero_mul] -- tune
include Pns sm e hz G o
lemma palmTimeΦRt(z:PlateTRt n): -(ΛSignXRt a)* (PlotLuaTRt k y false (J false) B τ 0 z- PlotLuaTRt k y true (J true) B τ 0 z)= -(woolTRt B z.1) * (TouchMΛ H (N:=N) V k a (ΘOculusRt k y z.2)*τ z.2):=by
 unfold PlotLuaTRt; by_cases hp:z∈closedBall ((0:ℝ),x) r; swap
 · rw [show PenCostRt B τ z=0 from image_eq_zero_of_notMem_tsupport (fun e=> hp ((closedBall_prod_same (0:ℝ) x r) ▸ PenCoverRt B τ x r r hB q e)), zero_mul,zero_mul,sub_self,mul_zero]; rw[← closedBall_prod_same] at hp; by_cases v: z.1∈closedBall (0:ℝ) r
   · rw [show τ z.2=0 from image_eq_zero_of_notMem_tsupport (fun e=> hp ⟨v,q e⟩),mul_zero,mul_zero]
   unfold woolTRt; rw [show shutterXRt B z.1=0 from image_eq_zero_of_notMem_tsupport (fun e=> v (closedBall_subset_closedBall hB (shutterWidthRt B e))),ofReal_zero,neg_zero,zero_mul]
 rw [← closedBall_prod_same] at hp
 have he(g:Bool)(s:ℝ)(p':s∈closedBall (0:ℝ) r): Yd J g ((s:ℂ),ΘOculusRt k y z.2) ∧ SunStrRt (J false) ((s:ℂ),ΘOculusRt k y z.2)= SunStrRt (J true) ((s:ℂ),ΘOculusRt k y z.2):=by
    rw[← LuaZRt k y g ..] -- tune order
    exact w g (0,(s,z.2)) ⟨mem_closedBall_self t.le,(closedBall_prod_same (0:ℝ) x r) ▸ ⟨p',hp.2⟩⟩
 have hx:= κEqualCalcRt (J false) (J true) r (ΘOculusRt k y z.2) (fun s z=> ⟨(he false s z).1.1,(he true s z).1.1,(he true s z).2⟩) z.1 hp.1
 rw [LuaZRt,LuaZRt,← mul_sub,hx, GlobeTRT p H G hz hv e V k a f y v z.2 Pns sm J (o _ hp.2)]
 unfold OrbitCostRT woolTRt PenCostRt; congrm(?_); ring -- tune point Defeq
lemma paidTuitionRT : -(ΛSignXRt a)*(∑ i:Axis, LambdaStampRT (B:=D) (Y:=Y) k (CoffΜΛ H p) (H.TinCanL ∘ V) a y τ (αWarmRt B f i) i)=(∫ x':Points n, TouchMΛ H (N:=N) V k a (ΘOculusRt k y x')*τ x') :=by
 rw [CorkValuesRt, paysFrontRT p H hv V k a f y v x J B τ r t hB q w m false,paysFrontRT p H hv V k a f y v x J B τ r t hB q w m true]
 have he(g:Bool): Integrable (PlotLuaTRt k y g (J g) B τ 0):= SitsPenRt k y g (J g) B τ x r t hB q (fun z p=>(w g z p).1.1) _ (mem_closedBall_self t.le)
 rw [← integral_sub (he false) (he true), ← integral_const_mul]; simp_rw [palmTimeΦRt p H G hz hv e V k a f y v x Pns sm J B τ r t hB q w o m]; refine (integral_prod_mul (μ:=volume) (ν:=volume) (fun s=> - woolTRt B s) (fun i=> Τh V k a (ΘOculusRt k y i)*τ i)).trans ?_; rw [integral_neg,woolWeightRt,neg_neg,one_mul] -- tune
#print axioms paidTuitionRT
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
