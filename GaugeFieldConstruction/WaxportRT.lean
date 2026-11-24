import GaugeFieldConstruction.PearlRT
/-!
 # Fx(t). slope hF ext derivative side commute and Z cost. hold on Fleck.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface PortRT Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable (T:Axis→Axis→ S.Union)(e:MintDΛ (X:=X) T)(p:X.FullBody F)
variable (V:Fin n→S.Union)(a:Axis)
variable (f:Space3→ℂ)(hc:ContDiff ℝ ∞ f)(h:HasCompactSupport f)
variable (g:Bool){A:Set (ZSideRt n)}(hA:IsOpen A)(u:MapsTo (fun z:ZSideRt n × Space3=> QchIRt k g z.1 z.2) (A ×ˢ univ) (tube (n+1))){z:ZSideRt n}(hz:z∈A)
noncomputable abbrev PanProjRT(f:Space3→ℂ)(i:Axis)(g:Bool)(z:ZSideRt n):= ∫ x,f x * TapCoreRt (X:=X) k T V a g z i x
local notation "W'"=> PanProjRT (X:=X) k T V a
noncomputable abbrev basisTRt (n:ℕ):ZSideRt n:= (1,0)
noncomputable abbrev SunStrRt (Q :ZSideRt n → ℂ) (z:ZSideRt n):= fderiv ℂ Q z (basisTRt n)
local notation "Orc"=> OriΛTRt (X:=X) k T V a g
local notation "Bx" => CrestRailRt k g f (Orc timeAxis)
local notation "ΔTACT" => TapCoreRt (X:=X) k T V a g
local notation "Υ" => CrestAxisRT (X:=X) k T V a g
include p hc h hA u
lemma PaneBandsRT {l:Space3→ℂ} (x:ZSideRt n)(i:Axis): (∫ v in tsupport l, TPanRt (X:=X) k (TxRT k T V a i) l g x v)= PanProjRT (X:=X) k T V a l i g x:= by
 rw[setIntegral_eq_integral_of_forall_compl_eq_zero]; · rfl
 intro y hy; change l y*_=_; rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
lemma QmapΧRt (K:Set Space3): MapsTo (fun z:ZSideRt n × Space3 => QchIRt k g z.1 z.2) (A ×ˢ K) (tube (n+1)):=fun z b=> @u z ⟨b.1,mem_univ _⟩
lemma hellStarRt (i:Axis) : AnalyticOnNhd ℂ (PanProjRT (X:=X) k T V a f i g) A:=by
 rw [show PanProjRT (X:=X) k T V a f i g = _ from (funext (fun (x:ZSideRt n)=> PaneBandsRT k T p V a f hc h g hA u x i (l:=f))).symm]
 exact TαNormalRT k g f hc.continuous (Orc i) _ (south _) (p.hol _ _) h h.measurableSet (Subset.refl _) (QmapΧRt k p f hc h g hA u (tsupport f)) hA -- tune Qmap auto
lemma ΨCostRT (i:Axis)(x:ZSideRt n)(v:x∈A): Integrable (fun y:Space3=> f y * TapCoreRt (X:=X) k T V a g x i y):= (hc.continuous.mul (continuous_iff_continuousAt.2 fun y=> (NodXRt k T p V a g u v i y).continuousAt)).integrable_of_hasCompactSupport h.mul_right
include hz e
noncomputable abbrev DawnSideRt(g:Bool)(z:ZSideRt n):= ∑ i:Fin 3, PanProjRT (X:=X) k T V a (dxTRt i f) i.castSucc g z
lemma pricedSurgeRT: SunStrRt (PanProjRT (X:=X) k T V a f timeAxis g) z= DawnSideRt (X:=X) k T V a f g z :=by
 let I:=tsupport f; have HE: HasFDerivAt (PanProjRT (X:=X) k T V a f timeAxis g) (∫ x in I,Bx z x) z:=by
    rw [show PanProjRT (X:=X) k T V a f timeAxis g = _ from (funext (fun (x:ZSideRt n)=> PaneBandsRT k T p V a f hc h g hA u x timeAxis (l:=f))).symm]
    exact TαDerivRT k g f hc.continuous _ _ (south _) (ΩanalyticRt k T p V a g _) h h.measurableSet (Subset.refl _) (QmapΧRt k p f hc h g hA u _) hz hA
 unfold SunStrRt; rw [HE.fderiv]; let K (i:Axis) (x:Space3):=f x*Υ z i i x
 have hi : IntegrableOn (Bx z) I:= TeaseTwistRt k g f hc.continuous _ _ (south _) (ΩanalyticRt k T p V a g _) h (Subset.refl _) (QmapΧRt k p f hc h g hA u _) hz
 rw [ContinuousLinearMap.integral_apply hi, show (fun x:Space3=>(Bx z x) (basisTRt n))=K timeAxis from ?_, setIntegral_eq_integral_of_forall_compl_eq_zero]; swap
 · intro x p; rw [image_eq_zero_of_notMem_tsupport p,zero_mul]
 rotate_left -- tune
 · ext1 x; unfold CrestRailRt K CrestAxisRT; simp only [smul_apply,ContinuousLinearMap.comp_apply,basisTRt,χAccountRt, smul_eq_mul]
 have ht(x:Space3): K timeAxis x= -(∑ j:Fin 3,K j.castSucc x):=eq_neg_of_add_eq_zero_right (show (∑ j:Fin 3,K j.castSucc x)+K timeAxis x=0 from by unfold K; rw [← mul_sum,← mul_add,domeXRT k T e p V a g u hz x,mul_zero])
 have hg(i:Axis):Integrable (K i):=(hc.continuous.mul (tempoPRt k T p V a g u hz i i)).integrable_of_hasCompactSupport h.mul_right
 change (∫ x,K timeAxis x)=_; simp_rw [ht]; rw[integral_neg,integral_finsetSum _ (fun i _=>hg i.castSucc),← sum_neg_distrib]; apply sum_congr rfl
 intro i _; rw [show (∫ x,K i.castSucc x)=_ from tierPayXRt k T p V a g f hc h u hz _ _, neg_neg] -- tune
#print axioms pricedSurgeRT
end YM.NSF.Boundary
end
