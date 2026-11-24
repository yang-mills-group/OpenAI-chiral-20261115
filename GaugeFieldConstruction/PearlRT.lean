import GaugeFieldConstruction.ClaudeRT
/-!
 # D^0 stress boundary slit relation by spatial-only integration. h_± slopes BOTH attached to same radial pressure. interior. Derivative complex variable t.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface PortRT Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
local notation "Z"=>ZSideRt n
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable (T:Axis→Axis→ S.Union)(e:MintDΛ (X:=X) T)(p:X.FullBody F)
variable (V:Fin n→S.Union)(a:Axis)(g:Bool)
noncomputable abbrev OriΛTRt (j:Axis):=X.emit (CabinTRt k (TxRT k T V a j) g)
local notation "Q_m"=> QchIRt k g
local notation "Hτ"=> OriΛTRt (X:=X) k T V a g
noncomputable abbrev CrestAxisRT (z:ZSideRt n)(j i:Axis)(u:Space3):= fderiv ℂ (OriΛTRt (X:=X) k T V a g j) (QchIRt k g z u) (realDirΛ (dayRT k g) i)
local notation "Ωrt"=> CrestAxisRT (X:=X) k T V a g
variable (f:Space3→ℂ)(hc:ContDiff ℝ ∞ f)(h:HasCompactSupport f)
variable {A:Set (ZSideRt n)}(hA:IsOpen A)(u:MapsTo (fun z:ZSideRt n × Space3=> QchIRt k g z.1 z.2) (A ×ˢ univ) (tube (n+1))){z:ZSideRt n}(hz:z∈A)
include p
lemma ΩanalyticRt (i:Axis): AnalyticOnNhd ℂ (OriΛTRt (X:=X) k T V a g i) (tube (n+1)):= p.hol _ _
include u hz
omit p in
lemma curveLitΓRt (x:Space3):QchIRt k g z x∈tube (n+1):= @u (z,x) ⟨hz,mem_univ _⟩
noncomputable abbrev TapCoreRt (z:ZSideRt n)(i:Axis) : Space3→ℂ:= OriΛTRt (X:=X) k T V a g i ∘ QchIRt k g z
lemma tempoPRt(i j:Axis): Continuous (CrestAxisRT (X:=X) k T V a g z i j):=continuous_iff_continuousAt.2 (fun x=> ((((ΩanalyticRt k T p V a g i _ (curveLitΓRt k g u hz x)).fderiv.continuousAt).comp (f:=QchIRt k g z) (show ContinuousAt (QchIRt k g z) x from ((χTintRt k g).comp (continuous_const.prodMk continuous_id)).continuousAt)).clm_apply continuousAt_const))
lemma NodXRt (i:Axis)(x:Space3): HasFDerivAt (TapCoreRt (X:=X) k T V a g z i) ((fderiv ℂ (OriΛTRt (X:=X) k T V a g i) (QchIRt k g z x)).restrictScalars ℝ ∘L BarcoRT k g) x:= by
 refine (((p.hol _ (CabinTRt k (TxRT k T V a i) g) _ (@u (z,x) ⟨hz,mem_univ x⟩)).differentiableAt.hasFDerivAt).restrictScalars ℝ).comp x ?_
 simp_rw [funext fun x=>analyticBarRT k g x z]; exact (BarcoRT k g).hasFDerivAt.const_add _
include e
lemma domeXRT (x:Space3):(∑ j:Fin 3,CrestAxisRT (X:=X) k T V a g z j.castSucc j.castSucc x)+ CrestAxisRT (X:=X) k T V a g z timeAxis timeAxis x=0:=by
 change _ + Ωrt z (Fin.last 3) (Fin.last 3) x =_; rw [← Fin.sum_univ_castSucc (f:=fun i=> Ωrt z i i x)]; unfold CrestAxisRT OriΛTRt
 cases g <;> simp only [CabinTRt,Bool.false_eq_true,↓reduceIte]
 · simp_rw [reverseTxRt]; exact e (n+1) _ k.castSucc a _ (curveLitΓRt k false u hz _)
 simp_rw [flipTxRt]; exact e (n+1) _ k.succ a _ (curveLitΓRt k true u hz _)
omit e
noncomputable abbrev dxTRt (j:Fin 3)(f:Space3→ℂ)(x:Space3):= fderiv ℝ f x (skyIRT j)
include h hc
lemma tierPayXRt (i: Axis)(j: Fin 3): (∫ x, f x * CrestAxisRT (X:=X) k T V a g z i j.castSucc x)= -(∫ x, dxTRt j f x* TapCoreRt (X:=X) k T V a g z i x):=by
 let M:= TapCoreRt (X:=X) k T V a g z i
 have kχ(x):fderiv ℝ M x (skyIRT j)= Ωrt z i j.castSucc x := by
    unfold CrestAxisRT; rw[(NodXRt k T p V a g u hz i x).fderiv, ContinuousLinearMap.comp_apply,χUpwardRT]; rfl
 have eM: Continuous M:= continuous_iff_continuousAt.2 fun x=> (NodXRt k T p V a g u hz i x).continuousAt
 have hd: Integrable (fun x=> f x*fderiv ℝ M x (skyIRT j)):=by simp_rw [kχ]; exact (hc.continuous.mul (tempoPRt _ _ p _ _ _ u hz _ _)).integrable_of_hasCompactSupport h.mul_right
 have pu: Continuous fun x=> fderiv ℝ f x (skyIRT j):= (hc.continuous_fderiv (by simp)).clm_apply continuous_const
 have hχ: Integrable (fun x=> fderiv ℝ f x (skyIRT j)*M x):=(pu.mul eM).integrable_of_hasCompactSupport (h.fderiv_apply ..|>.mul_right)
 simp_rw [← kχ]; exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hχ hd ((hc.continuous.mul eM).integrable_of_hasCompactSupport h.mul_right) (fun x _=> hc.differentiable (by simp) x) (fun x _=> (NodXRt _ _ p _ _ _ u hz _ _).differentiableAt)
#print axioms tierPayXRt
end YM.NSF.Boundary
end
