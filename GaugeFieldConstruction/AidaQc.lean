import GaugeFieldConstruction.DulceeQc
/-!
# Repayment contour comparison. No distro-cutoff ambiguity. Shell support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Salam
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Metric
open scoped Topology BigOperators ContDiff Classical
variable {n : ℕ} {b : Bulb}{p : Test (n+1)}{a:Bulb} (h:Works b p 0)(q:RespectQc p a)
lemma slipDerQc (x:Points (n+2))(i:Axis): tilt (direction 0 i) (PokerQc b p a h q) x = (D (basis i) b.f (helm x) - D (basis i) a.f (LengthQc x)) • p (riders x):=by
 rw [tilt_pays]; change fderiv ℝ (((b.f ∘ (helm (n:=n+1)))-(a.f ∘ (LengthQc (n:=n)))) • (p ∘ riders)) x _ = _
 have hb:= b.d.differentiable (by simp) (helm x); have ha:= a.d.differentiable (by simp) (LengthQc x); have hp:=diffT p (riders x)
 rw[fderiv_smul ((hb.comp _ helm.differentiableAt).sub (ha.comp _ LengthQc.differentiableAt)) (hp.comp x riders.differentiableAt),fderiv_sub (hb.comp x helm.differentiableAt) (ha.comp x LengthQc.differentiableAt), fderiv_comp _ hb helm.differentiableAt,fderiv_comp _ ha LengthQc.differentiableAt, fderiv_comp _ hp riders.differentiableAt]
 rw [ContinuousLinearMap.fderiv,ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
 simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,on_left,head_on,LengthCostQc,map_zero, smul_zero,zero_add]; rfl
-- Δ_K via tilted version. Late cut tests.
noncomputable def YoungQc (K:Payroll (n+1))(i j:Axis):Test (n+2):=testcut K p b h.cared i j - weigh (K.K j) (K.sm j) (tilt (direction 0 i) (PokerQc b p a h q)) -- h q params invisible need bind
lemma YoungCostQc (K:Payroll (n+1))(i j:Axis)(x:Points (n+2)):YoungQc h q K i j x=(K.K j x * D (basis i) a.f (LengthQc x)) • p (riders x):=by
 change testcut _ _ _ _ _ _ x - weigh _ (K.sm j) _ x=_; rw [scalar,slipDerQc,testcut_v]; rw [smul_smul,mul_sub,mul_comm (D (basis i) b.f (helm x)),sub_smul,sub_sub_cancel] -- tune
lemma ShadowQc (A:Variation (n+1))(c:Conserves A) (K:Payroll (n+1)) : (∑ i:Axis, ∑ j:Axis,A i j (YoungQc h q K i j))= delta K p b h.cared A:=by
 unfold YoungQc delta; simp_rw [map_sub, Finset.sum_sub_distrib]; suffices T: (∑ i:Axis,∑ j:Axis,A i j (weigh (K.K j) (K.sm j) (tilt (direction 0 i) (PokerQc b p a h q))))=0 by rw [T,sub_zero]
 let t:=PokerQc b p a h q
 let T(i j:Axis):= weigh (D (direction 0 i) (K.K j)) (DG _ (K.sm j) _) t; let w(i j):=A i j (T i j)
 have ht (a b:Axis): T a b= - T b a:=by ext1 x; change D (direction 0 a) (K.K b) x • (t x:ℂ)= -(D (direction 0 b) (K.K a) x • (t x:ℂ)); rw [K.skew,neg_smul] -- tune
 have he(i j:Axis): w j i= - w i j:=by unfold w; rw [c.maps,ht,map_neg]
 have L (j): (∑ i:Axis,A i j (weigh (K.K j) (K.sm j) (tilt (direction 0 i) t)))= - ∑ i:Axis, w i j:=by
    have u:=c.withdraw (weigh _ (K.sm j) t) j; simp_rw [weight_deriv,map_add,Finset.sum_add_distrib] at u; exact eq_neg_of_add_eq_zero_right u -- tune
 rw [Finset.sum_comm]; simp_rw [show PokerQc b p a h q=t from rfl,L,Finset.sum_neg_distrib,opposite _ he,neg_zero] -- tune
-- payroll transport shape K
structure TwistQc (K:Payroll (n+1))(m:ℕ)(L:Axis→ E4→ℝ) :Prop where
   expense:∀ j,Continuous (L j)
   flux:∀ j:Axis,∀ e:ℝ,∀ y:E4,∀ x:Points (n+1), K.K j (LensQc (e • y) x)=e^m * L j y
lemma ToastQc (i:Axis): TwistQc (ticket i) (n:=n) 0 (fun j _=>basis i j):= ⟨fun _=> continuous_const,fun _ _ _ _=>(one_mul _).symm⟩
def TurnyQc (Ω:Ortho.Skew)(i:Axis):E4→L[ℝ] ℝ:= Payroll.proj i ∘L turn Ω
lemma TackQc (Ω:Ortho.Skew): TwistQc (desk 0 Ω) (n:=n) 1 (fun i=>TurnyQc Ω i):= by
 refine ⟨fun i=>(TurnyQc ..).continuous,?_⟩
 intro j e y x
 change TurnyQc _ _ (LengthQc (LensQc ..))= _
 unfold LensQc; rw [lengthBpQc]; rw [show head x=x 0 from rfl,add_sub_cancel_left,map_smul,pow_one]; rfl
lemma TallonQc {e:ℝ}(v:0<e){i j:Axis}{m:ℕ}{L}{K:Payroll (n+1)}(p':RespectQc p (dockScaleQc e v))(r:TwistQc K m L)(y:E4)(x:Points (n+1)): YoungQc h p' K i j (LensQc (e • y) x) = (e⁻¹*e^m) • ((L j y * D (basis i) DokiQc.f y) • p x):=by
 rw [YoungCostQc,r.flux]; unfold LensQc; rw [lengthBpQc,dockCostQc, Prod.mk.inj (helm_consQ _ _)|>.2]; rw [show head x=x 0 from rfl,add_sub_cancel_left, inv_smul_smul₀ v.ne',smul_smul]; congr 1; ring
#print axioms ShadowQc
#print axioms TallonQc
end YM.GaugeFieldConstruction.Fathom.Salam
