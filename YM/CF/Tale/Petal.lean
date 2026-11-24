import YM.CF.Tale.Jive
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Tale
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Next Next.Free PhysicalNext.JointLoad Cube SU Exterior Cascade Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable{c f:Side}(M:Lattice.Ratio c f)
open StressFlux AnalyticBridge.VerifiedReset
variable (d':PlaqAxes)(o:Site c)(W:townX c)(s t:Step)
local notation "G"=> SU.group
open Next Next.Fluctuations AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine.Offset
open Heir
abbrev PointB := Fin 4→ SU.group.Color -- step palette
private def plusX (s:Step)(c:SU.group.Color):SU.group.El:= if s.neg then (SU.group.lieExp c)⁻¹ else SU.group.lieExp c -- G dot fix
private def arcF(s t:Step)(x:PointB):SU.group.Color:= SU.group.curvature (plusX s (x 0) * (plusX t (x 1) * (plusX s.rev (x 2) * plusX t.rev (x 3))))
def plume_P (o:Site c)(s t:Step): townX c→L[ℝ] PointB:=
 let f(p:Step)(v:Site c): townX c→L[ℝ] SU.group.Color:=ContinuousLinearMap.proj (p.used v); let x:= o+s.vec; let y:=x+t.vec
 ContinuousLinearMap.pi (![f s o,f t x,f s.rev y,f t.rev (y+s.rev.vec)])
private lemma link_w (U:townX c) (s:Step) : Lattice.Step.read (x:=o) s (increment 1 U)=plusX s (U (s.used o)) :=by unfold Lattice.Step.read plusX; split <;> simp [increment] -- step if syntax
private lemma pressed (s t:Step): (fun x:townX c=> plate (increment 1 x) o s t) = (arcF s t) ∘ (plume_P o s t) :=by funext x; unfold plate arcF; rw [Function.comp_apply, Lattice.oriented]; simp_rw [travel, link_w]; simp only [mul_one]; rfl
private lemma plume_cost : ‖plume_P o s t‖≤1:=by
 refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>(pi_norm_le_iff_of_nonneg (show 0 ≤ 1*‖x‖ by positivity)).mpr (fun i=>?_)); rw [one_mul]; fin_cases i <;> exact norm_le_pi_norm x _
private lemma yacht (s:Step) : ContDiff ℝ (↑(3:ℕ):WithTop ℕ∞) (fun c=>SU.group.mat (plusX s c)):=by
 unfold plusX; split; · simp_rw [Gauge.mat_inv]; exact ((starL' ℝ).contDiff.comp SU.group.exp_jet).of_le le_top
 exact SU.group.exp_jet.of_le le_top
private lemma ζX: ContDiff ℝ (↑(3:ℕ):WithTop ℕ∞) (arcF s t):=by
 unfold arcF Gauge.curvature; let K:= SU.group.projectColor; let a:= K.toContinuousLinearMap; let f(x:PointB):SU.group.Mat:= SU.group.mat (plusX s (x 0) * (plusX t (x 1) * (plusX s.rev (x 2) * plusX t.rev (x 3))))
 have hp : ContDiff ℝ (↑(3:ℕ):WithTop ℕ∞) f:=by unfold f; simp_rw [Gauge.mat_mul]; exact ((yacht _).comp (contDiff_apply ℝ SU.group.Color 0)).mul (((yacht _).comp (contDiff_apply ℝ SU.group.Color 1)).mul (((yacht _).comp (contDiff_apply ℝ SU.group.Color 2)).mul ((yacht _).comp (contDiff_apply ℝ SU.group.Color 3))))
 simp_rw [Gauge.mat_inv]; exact a.contDiff.comp ((hp.sub ((starL' ℝ).contDiff.comp hp)).const_smul (c:= (1/2:ℝ))) -- tune
private lemma earn_x (s t:Step): ∃ M:ℝ,0 ≤ M∧∀ v:PointB,‖v‖≤1 → Through 2 (arcF s t) v M:=by
 let A:=arcF s t; let P(x:PointB):=‖iteratedFDeriv ℝ 0 A x‖ + ‖iteratedFDeriv ℝ 1 A x‖+ ‖iteratedFDeriv ℝ 2 A x‖
 have he(d:ℕ)(h:d≤2):Continuous (fun x=>‖iteratedFDeriv ℝ d A x‖):=((ζX _ _).continuous_iteratedFDeriv (by exact_mod_cast (show d≤3 by omega))).norm
 have ht:Continuous P:=((he 0 (by omega)).add (he 1 (by omega))).add (he 2 (by omega))
 obtain ⟨m,h⟩:= ((isCompact_closedBall (0:PointB) 1).image ht).bddAbove; refine ⟨max m 0, le_max_right ..,fun i k=>⟨((ζX ..).contDiffAt.of_le (Nat.cast_le.mpr (show 2 ≤ 3 by norm_num))),fun d v=>?_⟩⟩
 apply le_trans _ ((h ⟨i,mem_closedBall_zero_iff.mpr k,rfl⟩).trans (le_max_left ..)); interval_cases d <;>change ‖iteratedFDeriv ℝ _ A i‖≤ P i <;>unfold P <;>linarith only [norm_nonneg (iteratedFDeriv ℝ 0 A i),norm_nonneg (iteratedFDeriv ℝ 1 A i),norm_nonneg (iteratedFDeriv ℝ 2 A i)] -- tune
lemma ν_p:∃ M:ℝ,1≤ M∧∀ (c:Side)(o:Site c)(K:PlaqAxes)(v:townX c),‖v‖≤1→ Through 2 (fun x:townX c=> petals (increment 1 x) o K) v M:=by
 let g(v:Axis×Bool):Step:=⟨v.1,v.2⟩; letI:=Fintype.ofSurjective g (fun v=> ⟨(v.dir,v.neg),rfl⟩)
 choose s h V using fun x:Step×Step=>earn_x x.1 x.2; let P:=1+∑ i,s i; have ht:1 ≤ P:=le_add_of_nonneg_right (sum_nonneg (fun i _=> h i))
 refine ⟨P,ht,fun c o K v q=>?_ ⟩; let x:= posDir K.val.1; let x':= negDir K.val.1; let y:= posDir K.val.2; let y':= negDir K.val.2
 let f(s t:Step):= fun x:townX c=> plate (increment 1 x) o s t; have hp(i j): Through 2 (f i j) v P:=by
    unfold f; rw [pressed]; refine (pre_through _ (plume_cost o i j) _ (V (i,j) _ ?_)).mono ((single_le_sum (fun i _=>h i) (mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))
    exact ((plume_P o i j).le_opNorm _).trans (mul_le_one₀ (plume_cost o i j) (norm_nonneg _) q)
 have he(u v':Step×Step):Through 2 (f u.1 u.2-f v'.1 v'.2) v (P+P):=by
    rw [sub_eq_add_neg]; apply sum_through (hp _ _); simpa only [abs_neg, abs_one,one_mul,neg_one_smul,←Pi.neg_def] using ((hp v'.1 v'.2).scale (-1)) -- tune
 let F:= f x y-f x y'; let Q:=f x' y-f x' y'; have h₁:Through 2 F v (P+P):=he (x,y) (x,y'); have h₂:Through 2 Q v (P+P):=he (x',y) (x',y'); apply Through.mono (C:=|(4:ℝ)⁻¹| *((P+P)+(P+P)))
 · have hh:Through 2 (F-Q) v ((P+P)+(P+P)):=by rw [sub_eq_add_neg]; exact sum_through h₁ (by simpa only [abs_neg,abs_one,one_mul,neg_one_smul,←Pi.neg_def] using h₂.scale (-1))
   exact hh.scale _
 norm_num; linarith -- check Clover defin
end YM.CF.Tale
