import GaugeFieldConstruction.IoneΛL
/-!
 # Conservative Mink distribution, directional derivatives represent Tuy formulas with correct signs.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Filter Set Finset Mink MeasureTheory Analysis LineDeriv
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable {n:ℕ}
noncomputable def penΛ (n:ℕ):Points n→L[ℝ]Full n:= LinearMap.toContinuousLinearMap {
 toFun x:=glow x 0
 map_add' x y:=by ext i; simp [glow]
 map_smul' a x:=by ext i; simp [glow] -- tune
}
lemma φpenΛ {y:Points n} (x:Points n): glow x y=penΛ n x+glow 0 y:=by ext i; change glow _ _ _= (glow _ _ _) + (glow _ _ _); simp [glow]
lemma penaΛ {y:Points n}(x:Points n):HasFDerivAt (fun x=> glow x y) (penΛ n) x:= by
 rw [show (fun x=> glow x y)=fun x=> penΛ n x + glow 0 y from funext fun i=>φpenΛ i]; exact (penΛ n).hasFDerivAt.add_const _
variable {y:Points n}(hy:y∈fields n)
include hy
lemma roseΛ (x:Points n):glow x y∈tube n:=by simpa [tube] using hy
abbrev emberΛ (w:Full n→ℂ)(x:Points n):=w (glow x y)
abbrev MintSpΛ (w:Full n→ℂ)(d: Points n)(x:Full n):ℂ:=fderiv ℂ w x (penΛ n d)
variable (w:Full n→ℂ)(r:AnalyticOnNhd ℂ w (tube n))(f:Joint n)
local notation "Φw"=> emberΛ (y:=y) w
variable (d:Points n)
include r
lemma phiFΛ (x:Points n):HasFDerivAt Φw ((fderiv ℂ w (glow x y)).restrictScalars ℝ ∘L penΛ n) x := (((r _ (roseΛ hy x)).differentiableAt.hasFDerivAt).restrictScalars ℝ).comp x (penaΛ x)
lemma ΜineSpΛ (x:Points n): fderiv ℝ Φw x d= MintSpΛ w d (glow x y):=by rw [(phiFΛ hy w r _).fderiv]; rfl
-- integrable compact derivative test norm
variable (h:HasCompactSupport (f:Points n→ℂ))
include h
lemma MSteadyΛL : Integrable (fun x:Points n=> MintSpΛ w d (glow x y)* f x):=by
 have e: Continuous fun x:Points n=> MintSpΛ w d (glow x y):= continuous_iff_continuousAt.mpr fun x=> ((((r _ (roseΛ hy x)).fderiv.continuousAt).comp (f:=fun x=>glow x y) (penaΛ x).continuousAt).clm_apply continuousAt_const)
 exact (e.mul f.continuous).integrable_of_hasCompactSupport h.mul_left
noncomputable abbrev DriftΛL (x:Points n):Joint n →L[ℂ] Joint n:= lineDerivOpCLM ℂ _ x
omit h hy r in
lemma DriftΛKnownL (x:Points n): DriftΛL d f x=fderiv ℝ f x d:=by simp [DriftΛL, SchwartzMap.lineDerivOp_apply_eq_fderiv]
lemma FeeΛSpL : (∫ x:Points n, MintSpΛ w d (glow x y)* f x)= -(∫ x:Points n, w (glow x y) * (DriftΛL d f) x ) :=by
 have hc:Continuous Φw:=continuous_iff_continuousAt.mpr (fun x=> (phiFΛ hy w r x).continuousAt)
 have hI:Integrable (fun x=>fderiv ℝ Φw x d * f x):=by simp_rw [ΜineSpΛ hy w r]; exact MSteadyΛL hy w r f d h
 have hJ: HasCompactSupport (DriftΛL d f : Points n→ℂ) := h.mono' (Set.Subset.trans (subset_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset d f)) -- tune
 have he:Integrable (fun x=>Φw x * fderiv ℝ f x d):=by simp_rw [← DriftΛKnownL]; exact (hc.mul (DriftΛL d f).continuous).integrable_of_hasCompactSupport hJ.mul_left
 have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hI he ((hc.mul f.continuous).integrable_of_hasCompactSupport h.mul_left) (fun x _=> (phiFΛ hy w r x).differentiableAt) (fun x _=> (f.smooth 1).differentiable (by simp) x)
 simp_rw [ΜineSpΛ hy w r,← DriftΛKnownL] at H; change _= -(∫ x:Points n, Φw x * DriftΛL d f x); rw [H,neg_neg]
omit hy r
-- ∂ distributions are W derivatives exactly. profile corner
variable (V:Fin n→ S.Union)(p:F.NonTangentialFree Y)(q:X.FullBody F)
include p q
lemma risePayΛ : Tendsto (fun e: Heights n=> (∫ x:Points n, MintSpΛ (X.emit V) d (glow x (dawn e))* f x)) (𝓝[east n] 0) (𝓝 (-(Y.W n V (DriftΛL d f)))):= by
 refine (Tendsto.neg (p.corner n V (DriftΛL d f))).congr' ?_
 filter_upwards [self_mem_nhdsWithin] with i hi
 change -(∫ x:Points n,F.restricted V i x * _) = _; rw [FeeΛSpL (etched hi) _ (q.hol n V) f d h]; simp_rw [q.pure n V _ i hi]

abbrev MintDΛ (D:Axis→Axis→ S.Union):Prop:=∀ (n:ℕ)(V:Fin n→ S.Union)(i:Fin n)(a:Axis)(x:Full n), x∈tube n→ (∑ j:Axis, MintSpΛ (X.emit (Function.update V i (D j a))) (NSF.Points.direction i j) x)=0 -- not MinkΦ, binding external
variable (D:Axis→Axis→ S.Union) (e:MintDΛ (X:=X) D)
include e
variable (a:Axis)(k:Fin n)
lemma ΛDomusL : (∑ j:Axis, (Y.W n (Function.update V k (D j a)) (DriftΛL (NSF.Points.direction k j) f)))=0 :=by
 let A(j:Axis):= X.emit (Function.update V k (D j a)); let d(j:Axis):=NSF.Points.direction k j
 let I(j:Axis):=Y.W n (Function.update V k (D j a)) (DriftΛL (d j) f)
 let J (j:Axis)(v:Heights n)(x:Points n):=MintSpΛ (A j) (d j) (glow x (dawn v))* f x
 let U(v:Heights n):=∑ j:Axis, ∫ x:Points n, J j v x
 have ht: Tendsto U (𝓝[east n] 0) (𝓝 (∑ j:Axis, -(I j))):= tendsto_finsetSum _ fun i _=> risePayΛ f _ h _ p q
 have hm(v:Heights n)(u:v∈east n): U v=0 :=by
    have he(x:Points n):(∑ j:Axis,J j v x)=0:=by unfold J; rw [← sum_mul, show (∑ j:Axis, MintSpΛ (A j) (d j) (glow x (dawn v)))=0 from e n V k a (glow x (dawn v)) (roseΛ (etched u) _),zero_mul]
    unfold U; rw[← integral_finsetSum _ (fun i _=> MSteadyΛL (etched u) _ (q.hol n _) f _ h)]; change (∫ x:Points n,∑ j:Axis,J j v x)=0
    simp only [he,integral_zero]
 haveI: (𝓝[east n] (0: Heights n)).NeBot:= awaits (light n)
 rw [sum_neg_distrib] at ht
 have h0:Tendsto U (𝓝[east n] 0) (𝓝 0):= Tendsto.congr' (?_ : (fun _:Heights n=>(0:ℂ))=ᶠ[_] U) tendsto_const_nhds
 · exact neg_eq_zero.mp (tendsto_nhds_unique ht h0)
 filter_upwards [self_mem_nhdsWithin] with v hv; exact (hm v hv).symm
omit h
structure ConsWΛL (Y:Surface S)(D:Axis→Axis→ S.Union):Prop where
    lives (n:ℕ)(f:Joint n)(V:Fin n→ S.Union)(a:Axis)(k:Fin n): (∑ j:Axis, (Y.W n (Function.update V k (D j a)) (DriftΛL (NSF.Points.direction k j) f)))=0
lemma ΛHestiaL : ConsWΛL Y D:=by
 constructor; intro n f V a k; let G(f:Joint n):=∑ j:Axis,Y.W n (Function.update V k (D j a)) (DriftΛL (NSF.Points.direction k j) f)
 have h: Continuous G:= continuous_finsetSum _ fun i _=> (Y.W n _).continuous.comp (DriftΛL _).continuous
 have he (i:ℕ): G (Probe.cap i f)=0:= ΛDomusL _ (Probe.finite_cap i) V p q D e a k
 have u:Tendsto (fun i:ℕ=> G (Probe.cap i f)) atTop (𝓝 (G f)):= (h.tendsto f).comp (Probe.persistent f)
 simp_rw [he] at u; exact tendsto_nhds_unique u tendsto_const_nhds
#print axioms roseΛ
#print axioms risePayΛ
#print axioms ΛHestiaL
end YM.NSF.Boundary
