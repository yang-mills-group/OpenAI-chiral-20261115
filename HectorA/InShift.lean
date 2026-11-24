import HectorA.Caffeine
set_option autoImplicit false
noncomputable section
namespace Yoland
open YM Filter Set Function
open YM.OS YM.OS.Semigroup
open scoped Topology NNReal InnerProductSpace BigOperators Classical
variable {H:Hilbert}{j:Axis}(S:OS.Semigroup H j)(x:H)
attribute [local instance] InnerProductSpace.complexToReal
abbrev dawn (t:ℝ):H.Op:=S.E t.toNNReal
lemma dawnRise(t:ℝ)(h:0<t): AnalyticAt ℝ (dawn S) t:=by
 have hp : AnalyticAt ℂ (F S) t:=S.localHeat t (show 0 < (t:ℂ).re from h)
 refine ((AnalyticAt.restrictScalars (𝕜:=ℝ) hp).comp (Complex.ofRealCLM.analyticAt t)).congr ?_
 filter_upwards [lt_mem_nhds h] with y hy
 change S.F y=_; rw [show (y:ℂ) = duration y.toNNReal from congrArg ((↑):ℝ→ℂ) (Real.coe_toNNReal y hy.le).symm,S.roots_heat (Real.toNNReal_pos.mpr hy)]
lemma dawn_add {a b:ℝ}(ha:0 ≤ a)(hb:0 ≤ b): dawn S (a+b)=(dawn S a).comp (dawn S b):=by
 unfold dawn; rw [show (a+b).toNNReal=a.toNNReal+b.toNNReal from (by apply NNReal.eq; rw [Real.coe_toNNReal _ (by linarith),NNReal.coe_add,Real.coe_toNNReal _ ha,Real.coe_toNNReal _ hb]),S.time];
abbrev pay(i:ℕ)(t:ℝ):H.Op:= iteratedDeriv i (dawn S) t
lemma paid{t:ℝ}(p:0<t)(i:ℕ): detail S x i t=(pay S i t) x:=by
 let F: H.Op→L[ℂ] H:= ContinuousLinearMap.apply ℂ H.space x
 exact transport (dawnRise S t p) (F.restrictScalars ℝ) i
-- P.Shard.D by h^n
abbrev noon(h:ℝ):H.Op:= (h⁻¹:ℝ) • (dawn S h-ContinuousLinearMap.id ℂ H.space)
def frame (n:ℕ)(t:ℝ)(b:H.Op):H.Op:= Nat.rec b (fun _ g=> (noon S t).comp g) n
lemma fringe (h:ℝ): frame S 0 h= id:=rfl
lemma stride_single {v t:ℝ}(u:0<v)(ht:0 ≤ t): (noon S t).comp (dawn S v)= t⁻¹ • (dawn S (v+t)-dawn S v):=by
 rw [add_comm v t,dawn_add S ht u.le]; unfold noon; rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp]
lemma paysH1 (y:ℕ→ℝ)(h:∀i,0<y i)(v:Tendsto y atTop (𝓝 0)) {k:ℝ}(e:0<k):
 Tendsto (fun i=>(noon S (y i)).comp (dawn S k)) atTop (𝓝 (pay S 1 k)):=by
 have ht:Tendsto (fun t:ℝ=> t⁻¹ • (dawn S (k+t)-dawn S k)) (𝓝[≠] 0) (𝓝 (pay S 1 k)):= hasDerivAt_iff_tendsto_slope_zero.mp (show HasDerivAt (dawn S) (pay S 1 k) k from (by rw [pay,iteratedDeriv_one]; exact (dawnRise S k e).differentiableAt.hasDerivAt))
 have hu:Tendsto y atTop (𝓝[≠] 0):= tendsto_nhdsWithin_iff.mpr ⟨v,Eventually.of_forall fun i=> (h i).ne'⟩
 exact (ht.comp hu).congr (fun i=> (stride_single S e (h i).le).symm)
-- S.P derivatives compose exact.i+n n any positive gaps.
lemma earns_asset(i n:ℕ)(a b:ℝ)(ha:0<a)(hb:0 < b): (pay S n b).comp (pay S i a)=pay S (n+i) (a+b):=by
 -- evaluate n pull first.For each x price vector.Second shift S.E(b) left.
 have hi(x:H)(r:ℝ)(p:0<r): (dawn S r) (pay S i a x) = pay S i (a+r) x:=by
    have he:dawn S r ∘ tempo S x =ᶠ[𝓝 a] (fun t=> tempo S x (t+r)):= by
       filter_upwards [lt_mem_nhds ha] with t ht
       change dawn S r (dawn S t x)=dawn S (t+r) x; rw [add_comm,dawn_add S p.le ht.le]; rfl
    rw [← paid S _ ha,← paid S _ (by linarith)]; exact shifted _ (civilB S x) ha he i
 ext x
 change (pay S n b) (pay S i a x)=pay S (n+i) (a+b) x
 let y:=pay S i a x
 rw [← paid S y hb,← paid S _ (by linarith)]; unfold detail
 have he:(tempo S y) =ᶠ[𝓝 b] (fun r:ℝ=>iteratedDeriv i (tempo S x) (a+r)):=by
    filter_upwards [lt_mem_nhds hb] with r hr
    exact (hi x r hr).trans ((paid S _ (by linarith) _) |>.symm)
 rw [he.iteratedDeriv_eq, iteratedDeriv_comp_const_add]
 simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply] -- D^n D^i, don't commute?
#print axioms earns_asset
 -- flag view dollars
lemma framed(v w:H.Op)(n:ℕ)(t:ℝ):frame S n t (v.comp w)=(frame S n t v).comp w:=by induction n <;> simp_all [frame,ContinuousLinearMap.comp_assoc] -- tune Induction ih.Basis
lemma tempo_step(y:ℕ→ℝ)(h:∀i,0< y i)(v:Tendsto y atTop (𝓝 0))(n:ℕ) : Tendsto (fun i=> frame S n (y i) (dawn S n)) atTop (𝓝 (pay S n n)):=by
 induction n with
 | zero=>simp [frame,pay]
 | succ n ih=>
   let f(i):= frame S n (y i) (dawn S n); let g(i):=(noon S (y i)).comp (dawn S (1:ℝ))
   have hh:Tendsto (fun i=> (g i).comp (f i)) atTop (𝓝 ((pay S 1 1).comp (pay S n n))):= soup (R:=H) g f (paysH1 S y h v zero_lt_one) ih
   have hp:(pay S 1 1).comp (pay S n n)= pay S (n+1:ℕ) (n+1:ℕ):=by
      by_cases p:n=0; · subst n; unfold pay; rw [iteratedDeriv_zero,dawn,Nat.cast_zero,Real.toNNReal_zero,S.eZero,ContinuousLinearMap.comp_id]; norm_num
      rw [earns_asset S n 1 n 1 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero p)) zero_lt_one,Nat.cast_add,Nat.cast_one,add_comm 1 n]
   rw [hp] at hh; refine hh.congr fun i=>?_
   -- successor frame is D∘(frame n (E1+En)), commute dawn(1) under frame.
   have hu(w:ℝ)(u:0 ≤w)(z:H.Op)(p:ℕ): frame S p (y i) ((dawn S w).comp z)=(dawn S w).comp (frame S p (y i) z):= by
      induction p generalizing z with
      | zero=>rfl
      | succ p hp=>
        change (noon S _).comp (frame S p _ _)=(dawn S w).comp ((noon S _).comp (frame S p _ z)); rw [hp,← ContinuousLinearMap.comp_assoc,← ContinuousLinearMap.comp_assoc,show (noon S (y i)).comp (dawn S w)=(dawn S w).comp (noon S (y i)) from (?_)] -- orientation comp_assoc maybe (f.comp g).comp h
        unfold noon; rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_sub,← dawn_add S (h _).le u,← dawn_add S u (h _).le,add_comm w]; simp
   unfold f g; change ((noon S (y i)).comp (dawn S 1)).comp _=(noon S (y i)).comp (frame S n _ _)
   rw [Nat.cast_add,Nat.cast_one,add_comm (n:ℝ) 1,dawn_add S zero_le_one (Nat.cast_nonneg n),hu 1 zero_le_one, ContinuousLinearMap.comp_assoc]
where soup{R:Hilbert}(f g:ℕ→R.Op){a b:R.Op}(h:Tendsto f atTop (𝓝 a))(t:Tendsto g atTop (𝓝 b)): Tendsto (fun i=>(f i).comp (g i)) atTop (𝓝 (a.comp b)):= (show Continuous (fun p:R.Op × R.Op=> ContinuousLinearMap.compL ℂ R.space R.space R.space p.1 p.2) from ((ContinuousLinearMap.compL ℂ R.space R.space R.space).continuous.comp continuous_fst).clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds t)
#check Filter.Tendsto.prodMk_nhds
#check ContinuousLinearMap.compL
end Yoland
