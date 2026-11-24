import YM.SU5.Reconstruction.Anvil.Rays
/-! # Limit budgets in both WOT (no products without continuity) and SOT-star. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup ConePrice
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {ι:Type*}{H:Hilbert}
structure Limited (l:Filter ι) (A:ι→H.Op) (B:H.Op):Prop where
  uniform : ∃ M≥ (0:ℝ),∀ᶠ i in l,‖A i‖≤ M
  confirms (x y:H): Tendsto (fun i=> inner ℂ x (A i y)) l (𝓝 (inner ℂ x (B y)))
structure Pearl (l: Filter ι) (A:ι→H.Op) (B:H.Op):Prop where
  uniform : ∃ M≥ (0:ℝ),∀ᶠ i in l,‖A i‖≤ M
  before (x:H): Tendsto (fun i=> A i x) l (𝓝 (B x))
  after (x:H): Tendsto (fun i=> ContinuousLinearMap.adjoint (A i) x) l (𝓝 (ContinuousLinearMap.adjoint B x))
lemma Pearl.sane {l:Filter ι} {A:ι→H.Op}{B:H.Op}(p:Pearl l A B): Limited l A B:= ⟨p.uniform,fun i y=> tendsto_const_nhds.inner (p.before y)⟩
lemma Pearl.still (l:Filter ι) (B:H.Op): Pearl l (fun _=>B) B:=⟨⟨‖B‖,norm_nonneg _,Eventually.of_forall fun _=> le_rfl⟩,fun i=>tendsto_const_nhds,fun i=>tendsto_const_nhds⟩
lemma earns_per (l:Filter ι)[l.IsCountablyGenerated]{a:Axis}(S:OS.Semigroup H a){z:Wage}(u:Loan a z){x:ι→Wage}(t:Tendsto x l (𝓝 z))(h:∀ᶠ i in l, Loan a (x i)): Pearl l (fun i=> PaysOn S (x i)) (PaysOn S z):= ⟨⟨1,zero_le_one,h.mono (fun i v=>francs S _ v)⟩, on_approach S l u x h t, adj_approach S l u x h t⟩
namespace Limited
variable {l:Filter ι}{A X:ι→H.Op}{B Y:H.Op}(p:Limited l A B)
include p
private lemma sleeve_left (x:H)(g:ι→ H)(y:H)(h:Tendsto g l (𝓝 y)):
    Tendsto (fun i=>inner ℂ (g i) (A i x)) l (𝓝 (inner ℂ y (B x))):= by
 obtain ⟨M,q,e⟩ := p.uniform
 have k:Tendsto (fun i=> ‖g i-y‖*(M*‖x‖)+ dist (inner ℂ y (A i x)) (inner ℂ y (B x))) l (𝓝 0):= by simpa using (((h.sub (tendsto_const_nhds (x:=y))).norm.mul_const (M*‖x‖)).add ((p.confirms y x).dist (tendsto_const_nhds (x:=inner ℂ y (B x))))) -- y implicit
 apply Metric.tendsto_nhds.mpr; intro ε hv
 filter_upwards [k.eventually (gt_mem_nhds hv),e] with i hk t
 apply lt_of_le_of_lt (le_trans (dist_triangle _ (inner ℂ y (A i x)) _) (add_le_add_left ?_ _)) hk
 rw [dist_eq_norm,← inner_sub_left]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right t (norm_nonneg _))) (norm_nonneg _)) -- add leak
private lemma sleeve_right (x:H)(g:ι→ H)(y:H)(h:Tendsto g l (𝓝 y)):
    Tendsto (fun i=>inner ℂ x (A i (g i))) l (𝓝 (inner ℂ x (B y))):= by
 obtain ⟨M,q,e⟩ := p.uniform
 have k:Tendsto (fun i=> ‖x‖*(M*‖g i-y‖)+ dist (inner ℂ x (A i y)) (inner ℂ x (B y))) l (𝓝 0):= by simpa using ((((h.sub (tendsto_const_nhds (x:=y))).norm.const_mul M).const_mul ‖x‖).add ((p.confirms x y).dist (tendsto_const_nhds (x:=inner ℂ x (B y))))) -- name
 apply Metric.tendsto_nhds.mpr; intro ε hv
 filter_upwards [k.eventually (gt_mem_nhds hv),e] with i hk t
 apply lt_of_le_of_lt (le_trans (dist_triangle _ (inner ℂ x (A i y)) _) (add_le_add_left ?_ _)) hk
 rw [dist_eq_norm,← inner_sub_right,← map_sub]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right t (norm_nonneg _))) (norm_nonneg _))
omit p in
private lemma rates (p:Limited l A B)(q:Limited l X Y) : ∃ M≥(0:ℝ),∀ᶠ i in l,‖X i*A i‖ ≤ M:= by
 obtain ⟨r,v,e⟩:=p.uniform; obtain ⟨t,f,g⟩:=q.uniform; exact ⟨t*r,mul_nonneg f v,(g.and e).mono fun x ⟨h,j⟩=>(norm_mul_le ..).trans (mul_le_mul h j (norm_nonneg _) f)⟩
lemma toLeft (q:Pearl l X Y): Limited l (fun i=>X i*A i) (Y*B):= by
 refine ⟨rates p q.sane,fun x y=>?_⟩
 simp_rw [mul_apply_eq_comp, ←ContinuousLinearMap.adjoint_inner_left]
 simpa only [←ContinuousLinearMap.adjoint_inner_left] using p.sleeve_left y _ _ (q.after x) -- simp rew applies also A! need polygons
lemma toRight(q:Pearl l X Y): Limited l (fun i=>A i*X i) (B*Y):= ⟨rates q.sane p,fun x y=> p.sleeve_right x _ _ (q.before y)⟩
end Limited
end YM.Anvil
