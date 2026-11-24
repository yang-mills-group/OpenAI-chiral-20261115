import YM.SU5.Registration.Reconstruction
/-! # Strong* purchases, stable under the absolute-error accounts (estimates in
norm). Pointwise is in i on full H before applying widths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function MeasureTheory Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet Boundary Probe Multiplier Roy
variable {H : Hilbert} {A B:ℕ→ H.Op} {U V : H.Op}
def Flying (A:ℕ→ H.Op)(U:H.Op) : Prop :=
  ∀ x:H, Tendsto (fun i=> A i x) atTop (𝓝 (U x)) ∧ Tendsto (fun i=> (A i).adjoint x) atTop (𝓝 (U.adjoint x))
def Travels (A:ℕ→ H.Op):Prop:= ∀ x:H, CauchySeq (fun i=> A i x) ∧ CauchySeq (fun i=> (A i).adjoint x)
namespace Flying
lemma still (U:H.Op): Flying (fun _=>U) U:=fun _=>⟨tendsto_const_nhds,tendsto_const_nhds⟩
lemma heat {α:Axis}(S : OS.Semigroup H α){p:ℕ→ℝ≥0}{t:ℝ≥0}(h:Tendsto p atTop (𝓝 t)): Flying (fun i=> S.E (p i)) (S.E t):=by
 intro v; simp_rw [S.sym]; have hv:= ((S.continuousE v).tendsto t).comp h; exact ⟨hv,hv⟩
lemma adjoint (p:Flying A U): Flying (fun i=> (A i).adjoint) U.adjoint:=by intro v; simp_rw [ContinuousLinearMap.adjoint_adjoint]; exact (p v).symm
lemma const_adjoint_in_forall (p:Flying A U) (x:H) : Tendsto (fun i=> star (A i) x) atTop (𝓝 (star U x)) := (p x).2
lemma Cauchy (p:Flying A U): Travels A:=fun i=>⟨(p i).1.cauchySeq,(p i).2.cauchySeq⟩
lemma settles (p:Travels A):∃ U,Flying A U := by
 obtain ⟨U,u⟩:= delivery_limit (fun x=> (p x).1); obtain ⟨V,v⟩:= delivery_limit (fun x=> (p x).2)
 have h:U.adjoint=V:=by
    ext1 x; apply ext_inner_right ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_left]; apply tendsto_nhds_unique ((tendsto_const_nhds (x:=x)).inner (𝕜:=ℂ) (u y)); refine ((v x).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=y))).congr fun i=>?_ ; exact ContinuousLinearMap.adjoint_inner_left ..
 exact ⟨U,fun x=>⟨u x,by rw [h]; exact v x⟩⟩
lemma firm (p:Flying A U){x:ℕ→H}{y:H}(h:Tendsto x atTop (𝓝 y)): Tendsto (fun i=>A i (x i)) atTop (𝓝 (U y)):=by
 obtain ⟨C,hc,u⟩:= ceiling (fun v=> (p.Cauchy v).1)
 -- local continuous strap
 rw [tendsto_iff_norm_sub_tendsto_zero]
 refine squeeze_zero (fun _ => norm_nonneg _) (fun i=> (show ‖A i (x i)-U y‖ ≤ C*‖x i-y‖+‖A i y-U y‖ from ?_)) ?_
 · refine (norm_sub_le_norm_sub_add_norm_sub _ (A i y) _).trans (add_le_add ?_ le_rfl); rw [←map_sub]; exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (u i) (norm_nonneg _))
 simpa only [mul_zero,zero_add] using (((tendsto_iff_norm_sub_tendsto_zero.mp h).const_mul C).add (tendsto_iff_norm_sub_tendsto_zero.mp (p y).1))
lemma multiply (p:Flying A U)(g:Flying B V): Flying (fun i=>A i*B i) (U*V):= by
 intro v; simp only [←ContinuousLinearMap.star_eq_adjoint,star_mul]
 exact ⟨p.firm ((g v).1),g.adjoint.firm ((p v).2)⟩
lemma scaled {a:ℕ→ℂ}{b:ℂ}(h:Tendsto a atTop (𝓝 b))(p:Flying A U) : Flying (fun i=>a i • A i) (b • U):=by
 intro x; have hx: ∀ (U:H.Op)(a:ℂ), (a • U).adjoint=(star a) • U.adjoint:= fun U a=> ContinuousLinearMap.adjoint.map_smulₛₗ a U -- name
 simp only [hx]; exact ⟨Tendsto.smul h (p x).1, Tendsto.smul h.star (p x).2⟩
lemma late (p:Flying A U)(q:A=ᶠ[atTop] B): Flying B U:=fun x=> ⟨((p x).1).congr' (q.mono fun i h=>congrArg (fun r:H.Op=>r x) h), ((p x).2).congr' (q.mono fun i h=>congrArg (fun r:H.Op=>r.adjoint x) h)⟩

private lemma flourishes (A:ℕ→ H.Op)(p:∀ ε:ℝ,0<ε→∃ B:ℕ→H.Op, (∀ x:H, CauchySeq (fun i=> B i x))∧ ∀ᶠ i:ℕ in atTop,‖A i-B i‖≤ε) : ∀ v:H,CauchySeq (fun i=> A i v):=by
 intro v; apply Metric.cauchySeq_iff.2; intro ε e
 let c:= ‖v‖; have h:0≤c:= norm_nonneg _; let s:=ε/(3*(c+1)); have he:0<s:=by unfold s; positivity
 obtain ⟨W,q,t⟩:= p s he; obtain ⟨n,u⟩:=eventually_atTop.mp t; obtain ⟨k,p⟩:=Metric.cauchySeq_iff.1 (q v) (ε/3) (by positivity)
 have hz(i:ℕ)(j:i≥n): dist (A i v) (W i v)≤ s*c:=by rw [dist_eq_norm]; exact ((A i-W i).le_opNorm v).trans (mul_le_mul_of_nonneg_right (u i j) h)
 refine ⟨max k n,fun i g j w=>?_⟩
 have hA:= (dist_triangle (A i v) (W i v) _).trans (add_le_add (hz i ((le_max_right ..).trans g)) (dist_triangle (W i v) (W j v) (A j v)))
 have ht:= hz j ((le_max_right ..).trans w); rw [dist_comm] at ht; have hg:= p i ((le_max_left ..).trans g) j ((le_max_left ..).trans w)
 have hC : s*(3*(c+1))=ε:= div_mul_cancel₀ _ (by positivity); linarith only [hA,ht,hC,hg,he] -- linarith `s*c` normalize? have he overloaded argument
lemma via (p:∀ ε:ℝ,0<ε→∃ B:ℕ→H.Op, Travels B ∧ ∀ᶠ i:ℕ in atTop,‖A i-B i‖ ≤ ε) : Travels A:=by
 intro v; refine ⟨flourishes A (fun ε t=> (p ε t).imp (fun B h=>⟨fun x=>(h.1 x).1,h.2⟩)) v, flourishes (fun i=> (A i).adjoint) (fun e t=> ?_) v⟩
 obtain ⟨b,q,h⟩:=p e t
 refine ⟨fun i=> (b i).adjoint, fun x=>(q x).2,h.mono fun i y=>?_⟩
 rw [←map_sub,ContinuousLinearMap.adjoint.norm_map]; exact y
end Flying
end YM.SatinRegistration
open YM.SatinRegistration
#print axioms Flying.via
#print axioms Flying.settles
#print axioms Flying.scaled
#print axioms Flying.multiply
