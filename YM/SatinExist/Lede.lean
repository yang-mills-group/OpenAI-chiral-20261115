import YM.SU5.Aria.Troupe
-- Chain topology tools on one H: bi-SOT incl tail price; supports parameterized motions.
set_option autoImplicit false
noncomputable section
namespace YM.SatinTails
open Function Filter Set TopologicalSpace Metric NormedSpace
open scoped Topology NNReal InnerProductSpace ComplexOrder Classical
variable {H:Hilbert}(X:H.Op)
variable {F G:ℕ→ H.Op}
open CF.Buffered.Afterglow.Tower.Aria
structure Brakes {A:Hilbert}(F:ℕ→ A.Op)(X:A.Op):Prop where
 costs:∃ k:ℝ,∀ᶠ i:ℕ in atTop, ‖F i‖ ≤ k
 brakes(y:A): Tendsto (fun i=> F i y) atTop (𝓝 (X y))
 heels(y:A):Tendsto (fun i=> (star (F i)) y) atTop (𝓝 ((star X) y))
omit X
namespace Brakes
variable {V W:H.Op}
lemma costAll (p: Brakes F V): ∃ k:ℝ,0≤k ∧ ∀ i, ‖F i‖ ≤ k:=by
 obtain ⟨C,h⟩:= p.costs; obtain ⟨n,h⟩:= eventually_atTop.mp h
 let s:= Finset.Iic n; obtain ⟨i,t⟩:= Finset.exists_max_image s (fun i=> ‖F i‖) ⟨n,Finset.mem_Iic.mpr le_rfl⟩
 refine ⟨max C ‖F i‖, le_max_of_le_right (norm_nonneg _),fun j=>?_⟩
 rcases le_total j n with x|x
 · exact le_max_of_le_right (t.2 _ (Finset.mem_Iic.mpr x))
 exact le_max_of_le_left (h j x)
lemma by_budget(p:Tendsto F atTop (𝓝 V)): Brakes F V:=
 ⟨⟨_,p.norm.eventually (ge_mem_nhds (lt_add_one ‖V‖))⟩,fun y=>(Continuous.clm_apply (show Continuous (@Prod.fst H.Op H) from continuous_fst) continuous_snd |>.continuousAt.tendsto).comp (p.prodMk_nhds (tendsto_const_nhds («x»:=y))),fun y=>(Continuous.clm_apply (show Continuous (@Prod.fst H.Op H) from continuous_fst) continuous_snd |>.continuousAt.tendsto).comp (p.star.prodMk_nhds (tendsto_const_nhds («x»:=y)))⟩
lemma driven (p: Brakes F V){x:ℕ→H} {y:H}(u:Tendsto x atTop (𝓝 y)) : Tendsto (fun i=> F i (x i)) atTop (𝓝 (V y)):= by
 obtain ⟨k,h,t⟩:=p.costAll; exact firmly F h (Eventually.of_forall t) (p.brakes _) u -- name
lemma starR(p:Brakes F V):Brakes (fun i=> star (F i)) (star V):=by
 obtain ⟨t,h,k⟩:=p.costAll; refine ⟨⟨t,Eventually.of_forall fun i=>by rw [norm_star]; exact k _⟩,p.heels,fun x=>?_⟩; simp only [star_star]; exact p.brakes _
lemma uniqueR(p:Brakes F V)(q:Brakes F W): V=W:= ContinuousLinearMap.ext fun i=> tendsto_nhds_unique (p.brakes i) (q.brakes i)
lemma sameC {M:H.Op}(p:Brakes F V)(h:F =ᶠ[atTop] G)(e:V=M):Brakes G M:=by
 subst M; obtain ⟨⟨v,k⟩,y,c⟩:=p
 refine ⟨⟨v,(h.and k).mono fun i ⟨p,k⟩=> p ▸ k⟩,fun i=>(y i).congr' (h.mono fun j p=> by rw [p]),fun i=>(c i).congr' (h.mono fun j p=>by rw [p])⟩
lemma weave(p:Brakes F V)(q:Brakes G W):Brakes (fun i=> F i*G i) (V*W):=by
 obtain ⟨a,h,e⟩:=p.costAll; obtain ⟨b,v,f⟩:=q.costAll
 refine ⟨⟨a*b,Eventually.of_forall fun i=> (norm_mul_le ..).trans (mul_le_mul (e _) (f _) (norm_nonneg _) h)⟩,fun x=> p.driven (q.brakes x),fun x=>?_⟩; simp_rw [star_mul]; exact q.starR.driven (p.starR.brakes x)
lemma pump(p:Brakes F V)(x:ℂ):Brakes (fun i=>x • F i) (x • V):=by
 obtain ⟨a,h,e⟩:=p.costAll; refine ⟨⟨‖x‖*a,Eventually.of_forall fun i=> by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (e i) (norm_nonneg _)⟩,fun i=>(p.brakes i).const_smul _,fun i=>?_⟩; simp only [star_smul]; exact (p.heels i).const_smul _
lemma wickBound(p:Brakes F V)(a:ℝ)(q:∀ᶠ n:ℕ in atTop,‖F n‖≤a):‖V‖≤a:=by
 obtain ⟨i,v⟩:=q.exists
 exact ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans v) fun x=> le_of_tendsto ((p.brakes x).norm) (q.mono fun i v=> ((F i).le_opNorm x).trans (mul_le_mul_of_nonneg_right v (norm_nonneg _)))
variable {j:Axis}(S:OS.Semigroup H j)
lemma heatT{f:ℕ→ℝ≥0}{t:ℝ≥0}(h:Tendsto f atTop (𝓝 t)):Brakes (fun i=>S.E (f i)) (S.E t):=by
 have he(y:H):=(((S.continuousE y).tendsto t).comp h);
 refine ⟨⟨1,Eventually.of_forall fun i=> S.shrinks _⟩,fun i=> he i,fun i=>?_⟩
 have u(t):star (S.E t)= S.E t:= S.sym _; simp_rw [u]; exact he _
-- Bounded linear pricing.
end Brakes
end YM.SatinTails
