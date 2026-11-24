import YM.SU5.Cordial.Balloon
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup.Balloon
open Function Filter Complex Set
open scoped InnerProductSpace NNReal BigOperators Topology
variable {H:Hilbert}{j:Axis}(S:Semigroup H j)(x:ℕ→H)
-- lemmas on costs, avoid unfolding
abbrev Limited (H:Hilbert)(x:ℕ→H):Prop:=∃ c:ℝ,∀ᶠ i:ℕ in atTop, ‖x i‖≤ c
lemma le_seam {y:ℕ→H}(h:Limited H x)(u:∀ i,‖y i‖ ≤ ‖x i‖) : Limited H y:=by obtain ⟨v,V⟩:=h; exact ⟨v,V.mono (fun i h=>(u i).trans h)⟩
lemma heatedLim (w:ℝ≥0)(x:H): ‖S.E w x‖≤‖x‖:= ((S.E w).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks w))
lemma gainedLim (t:ℕ→ℝ≥0)(h:Limited H x): Limited H (fun i=> S.E (t i) (x i)):= le_seam x h (fun i=> heatedLim S (t i) (x i))
lemma soarE(t:ℕ→ Cross j)(F:ℕ→H)(h:Tendsto F atTop (𝓝 0)): Tendsto (fun i=> S.U (t i) (F i)) atTop (𝓝 0):=by rw [tendsto_zero_iff_norm_tendsto_zero]; simp_rw [S.unitary]; exact tendsto_zero_iff_norm_tendsto_zero.mp h
lemma soarL(t:ℕ→ℝ≥0) (F:ℕ→H)(h:Tendsto F atTop (𝓝 0)): Tendsto (fun i=> S.E (t i) (F i)) atTop (𝓝 0):=by rw [tendsto_zero_iff_norm_tendsto_zero]; exact squeeze_zero (fun _=> norm_nonneg _) (fun _=> heatedLim ..) (tendsto_zero_iff_norm_tendsto_zero.mp h)
lemma aura (H:Hilbert)(x y:ℕ→H)(h:Limited H x)(t:Tendsto y atTop (𝓝 0)): Tendsto (fun i=>inner ℂ (x i) (y i)) atTop (𝓝 0):=by
 obtain ⟨c,h⟩:=h; rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) (h.mono fun i h=> (norm_inner_le_norm (x i) (y i)).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))) ?_; simpa only [mul_zero] using (tendsto_zero_iff_norm_tendsto_zero.mp t).const_mul c
lemma aura' (H:Hilbert)(x y:ℕ→H)(h:Limited H x)(t:Tendsto y atTop (𝓝 0)): Tendsto (fun i=>inner ℂ (y i) (x i)) atTop (𝓝 0):=by
 let u:= continuous_star (R:=ℂ); have he:=u.continuousAt.tendsto.comp (aura H x y h t); rw [star_zero] at he; exact he.congr fun i=> inner_conj_symm ..
lemma unifier {b : ℂ} {f g:ℕ→ℂ} (h:Tendsto (fun i=>f i-g i) atTop (𝓝 0))(t:Tendsto g atTop (𝓝 b)): Tendsto f atTop (𝓝 b):=by have he:=h.add t; rw [zero_add] at he; exact he.congr fun i=> sub_add_cancel ..
lemma realize_shim (q:ℕ→ℝ≥0)(X Y: ℕ→ Cross j)(h:Tendsto (fun i=> S.U (X i) (x i)-S.U (Y i) (x i)) atTop (𝓝 0)) : Tendsto (fun i=> S.U (X i) (S.E (q i) (x i))- S.U (Y i) (S.E (q i) (x i))) atTop (𝓝 0):=by
 let f(i):=S.U (X i) (x i)-S.U (Y i) (x i); refine (soarL S q f h).congr fun i=>?_ ; unfold f; rw [map_sub]; exact congrArg₂ (· - ·) (DFunLike.congr_fun (S.independent ..) _) (DFunLike.congr_fun (S.independent ..) _)
-- monotone cost nonnegative
lemma shrinkBound (t u:ℝ≥0)(x:H)(h:t≤u) : (inner ℂ x (S.E u x)).re ≤ (inner ℂ x (S.E t x)).re:=by
 have he(v:ℝ≥0): (inner ℂ x (S.E v x)).re= ‖S.E (v/2) x‖^2:= by
    nth_rw 1 [← add_halves v]; rw [S.time, ContinuousLinearMap.comp_apply,← S.swing]; exact inner_self_eq_norm_sq (𝕜:=ℂ) (S.E (v/2) x)
 rw [he,he]; exact pow_le_pow_left₀ (norm_nonneg _) (S.norm_decrease x (by gcongr)) 2
lemma capture (t u:ℝ≥0)(x:H)(h:t≤u) : ‖S.E t x-x‖^2 ≤ 2*(‖x‖^2-(inner ℂ x (S.E u x)).re):= by
 rw [norm_sub_rev,norm_sub_sq (𝕜:=ℂ)]; have ht:=pow_le_pow_left₀ (norm_nonneg _) (heatedLim S t x) 2; change _ - 2*(inner ℂ x (S.E t x)).re + _ ≤ _; linarith [shrinkBound S t u x h]
lemma hasLimit {x:ℕ→H}{p:ℝ}(e:Tendsto (fun i=> ‖x i‖^2) atTop (𝓝 p)): Limited H x:=⟨Real.sqrt (p+1), (e.eventually (ge_mem_nhds (lt_add_one p))).mono fun _ w=> Real.le_sqrt_of_sq_le w⟩
variable {x}
lemma tiny {δ:ℕ→ℝ}(p:∀ i,0<δ i){F:ℝ→ℂ}(q:ContinuousAt F 0)(h:Tendsto (fun i=>‖x i‖^2) atTop (𝓝 (F 0).re)) (A:∀ s:ℝ,0<s→∃ t:ℕ→ℝ≥0,Tendsto (fun i=>(t i:ℝ)/δ i) atTop (𝓝 s) ∧ Tendsto (fun i=>(inner ℂ (x i) (S.E (t i) (x i))).re) atTop (𝓝 (F s).re))(u:ℕ→ℝ≥0)(t:Tendsto (fun i=>(u i:ℝ)/δ i) atTop (𝓝 0)): Tendsto (fun i=>S.E (u i) (x i)-x i) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; apply Metric.tendsto_nhds.mpr; intro ε v
 let G(s:ℝ):=2*((F 0).re-(F s).re); have he:G 0< ε^2:=by unfold G; simp; positivity
 have hv :=eventually_nhdsWithin_of_eventually_nhds (s:=Set.Ioi (0:ℝ)) ((show ContinuousAt G 0 from continuousAt_const.mul (continuousAt_const.sub (Complex.continuous_re.continuousAt.comp q))).tendsto.eventually (gt_mem_nhds he)); obtain ⟨d,D,W⟩:= (hv.and (self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ)))).exists; obtain ⟨l,L,H'⟩:= A d W
 filter_upwards [(t.eventually_lt L (show 0<d from W)), ((h.sub H').const_mul 2).eventually (gt_mem_nhds (show G d < _ from D))] with i h v'
 have ht:u i≤l i:= by exact_mod_cast (div_le_div_iff_of_pos_right (p i)).mp h.le
 simp only [Real.dist_eq,sub_zero,abs_norm]; exact (sq_lt_sq₀ (norm_nonneg _) v.le).mp ((capture S _ _ _ ht).trans_lt v')
end YM.OS.Semigroup.Balloon
