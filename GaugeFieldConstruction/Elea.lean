import YM.CF.BProof.PL
-- Arbitrary smooth bills — stronger than falling NPL at old hatch in these comparisons.
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.BProof.PricePort
open Filter
open scoped Topology
variable {a a' b b' c d C:ℝ}{f g h:ℝ→ℝ}
-- cost with unspecified log powers and constants absorbed
abbrev RunRate (a b:ℝ)(f:ℝ→ℝ):Prop:=∃ c:ℝ,∀ᶠ x in atTop,|f x| ≤ coin x a b c
lemma grade_price (p:RunRate a b f)(e:a<a' ∨ a=a' ∧ b<b')(C:ℝ)(w:0<C)(c:ℝ): ∀ᶠ x in atTop,|f x| ≤ C*coin x a' b' c:=by
 obtain ⟨d,h⟩:=p; filter_upwards [h,coin_budget (a:=a) (b:=b) (c:=d) (d:=a') (e:=b') (f:=c) (by rcases e with h|h; exact Or.inl h; tauto) 1 C w] with x H t; exact H.trans (by simpa only [one_mul] using t.le)
lemma RunRate.weaker (p:RunRate a b f)(e:a<a' ∨ a=a'∧ b≤b'): RunRate a' b' f:=by
 by_cases h:a<a' ∨ a=a' ∧ b<b'
 · exact ⟨0,by simpa only [one_mul] using grade_price p h 1 one_pos 0⟩
 obtain ⟨h1,h2⟩ := show a=a' ∧ b=b' from (by grind)
 rw [←h1,←h2]; exact p
lemma RunRate.relax (p:RunRate a b f){u':ℝ}(H:a<a'):RunRate a' u' f:=RunRate.weaker p (Or.inl H)
lemma RunRate.const (C:ℝ): RunRate 0 0 (fun _=>C):= PL.const _
lemma RunRate.xm : RunRate 1 0 id:= ⟨0,(eventually_gt_atTop (0:ℝ)).mono (fun x h=> (abs_of_nonneg h.le).le.trans (coinY h).symm.le)⟩
lemma RunRate.coins (a b c:ℝ):RunRate a b (fun x=>coin x a b c):=⟨c,Eventually.of_forall (fun _=>(abs_of_pos (coin_pos ..)).le)⟩
lemma RunRate.temps : RunRate (-(1/2)) 1 YM.Pressure.temp:=by
 refine ⟨0,?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ)] with x h
 rw [← thresh_eq h]; refine (abs_of_pos (coin_pos ..)).le.trans (le_of_eq ?_); ring_nf
lemma RunRate.add (p:RunRate a b f)(w:RunRate a b g): RunRate a b (fun x=>f x+g x):=by
 obtain ⟨c,h⟩:=p; obtain ⟨d,u⟩:=w; let V:=max c d+1; have hV : max c d < V:= lt_add_one _; have he(x:ℝ)(hx:x<V) : ∀ᶠ y:ℝ in atTop, 2*coin y a b x < 1* coin y a b V:= coin_budget (Or.inr (Or.inr ⟨rfl,rfl,hx⟩)) _ _ one_pos
 refine ⟨V,?_⟩; filter_upwards [h,u,he c ((le_max_left ..).trans_lt hV),he d ((le_max_right ..).trans_lt hV)] with x H W h k; apply (abs_add_le ..).trans ((add_le_add H W).trans ?_); linarith only [h,k]
lemma RunRate.neg (p:RunRate a b f):RunRate a b (fun x=> -f x):=by simpa only [RunRate,abs_neg] using p
lemma RunRate.mul (p:RunRate a b f)(w:RunRate c d g):RunRate (a+c) (b+d) (fun x=>f x*g x):=by obtain ⟨i,h⟩:=p; obtain ⟨j,u⟩:=w; refine ⟨i+j,?_⟩; filter_upwards [h,u] with x H E; rw [abs_mul]; exact (mul_le_mul H E (abs_nonneg _) (coin_pos ..).le).trans_eq (coin_mul ..)
lemma RunRate.cmul (p:RunRate a b f)(x:ℝ): RunRate a b (fun u=>x*f u):=by simpa only [zero_add] using (RunRate.const x).mul p
lemma RunRate.muc (p:RunRate a b f)(x:ℝ): RunRate a b (fun u=>f u*x):=by simpa only [add_zero] using p.mul (RunRate.const x)
lemma RunRate.divc (p:RunRate a b f)(x:ℝ):RunRate a b (fun u=>f u/x):=by simpa only [div_eq_mul_inv] using p.muc x⁻¹
lemma RunRate.mono (p:RunRate a b f)(w:∀ᶠ x in atTop,|g x|≤ |f x|):RunRate a b g:=by obtain ⟨c,h⟩:=p; refine ⟨c,?_⟩; filter_upwards [w,h] with x H T; exact H.trans T
lemma RunRate.pow (p:RunRate a b f)(k:ℕ) : RunRate (a*k) (b*k) (fun x=> f x^k):=by
 induction k with | zero=> simp only [pow_zero,Nat.cast_zero,mul_zero]; exact RunRate.const _|succ k ih=> simp only [Nat.cast_succ,pow_succ,mul_add,mul_one]; exact ih.mul p
lemma RunRate.abs (p:RunRate a b f):RunRate a b (fun x=> |f x|):=by simp_all only [RunRate, abs_abs]
lemma RunRate.tends (p:RunRate a b f)(h:a<0∨a=0∧b<0): Tendsto f atTop (𝓝 0):=by
 obtain ⟨c,H⟩:=p; refine squeeze_zero_norm' ?_ (coin_purchases (a:=a) (b:=b) (c:=c) (by grind)); simpa only [Real.norm_eq_abs] using H
abbrev Rrp (a:ℝ)(x:ℝ):= coin x a 0 0
lemma Rrp_out (a:ℝ)(x:ℝ)(p:0<x): Rrp a x=x^a:=by nth_rw 2 [← coinY p]; unfold Rrp; rw [coin_rpow,one_mul,zero_mul] -- may rewrites both
lemma Rrp_high (p:0<a) : Tendsto (Rrp a) atTop atTop:= (tendsto_rpow_atTop p).congr' ((eventually_gt_atTop (0:ℝ)).mono (fun u h=> (Rrp_out _ _ h).symm))
lemma logPrice (a b:ℝ)(p:RunRate a b f){c d v w:ℝ}(e:a<c∨a=c∧b<d)(h:0<v):∀ᶠ x in atTop,f x ≤ v*coin x c d w:= (grade_price p e v h w).mono fun x g=> (le_abs_self _).trans g
lemma ceiling_b (p:PL f)(e:∀ᶠ x in atTop,0 ≤ f x) : RunRate 0 0 (fun x=> (↑⌈f x⌉₊:ℝ)):=PL.ceil p e
end YM.CF.BProof.PricePort
end
