import YM.CF.BProof.Bias.Approx

/-! spending radius for Z near-model on every torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Stint Lattice Cube Align Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{I:Type}[Fintype I][DecidableEq I][Nonempty I]{F:I→Per N}{r:ℕ}{A B: Op I}
abbrev calf (b e v:ℝ)(t:ℕ):ℝ:= b^t*v+t*e*(1+v)
lemma recur (Z:Op I){e b f v:ℝ}(h:Z=A+Z*B)(a:Near F r e A)(p:Near F r e B)(w:‖B‖≤b)(fP:b+e≤f)(q: f ≤1)(l: ‖Z‖≤v)(t:ℕ): Near F (r*t) (calf f e v t) Z:=by
 obtain ⟨U,u,V⟩:=a; obtain ⟨X,x,T⟩:=p; have he:0≤e:= (norm_nonneg _).trans T; have hz:‖X‖≤f:=by apply (norm_le_norm_sub_add _ B).trans; rw [norm_sub_rev,add_comm]; exact (add_le_add w T).trans fP
 have hv:0 ≤ v:= (norm_nonneg _).trans l; induction t with
 | zero=> exact ⟨0,span_zero _, by simpa [calf] using l⟩
 | succ t ih=>
   obtain ⟨Y,y,W⟩:= ih; rw [mul_add,mul_one]; refine ⟨U+Y*X,plusP (u.up (by omega)) (span_mul y x),?_⟩; rw [show Z-(U+Y*X)= A-U+ Z*(B-X) +(Z-Y)*X by rw [mul_sub,sub_mul,← add_sub_assoc]; nth_rw 1 [h]; abel] -- tune
   apply (norm_add_le ..).trans; refine (add_le_add ((norm_add_le ..).trans (add_le_add V ((norm_mul_le ..).trans (mul_le_mul l T (norm_nonneg _) hv)))) ((norm_mul_le ..).trans (mul_le_mul W hz (norm_nonneg _) ((norm_nonneg _).trans W)))).trans ?_; unfold calf; rw [pow_succ]; push_cast; nlinarith only [mul_le_mul_of_nonneg_left q (show 0≤(t:ℝ)*e*(1+v) by positivity)]
def stepTail (p:Pay)(b v:ℝ)(t:ℕ):= calf ((b+1)/2) (tailPay p t) v t
variable {p:Pay}{b v e u:ℝ}
lemma stepT (w:0≤b)(x:b<1)(k:ℕ): Tendsto (fun i:ℕ=>(i:ℝ)^k*stepTail p b v i) atTop (𝓝 0):=by
 let f:=(b+1)/2; let r:=Real.exp (-p.rate/2)
 have hf:0≤f:=by unfold f; positivity
 have hz:f<1:=by unfold f; linarith
 have hr:r<1:= exp_lt_one_iff.mpr (by linarith [p.charge])
 have h:= tendsto_pow_const_mul_const_pow_of_lt_one k hf hz
 have g:=tendsto_pow_const_mul_const_pow_of_lt_one (k+1) (exp_pos (-p.rate/2)).le hr; convert (h.mul_const v).add (g.mul_const (p.cash*(1+v))) using 1; · ext i; unfold stepTail calf tailPay; rw [mul_comm (-p.rate/2), Real.exp_nat_mul]; dsimp only [f]; rw [pow_succ]; ring
 simp
structure Tango (F:I→Per N)(b v:ℝ)(p:Pay)(Z:Op I):Prop where
   leg:∃ A B:Op I, Z=A+Z*B∧ ‖B‖≤b∧‖Z‖≤v∧∀ i:ℕ, Near F i (tailPay p i) A∧ Near F i (tailPay p i) B
lemma enrol (b v:ℝ)(p:Pay)(w:0≤b)(x:b<1): ∀ᶠ R:ℕ in atTop,∀ {I:Type}[Fintype I][Nonempty I][DecidableEq I]{N:Side}{F:I→Per N}{Z:Op I}, Bias.Tango F b v p Z→ Near F (R^2) (stepTail p b v R) Z:= by
 filter_upwards [(tailPaid p).eventually (gt_mem_nhds (show 0 < (b+1)/2-b by linarith))] with R H; intro I _ _ _ N F Z t; obtain ⟨A,B,h,z,v,k⟩:= t.leg; rw [pow_two]; exact recur Z h (k R).1 (k R).2 z (le_sub_iff_add_le'.mp H.le) (by linarith) v R -- tune
lemma accessible (p:Pay)(u:ℕ)(w:0≤b)(x:b<1)(g:0≤v)(y:0<e)(e':ℝ)(uP:0 < e'): ∃ R:ℕ,∃ s:ℝ, u≤R ∧ 0<s ∧ ∀ {I:Type}[Fintype I][Nonempty I][DecidableEq I]{N:Side}{F:I→Per N}{Z:Op I}, Bias.Tango F b v p Z→ Near F R e' Z ∧ ((∀ i∈ young N u R, ‖swipe F i Z‖≤s)→ Near F u e Z) := by
 have h:Tendsto (fun n:ℕ=>stepTail p b v n) atTop (𝓝 0):=by simpa only [pow_zero,one_mul] using stepT (v:=v) w x 0
 have H:Tendsto (fun n:ℕ=>stepTail p b v n+ revCost (n^2)*stepTail p b v n) atTop (𝓝 0):= by
    convert h.add (((stepT (p:=p) (v:=v) w x 2).const_mul 2).add h) using 1; ext n; dsimp only [revCost]; push_cast; ring; simp -- tune
 obtain ⟨R,hR,hP,f,C⟩:= ((eventually_ge_atTop (max 1 u)).and ((H.eventually (gt_mem_nhds (by linarith:0<e/2))).and ((h.eventually (gt_mem_nhds uP)).and (enrol b v p w x)))).exists; let t:=revCost (R^2); have hx:0<t:=by unfold t revCost; positivity
 have ht:=max_le_iff.mp hR; have hr:u≤ R^2:= ht.2.trans (by nlinarith [ht.1]); let a:=stepTail p b v R; refine ⟨R^2,e/2/t,hr,by positivity,?_⟩; intro I _ _ _ N F Z k; have j:= C k; have ha:0≤a:= (norm_nonneg _).trans j.choose_spec.2; refine ⟨j.enlarge le_rfl f.le,fun k=>?_⟩; apply Near.enlarge (j.restrict hr ha (by positivity) k) le_rfl; change a+t*(e/2/t+a) ≤ e; change a+t*a< e/2 at hP; rw [mul_add,mul_div_cancel₀ _ hx.ne']; linarith -- tune
end YM.CF.BProof.Bias
