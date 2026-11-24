import YM.SU5.Reconstruction.Crease.Habit
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex
variable {H:Hilbert}{M:Net H}{Ω:H}
section
variable {A B:H.Op} (h: IsSelfAdjoint A) (p: IsSelfAdjoint B) (e:Commute A B)
include h p e
lemma noImag (x:H) : (inner ℂ (A x) (B x)).im=0:=by
 have hv: IsSelfAdjoint (A*B):= by unfold IsSelfAdjoint; rw [star_mul,h.star_eq,p.star_eq,e.eq]
 rw [Clasp.through_self _ h]; rw [← show (A*B) x=A (B x) from rfl]
 have hw : inner ℂ x ((A*B) x) = star (inner ℂ x ((A*B) x)):= by nth_rw 1 [← Clasp.through_self _ hv]; exact (inner_conj_symm (𝕜:=ℂ) ((A*B) x) x).symm -- tune occurrences
 have hk:= congrArg Complex.im hw; change _= - (inner ℂ x ((A*B) x)).im at hk; linarith
end
lemma permitted (f:ℝ→ℝ){A:H.Op}(q:A∈M): cfc f A∈ M:=by
 rw [← M.commutant_commutant]
 refine VonNeumannAlgebra.mem_commutant_iff.mpr fun g hg=> (((show Commute A g from VonNeumannAlgebra.mem_commutant_iff.mp hg A q).cfc_real f).symm.eq)
section
variable {A N:H.Op} (p:A∈M) (q:N∈ M.commutant) (h:IsSelfAdjoint N)(t:‖N‖ ≤1)
include q t
lemma profitable (Ω:H) {U:H.Op}(m:U ∈ M)(v:0≤U) : ‖inner ℂ (U Ω) (N Ω)‖ ≤ (inner ℂ (U Ω) Ω).re:=by
 let V:=CFC.sqrt U; have ht: IsSelfAdjoint V:=IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _); have hy: Commute V N:= rootComm (show Commute U N from VonNeumannAlgebra.mem_commutant_iff.mp q U m) -- name
 have hp: V (V Ω)=U Ω:= DFunLike.congr_fun (CFC.sqrt_mul_sqrt_self U v) Ω
 rw [← hp]; nth_rw 1 [Clasp.through_self _ ht]; rw [show V (N Ω)=N (V Ω) from DFunLike.congr_fun hy.eq Ω, Clasp.through_self V ht (V Ω) Ω,show (inner ℂ (V Ω) (V Ω)).re=‖V Ω‖^2 from inner_self_eq_norm_sq (𝕜:=ℂ) _]
 exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((N.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) t)) (norm_nonneg _)).trans (by rw [pow_two]))
-- approximate sign comparator
variable (a:ℂ) (k:a.re=1/2) (Ω:H)
-- enough strict ≤ price+ε (in kernel ‖Ω‖ unadjusted)
include k p
lemma priceAny (b:IsSelfAdjoint A)(ε:ℝ) (v:0<ε) : ∃ y:H.Op, y∈ M ∧ IsSelfAdjoint y ∧ ‖y‖≤1 ∧ (inner ℂ (A Ω) (N Ω)).re ≤ 2*( (star a)*inner ℂ (A Ω) (y Ω)).re+‖Ω‖^2*ε := by
 let f:=fun x:ℝ=> max x 0; let g:= fun x:ℝ=> max (-x) 0; let u(x:ℝ):= x/(|x|+ε); let P:= cfc f A; let Q:= cfc g A; let U:= cfc u A
 have ep (x:ℝ):0 < |x|+ε:= add_pos_of_nonneg_of_pos (abs_nonneg _) v; have cu:Continuous u:= continuous_id.div (by fun_prop) (fun x=> (ep x).ne')
 have cf:Continuous f:=by unfold f; fun_prop
 have cg:Continuous g:=by unfold g; fun_prop
 have hq: IsSelfAdjoint U:= cfc_predicate ..; have hu:Commute U A:= (Commute.refl A).cfc_real u
 have e(x:ℝ): f x+g x=|x| ∧ f x-g x=x:= by
    unfold f g; rcases le_total (0:ℝ) x with a|b
    · rw [max_eq_left a,max_eq_right (by linarith),abs_of_nonneg a]; simp
    rw [max_eq_right b,max_eq_left (by linarith),abs_of_nonpos b]; simp
 have eq:P-Q=A:=by unfold P Q; rw [← cfc_sub f g A,show (fun x:ℝ=> f x-g x)=_root_.id from funext (fun _=>(e _).2), cfc_id ℝ A b]; all_goals fun_prop
 have Pq :0≤ P:= cfc_nonneg (fun x _=>le_max_right ..); have Qp:0≤Q:= cfc_nonneg (fun x _=>le_max_right ..)
 refine ⟨U,permitted u p,hq,norm_cfc_le zero_le_one (fun x _=>?_),?_⟩
 · unfold u; rw [Real.norm_eq_abs, abs_div, abs_of_pos (ep x), div_le_one (ep x)]; linarith
 have he:(inner ℂ (A Ω) (N Ω)).re ≤ (inner ℂ ((P+Q) Ω) Ω).re:= by
    rw [← eq]; -- ALL occurrences? also P references A (reducible) maybe
    have hp:= profitable q t Ω (permitted f p) Pq; have hq:= profitable q t Ω (permitted g p) Qp; change ‖inner ℂ (P Ω) (N Ω)‖ ≤_ at hp; change ‖inner ℂ (Q Ω) (N Ω)‖≤_ at hq
    simp only [sub_apply,add_apply,inner_sub_left,inner_add_left, Complex.add_re, Complex.sub_re]; refine le_trans (sub_le_sub (b:=‖inner ℂ (P Ω) (N Ω)‖) (c:=- ‖inner ℂ (Q Ω) (N Ω)‖) ?_ ?_) ?_ -- arg order
    · exact Complex.re_le_norm _
    · exact (abs_le.mp (Complex.abs_re_le_norm _)).1
    rw [sub_neg_eq_add]; exact add_le_add hp hq
 -- estimate norm of cfc difference
 have hku(d:ℝ): |d| *|d|=d*d:= by rw [←pow_two,←pow_two,sq_abs] -- tune
 have hcd : ‖(P+ Q) - U*A‖≤ ε:= by
    unfold P Q U
    -- only rewrite product A
    have hy: cfc u A * A = cfc (fun x=>u x*x) A:= by
      conv_lhs=> rhs; rw [← cfc_id' ℝ A b]
      rw [cfc_mul u (fun x:ℝ=>x) A]; -- layout
    rw [hy,← cfc_add A f g,←cfc_sub (fun x=> f x+g x) (fun x=>u x*x) A];
    · apply norm_cfc_le v.le; intro x _; rw [Real.norm_eq_abs,(e x).1]; unfold u;
      have h0 : |x| - x/(|x|+ε)*x=|x| *ε/(|x|+ε):= by field_simp; linarith [hku x]
      rw [h0, abs_of_nonneg (by positivity), div_le_iff₀ (ep x)]; nlinarith
    all_goals fun_prop
 let D':= (P+Q)-U*A
 have H': |(inner ℂ (D' Ω) Ω).re| ≤ ‖Ω‖^2*ε:= by
    exact (Complex.abs_re_le_norm ..).trans ((norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_right ((D'.le_opNorm Ω).trans (mul_le_mul_of_nonneg_right hcd (norm_nonneg _))) (norm_nonneg _)).trans (le_of_eq (by ring))))
 unfold D' at H'; rw [sub_apply,inner_sub_left,Complex.sub_re,mul_apply_eq_comp,Clasp.through_self U hq] at H'
 rw [Complex.mul_re,noImag b hq hu.symm]
 rw [show (star a).re=a.re from rfl,k]
 exact he.trans (by linarith [le_abs_self ((inner ℂ ((P+Q) Ω) Ω).re-(inner ℂ (A Ω) (U Ω)).re)])
end
end YM.BridgeClub
