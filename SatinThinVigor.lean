import YM.CF.Mew.Lace
/-! # universal pricing along large keys. Cauchy radius comparison. -/
set_option maxHeartbeats 270000
noncomputable section
namespace YM.CF.Mew
open Function Filter Metric Set MeasureTheory NormedSpace
open scoped Topology ContDiff Matrix Classical
set_option autoImplicit false
variable {J E:Type*}[Fintype J][DecidableEq J][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable {a:ℂ}
abbrev lensShift (J:Type*)(a:ℂ)(x:Key J):Key J:=a • x
lemma vigor_tip {g f:Key J→ E}(z:‖a‖≤1)(hg:River g)(hf:River f)(V:EqOn f (g∘lensShift J a) (hill J))(l:List J) : tipI f l = a^l.length • tipI g l:=by
 induction l generalizing f g with
 | nil=> simpa [tipI,lance,lensShift] using V roots
 | cons i l ih=>
    have hp:MapsTo (lensShift J a) (hill J) (hill J):=fun x hx=> hill_i.mpr fun i=>by unfold lensShift; rw [Pi.smul_apply,norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg a) (hill_i.mp hx i)).trans z
    let G:= fun x=> a • cutI g i x; have hz:EqOn (cutI f i) (G ∘ lensShift J a) (hill J):=by
       intro x hx; let F:= lensShift J a; let H:= update x i; have hm(y:ℂ): F (H y)=update (F x) i (a*y):=by ext j:1; by_cases h:i=j; subst j; simp [F,lensShift,H]; rw [update_of_ne (Ne.symm h)]; change a* H y j=_; rw [show H y j=x j from update_of_ne (Ne.symm h) y x]; rfl -- tune ; tactic focus then next goal leaks
       have hc: ∀ᶠ y:ℂ in 𝓝 0, f (update x i y)=g (update (F x) i (a*y)):=by filter_upwards [closedBall_mem_nhds (0:ℂ) zero_lt_one] with y hy; rw [← hm]; exact V (fill_I hx i hy)
       have he:HasDerivAt (fun y=> f (update x i y)) (G (F x)) 0:=by
          let u(y):=g (update (F x) i y); have h1:HasDerivAt u (cutI g i (F x)) (a*0):=by rw [mul_zero]; exact mitt hg (hp hx) i
          exact (h1.scomp (0:ℂ) (show HasDerivAt (fun y=> a*y) a 0 from (by simpa using ((hasDerivAt_id' 0).const_mul a)))).congr_of_eventuallyEq hc
       exact (mitt hf hx i).unique he
    change tipI (cutI f i) l = _; rw [ih ((hg.flow i).scale a) (hf.flow i) hz, show tipI G l=a • _ from tip_C (hg.flow i) a l,List.length_cons, smul_smul, pow_succ]; rfl -- tune G he LS
lemma vigor_bound {v:ℝ}(p:0<v)(q:v≤1) {f:Key J→ℂ} (l:List J) {m:ℝ} (u:∀ c:ℂ,River (f ∘ lensShift J c)) (h:∀ x, (∀ i, ‖x i‖ ≤ 2*v⁻¹)→ ‖f x‖ ≤ m): ‖tipI f l‖≤ v^l.length*m:=by
 let g:= f∘ lensShift J (v:ℂ)⁻¹; have he (c:ℝ)(b:0≤c): ‖(c:ℂ)‖=c:=by rw [Complex.norm_real,Real.norm_of_nonneg b]
 have ht:tipI f l=(v:ℂ)^l.length • tipI g l:=vigor_tip ((he _ p.le).trans_le q) (u ((v:ℂ)⁻¹)) ((u 1).cong (fun i _=>congrArg f (one_smul ℂ i).symm)) (fun i _=>congrArg f ((inv_smul_smul₀ (by exact_mod_cast p.ne':(v:ℂ)≠0) i).symm)) l
 rw [ht,norm_smul,norm_pow, he v p.le]; apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ v^l.length); apply lance_bound (u ((v:ℂ)⁻¹)) l ?_ _ roots
 intro x hx; apply h; intro i; unfold lensShift; rw [Pi.smul_apply,norm_smul,norm_inv,he v p.le]; apply (mul_le_of_le_one_right (by positivity) (hill_i.mp hx i)).trans (le_mul_of_one_le_left (by positivity) one_le_two)
end YM.CF.Mew
#print axioms YM.CF.Mew.vigor_bound
