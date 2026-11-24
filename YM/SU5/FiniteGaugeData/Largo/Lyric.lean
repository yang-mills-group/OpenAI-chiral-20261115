import YM.SU5.FiniteGaugeData.Largo.Hocus
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Polynomial MeasureTheory
open scoped Topology BigOperators Pointwise Polynomial
-- work with mathlib convention of Fourier series. `Cf (+k)` uses minus exp. 
variable (o:Rim)(p:Slab o)
local instance τg : Fact (0<τ):=⟨tau_pos⟩
local notation "Γ"=> AddCircle τ
abbrev Corona:= ContinuousMap (AddCircle τ) ℂ
include p
lemma hymn_at (t:ℝ): ContinuousAt (hymn o) (t:ℂ):= ((slippery o p).smoothOff (t:ℂ) (by rintro ⟨⟨⟨i,j⟩,l⟩,e⟩; have he:=(altitude o i j l).1; rw [e,Complex.ofReal_im,abs_zero] at he; exact (bush_pos o i p).ne he)).continuousAt
lemma hymn_reel : Continuous ((hymn o) ∘ ((↑):ℝ→ℂ)):= continuous_iff_continuousAt.mpr fun x=> (hymn_at o p x).comp continuous_ofReal.continuousAt
def tag : Corona := ⟨(epoch o p).lift, continuous_quot_lift _ (hymn_reel o p)⟩
lemma tag_eq(t:ℝ) : tag o p (↑t:Γ)=hymn o t:= Periodic.lift_coe (epoch o p) t
lemma tag_star : star (tag o p) = tag o p:=by
 ext1 v; induction v using Quotient.inductionOn with| _ v=>
 change star (tag o p (v:AddCircle τ))=tag o p (v:AddCircle τ); rw [tag_eq, onActual o p]; rw [tsum_star]; simp
omit p
private lemma ofInt(i:ℤ)(x:ℝ): fourier i (x: Γ)=Complex.exp (i*(Complex.I*x)):=by
 rw [fourier_coe_apply]; apply congrArg Complex.exp; unfold τ; push_cast; field_simp [Real.pi_ne_zero]
private lemma partL (i:ℕ)(x:ℝ):fourier (i:ℤ) (x:Γ)= (Complex.exp (Complex.I*x))^i:=by rw [ofInt, Int.cast_natCast, Complex.exp_nat_mul]; -- push casts first

private def Lube (i:ℤ): Corona →ₗ[ℂ] ℂ where
 toFun f:= fourierCoeff f i
 map_add' f g:= congrFun (fourierCoeff.add (Continuous.integrable_of_hasCompactSupport f.continuous (HasCompactSupport.of_compactSpace _)) (Continuous.integrable_of_hasCompactSupport g.continuous (HasCompactSupport.of_compactSpace _))) i
 map_smul' k f:= fourierCoeff.const_smul ..
private lemma lube_eq(i:ℤ)(f:Corona):Lube i f=fourierCoeff f i:=rfl
private lemma lube_star(i:ℤ)(f:Corona): Lube (-i) (star f) = star (Lube i f) := by
 rw [lube_eq,lube_eq,fourierCoeff,fourierCoeff,Complex.star_def,← integral_conj]; apply integral_congr_ae; refine Eventually.of_forall fun x=>?_ ; change _ • star (f x)=starRingEnd ℂ (_ * f x); rw [fourier_neg,map_mul]; rfl
private lemma shave (i j:ℤ)(f:Corona): Lube i (fourier j*f)= Lube (i-j) f:=by rw [lube_eq,lube_eq,fourierCoeff, fourierCoeff]; apply integral_congr_ae; refine Eventually.of_forall fun x=>?_ ; simp only [ContinuousMap.mul_apply, show -(i-j)= -i+j from (by omega), smul_eq_mul, fourier_add,mul_assoc]
def literal (p:Slab o)(j:ℤ):ℂ:=fourierCoeff (tag o p) j
include p
lemma lit_star(i:ℤ) : star (literal o p i)= literal o p (-i):= by unfold literal; simp_rw [←lube_eq]; rw [←lube_star, tag_star]
omit p
private lemma spread (f:Corona)(A₀:Finset ℤ)(h:∀ i:ℤ,i∉A₀→ Lube i f=0): ∃ G:ℂ→ℂ,Differentiable ℂ G ∧ ∀ x:ℝ,G x=f x:=by
 refine ⟨fun x:ℂ=> ∑ i∈ A₀,Lube i f*Complex.exp (i*(Complex.I*x)),by fun_prop,?_⟩; intro x
 have hv : Summable (fourierCoeff f):= summable_of_ne_finset_zero h; let P:= fun i:ℤ=> fourierCoeff f i • (fourier i (x:Γ)); have he:HasSum P (f x):= has_pointwise_sum_fourier_series_of_summable hv _
 have hP: ∀ i∈ A₀,P i=Lube i f*Complex.exp (i*(Complex.I*x)):=fun i _=>by unfold P; rw [ofInt]; rfl
 exact (sum_congr rfl fun i v=> (hP i v).symm).trans ((tsum_eq_sum (f:=P) (s:=A₀) (fun i p=> by unfold P; rw [show fourierCoeff f i=0 from h i p,zero_smul])).symm.trans he.tsum_eq)
variable {n:ℕ}(g:Fin n→ℕ)(v: Injective g)(x:Fin n→ ℂ)
private def buildP : Polynomial ℂ := ∑ i:Fin n, monomial (g i) (x i)
private lemma buildH(z:ℂ): (buildP g x).eval z= ∑ i:Fin n, (x i)*z^(g i):= by unfold buildP; simp only [eval_finsetSum, eval_monomial]; -- tune
include v in
private lemma buildL (p:x≠0): buildP g x≠0:= by
 intro k; apply p; funext i; let A:= g i; rw [show x i=(buildP g x).coeff A from ?_, k]; rfl
 unfold buildP; rw [Polynomial.finsetSum_coeff, sum_eq_single i]; · simp [A]
 · intro j h x; simp [A,Polynomial.coeff_monomial,v.eq_iff,x]
 simp
private lemma smallG (f:Corona)(h:∀ᶠ i:ℤ in atBot,Lube i f=0) : ∀ᶠ i:ℤ in atBot,Lube i ((∑ j:Fin n, x j • fourier (g j : ℤ))*f)=0:=by
 filter_upwards [(eventually_all (ι:=Fin n)).mpr fun j=>(tendsto_atBot_add_const_right (α:=ℤ) _ (-(g j:ℤ)) tendsto_id).eventually h] with i t; rw [sum_mul,map_sum]; refine sum_eq_zero fun j _=>?_ ; rw [Algebra.smul_mul_assoc,map_smul,shave,sub_eq_add_neg,show Lube (i+- (g j:ℤ)) f=0 from t j,smul_zero]
include v in
private lemma mirrorG (N:ℕ)(h:∀ i:Fin n,g i≤N): Injective (fun i:Fin n=> N - g i):= fun i j t=> v (by have hx:= h i; have hy:=h j; dsimp only at t; omega) -- tune
include p v
lemma sends (w:x≠0):∃ᶠ i:ℤ in atBot,(∑ j:Fin n,x j *literal o p (i-g j))≠0:=by
 intro S; let X:= buildP g x; let G(r:ℝ):=r; let Q:Corona:= ∑ i: Fin n, x i • fourier (g i:ℤ); let N:= (univ:Finset (Fin n)).sup g; let W:Fin n→ℕ:= fun i=> N-g i; let y:= star x; let Y:= buildP W y; let V:Corona:=∑ i: Fin n,y i • fourier (W i:ℤ); have hx:∀ j:Fin n,g j ≤ N:= fun _=> Finset.le_sup (f:=g) (mem_univ _); let M:=tag o p
 let F:= Q*M; have hF:∀ᶠ i:ℤ in atBot,Lube i F=0:= S.mono fun i t=> by unfold F Q; change ¬¬_=_ at t; rw [sum_mul,map_sum]; simp_rw [Algebra.smul_mul_assoc,map_smul,shave]; exact not_not.mp t
 let Z:= V*F; let A:Corona:= fourier (N:ℤ); have vP:V= A*star Q:=by
                               unfold A Q V; rw [star_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ext1 u; -- tune h' shift
                               change star (x i)*fourier (W i:ℤ) u= _ * star (x i * fourier (g i:ℤ) u); rw [show (W i:ℤ)= (N:ℤ)+ -(g i:ℤ) from (by unfold W; rw [Nat.cast_sub (hx i)]; ring),fourier_add,fourier_neg]; simp only [star_mul, Complex.star_def,mul_comm,mul_left_comm] -- tune
 have hK: star A * A=(1:Corona):=by ext1 u; change star (fourier (N:ℤ) u) * fourier (N:ℤ) u=(1:ℂ); rw [Complex.star_def,← fourier_neg,←fourier_add, neg_add_cancel, fourier_zero]
 have hr: star Z= (star A*star A)*Z:=by
    have hx:star M=M:=tag_star o p; unfold Z; rw [vP]; unfold F; simp only [star_mul, star_star,hx]; calc
        _=(M*(star Q)* Q*star A) := by ring
        _= _:=by nth_rw 1 [← one_mul (M*star Q*Q*_)]; nth_rw 1 [← hK]; ring
 have h0: ∀ᶠ i:ℤ in atBot,Lube i Z=0:= smallG W y F hF; have ht: ∀ᶠ i:ℤ in atBot,Lube i (star Z)=0:= by
    let S:ℤ:=-(N:ℤ)+ -(N:ℤ); have he: star A*star A=fourier S:=by ext1 u; change star (fourier (N:ℤ) u)*star (fourier (N:ℤ) u)=_; unfold S; rw [fourier_add, fourier_neg]; rfl
    filter_upwards [(tendsto_atBot_add_const_right (α:=ℤ) _ (-S) tendsto_id).eventually h0] with i p; rw [hr,he,shave,sub_eq_add_neg]; exact p
 obtain ⟨a,c⟩:= eventually_atBot.mp h0; obtain ⟨b,f⟩:= eventually_atBot.mp ht; let B:= Icc a (-b)
 obtain ⟨H,v',T⟩:= spread Z B (fun i p=> by by_cases t:i≤a; exact c i t; apply star_injective; rw [←lube_star,star_zero]; apply f; by_contra! hz; exact p (mem_Icc.mpr ⟨by omega,by omega⟩))
 refine notRational o p (Y*X) (mul_ne_zero (buildL W (mirrorG g v _ hx) y (by simpa only [y, Ne,star_eq_zero] using w)) (buildL _ v _ w)) H v' (fun t=>?_); rw [eval_mul,T]; unfold Z V F Q; change ((∑ i:Fin n,y i • fourier (W i:ℤ)): Corona) (t:Γ)* _=_; simp_rw [ContinuousMap.mul_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply, partL, M, tag_eq]; rw [←mul_assoc]; simp only [Y,X,buildH, smul_eq_mul] -- tune

lemma reachG (w:x≠0):∃ᶠ i:ℤ in atTop,(∑ j:Fin n,x j*literal o p (i+g j))≠0:=by
 have he:= sends o p g v (star x) (by simpa using w); intro S; refine he ((tendsto_neg_atBot_atTop.eventually S).mono (fun i u=> ?_)); intro g; apply g; change ¬¬_=0 at u; rw [←star_inj,star_sum,star_zero]; simp_rw [star_mul, lit_star o p, Pi.star_apply,star_star, show ∀ x:ℤ,-(i-x)= -i+x from fun _=>by omega,mul_comm (b:=x _) _]; exact not_not.mp u
end YM.CF.Window.Largo
