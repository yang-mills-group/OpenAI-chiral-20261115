import YM.CF.Vp929.Analysis.Polynomial

/-! Uniform exponential stencil inequality: no conditioning number or spacing of positive nodes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.VolumeRate
open Set Function Complex Polynomial
open Finset (range)
open scoped BigOperators
private abbrev B := Set.Ioo (0:ℝ) 1
private def weightT (a b : ℂ) (t : ℝ) : ℂ:= (t:ℂ)^a*((1-t:ℝ):ℂ)^b
private lemma weight_jet (k:ℕ) (A:ℝ) (ha:0 ≤ A) : ∃ C:ℝ, 1 ≤ C ∧ ∀ a b:ℂ, k ≤ a.re → k ≤ b.re → ‖a‖≤ A→ ‖b‖≤ A→ BJet C k (weightT a b) := by
 have h (a b:ℂ)(ha:0≤a.re)(hb:0≤b.re)(x:ℝ)(p:x∈B) : ‖weightT a b x‖ ≤ 1:= by
   unfold weightT; rw [norm_mul]; have hm:0 < 1-x := sub_pos.mpr p.2
   refine mul_le_one₀ (?_) (norm_nonneg _) (?_)
   · rw [norm_cpow_eq_rpow_re_of_pos p.1]; exact Real.rpow_le_one p.1.le p.2.le ha
   rw [norm_cpow_eq_rpow_re_of_pos hm]; exact Real.rpow_le_one hm.le (by linarith [p.1]) hb
 induction k generalizing A with
 | zero=> refine ⟨1,le_rfl,?_⟩; push_cast; exact fun a b ha hb _ _=> h a b ha hb
 | succ n ih=>
    obtain ⟨C,H,U⟩:=ih (A+1) (by linarith); have hc:0≤C:=by linarith
    refine ⟨(A*C+A*C)+1,by nlinarith,?_⟩; push_cast; intro a b ha hb qa qb
    have ap:0 < a.re:=by linarith [Nat.cast_nonneg (α:=ℝ) n]
    have bp:0 < b.re:=by linarith [Nat.cast_nonneg (α:=ℝ) n]
    refine ⟨fun x p=>(h a b ap.le bp.le x p).trans (by nlinarith),fun x=> a * weightT (a-1) b x + (-b)* weightT a (b-1) x, fun x p=>?_,?_⟩
    · have hp:= p.1; have P:= hasDerivAt_ofReal_cpow_const hp.ne' (r:=a) (fun e=>by simp [e] at ap)
      have T:= hasDerivAt_ofReal_cpow_const (sub_pos.mpr p.2).ne' (r:=b) (fun e=>by simp [e] at bp)
      have O := T.scomp x ((hasDerivAt_id' x).const_sub 1)
      unfold weightT; apply (P.mul O).congr_deriv; simp; ring
    have p (z:ℂ)(f:ℝ→ℂ) (e:‖z‖ ≤ A)(g:BJet C n f): BJet (A*C) n (fun x=> z * f x):= g.clm ((ContinuousLinearMap.mul ℝ ℂ) z) (fun x=> by change ‖z*x‖ ≤ _; rw [norm_mul]; gcongr) ‹0≤A›
    have F:= U (a-1) b (by simp;linarith) (by linarith) (le_trans (norm_sub_le ..) (by simp [qa])) (by linarith)
    have G:= U a (b-1) (by linarith) (by simp;linarith) (by linarith) (le_trans (norm_sub_le ..) (by simp [qb]))
    exact ((p _ _ qa F).add (p (-b) _ (by simpa using qb) G)).mono (by linarith)

def widthS (N:ℕ):ℕ := N+2
local notation "M" => widthS
/-- Final stencils. Use all indices in this finset. -/
def panel (N:ℕ):Finset ℕ:= range (2*M N+1)
def wooden (N:ℕ)(c w:ℝ)(i:ℕ):ℝ:= c + (i-(M N:ℝ))*w
private def squash (x:ℝ) := x/(x+1)
private lemma squash_ok {x:ℝ} (hx:0<x): squash x∈B:= ⟨by unfold squash; positivity,(div_lt_one (by linarith)).mpr (by linarith)⟩
-- undo factor
private lemma squash_power (x:ℝ) (hx:0<x)(z:ℂ)(n:ℕ) : weightT (n+z) (n-z) (squash x) = (x:ℂ)^z * (x:ℂ)^n / (↑(x+1:ℝ):ℂ)^(2*n) := by
 let t:=squash x; let u:= (1-t)
 have ht:0<t:= (squash_ok hx).1; have hp:=squash_ok hx
 have hu:0<u:= sub_pos.mpr hp.2; have V:u=1/(x+1):= by dsimp [u,t,squash]; field_simp; ring
 have A:(t:ℂ)≠0:= by exact_mod_cast ht.ne'
 have B:(u:ℂ)≠0:= by exact_mod_cast hu.ne'
 have X:= add_pos hx (by norm_num : (0:ℝ)<1)
 change (t:ℂ)^((n:ℂ)+z)*(u:ℂ)^((n:ℂ)-z)=_
 rw [cpow_add _ _ A,cpow_sub _ _ B,cpow_natCast,cpow_natCast]
 have e: (t:ℂ)=(x:ℂ)*(u:ℂ):= by norm_cast; rw [V]; unfold t squash; ring
 have p:(t:ℂ)^z=(x:ℂ)^z*(u:ℂ)^z:= by
    rw [cpow_def_of_ne_zero A, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'),cpow_def_of_ne_zero B,←Complex.exp_add,e,log_ofReal_mul hx B,add_mul,ofReal_log hx.le]
 rw [p,e,mul_pow]
 have r:(u:ℂ)^z≠0:= by rw [cpow_def_of_ne_zero B]; exact exp_ne_zero _
 have R:(u:ℂ)^n*(u:ℂ)^n=((↑(x+1:ℝ):ℂ)^(2*n))⁻¹ := by
   rw [←pow_add,← two_mul,V]; push_cast; simp
 -- use cancellation
 rw [div_eq_mul_inv,div_eq_mul_inv]; show _ = _ * _
 rw [← R]; grind

set_option maxHeartbeats 800000 in
private lemma numerator (N:ℕ): ∃ C:ℝ, 1≤C ∧ ∀ z:ℂ, ‖z‖≤ 2 → ∀ s: Finset ℝ, s.card ≤ N → (∀ x∈ s,0<x) → ∃ p:ℕ→ℂ, (∑ i∈panel N, ‖p i‖) ≤ C ∧ ∀ x∈s, (x:ℂ)^z * (x:ℂ)^(M N)=∑ i∈panel N, p i * (x:ℂ)^i := by
 classical
 let n:= M N; have u:n=N+2:=rfl
 obtain ⟨C,H,Y⟩:=weight_jet N ((n:ℝ)+2) (by positivity); have hc : 0≤C:=by linarith
 obtain ⟨B,hB,U⟩:= jetCoeff N; have pB:0≤B:=by linarith
 let Q (i:ℕ): ℂ[X]:= X^i*(X+Polynomial.C 1)^(2*n-i)
 refine ⟨(∑ i∈panel N, ∑ j∈range (N+1), (B*C+B*C)*‖(Q j).coeff i‖)+1, by exact le_add_of_nonneg_left (by positivity),?_⟩; intro z hz s hs he
 let f:=weightT (n+z) (n-z)
 have P:BJet C N f:= by
    have hR:= abs_re_le_norm z
    refine Y _ _ ?_ ?_ ((norm_add_le ..).trans ?_) ((norm_sub_le ..).trans ?_)
    · simp [u]; linarith [neg_abs_le z.re]
    · simp [u]; linarith [le_abs_self z.re]
    all_goals simp; linarith
 let t:= s.image squash; have hu:= Finset.card_image_le (s:=s) (f:=squash)
 have hT:t.card≤N+1:= hu.trans (by omega)
 have ht:(t:Set ℝ)⊆ Ioo 0 1:=fun p h=>by obtain ⟨x,hx,rfl⟩:= Finset.mem_image.mp h; exact squash_ok (he _ hx)
 have Hr:= P.clm Complex.reCLM (C:=1) (fun x=> by simpa using abs_re_le_norm x) (by positivity)
 have Hi:= P.clm Complex.imCLM (C:=1) (fun x=> by simpa using abs_im_le_norm x) (by positivity)
 rw [one_mul] at Hr Hi; obtain ⟨p,hp,H₁,h₁⟩:= U C hc _ Hr _ hT ht; obtain ⟨q,hq,H₂,h₂⟩:= U C hc _ Hi _ hT ht
 let a (j:ℕ): ℂ:= (p.coeff j:ℂ)+q.coeff j*I
 refine ⟨fun i=>∑ j∈range (N+1), a j*(Q j).coeff i, (Finset.sum_le_sum ?_).trans (le_add_of_nonneg_right (by positivity)),?_⟩
 · intro i _; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>?_); rw [norm_mul]; refine mul_le_mul_of_nonneg_right ((norm_add_le ..).trans (add_le_add ?_ ?_)) (norm_nonneg _)
   · simpa using h₁ j
   · simpa [norm_mul] using h₂ j
 intro x hx; have e:= he x hx; let y:=squash x; have hy:y∈ t:=Finset.mem_image_of_mem _ hx
 have D:f y = ∑ j∈range (N+1), a j * (y:ℂ)^j:= by
    rw [←Complex.re_add_im (f y), ←(show p.eval y=(f y).re from hp hy), ←(show q.eval y=(f y).im from hq hy), eval_eq_sum_range' (n:=N+1) (by omega),eval_eq_sum_range' (n:=N+1) (by omega)]; simp [a,Finset.sum_mul,←Finset.sum_add_distrib,add_mul,mul_right_comm]
 let J:ℂ := ↑(x+1:ℝ); have hj:J≠0:= ofReal_ne_zero.mpr (by linarith)
 refine Eq.trans (show (x:ℂ)^z*(x:ℂ)^n=f y*J^(2*n) by rw [show f y=_ from squash_power x e z n,div_mul_cancel₀ _ (by positivity : J^(2*n)≠0)]) ?_
 rw [D,Finset.sum_mul]; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm (s:=panel N)]; refine Finset.sum_congr rfl ?_; intro j v; have h:= Finset.mem_range.mp v; simp_rw [mul_assoc,←Finset.mul_sum]
 unfold panel; rw [← eval_eq_sum_range' ?_]; change _ * (_ * _) = _ * Polynomial.eval _ (Q j); congr 1
 · have p : (Q j).eval (x:ℂ) = (x:ℂ)^j * J^(2*n-j) := by simp [Q,J]
   rw [p,show (y:ℂ)=(x:ℂ)/J from Complex.ofReal_div ..,div_pow,show J^(2*n)=J^j * J^(2*n-j) from by rw [←pow_add]; congr; omega]; field_simp
 have:= natDegree_mul_le (p:=(X^j:ℂ[X])) (q:=((X+Polynomial.C 1)^(2*n-j))); rw [natDegree_pow_X_add_C,natDegree_X_pow] at this; change (Q j).natDegree < 2*n+1; unfold Q; omega

/-- Universal stencil coefficient grant, usable for any real slopes, any normed vector space.
 Stencil centre `c`, spacing `w` (applications use positive `w`, using negative works too). -/
theorem slopedStencil (N:ℕ): ∃ C:ℝ, 1 ≤ C ∧ ∀ c w:ℝ, ∀ z:ℂ, ‖z‖ ≤ 2 → ∀ s: Finset ℝ, s.card ≤ N → ∃ p:ℕ→ℂ, (∑ i∈panel N, ‖p i‖) ≤ C ∧ ∀ x∈s, exp ((x:ℂ)*((c:ℂ)+z*w)) = ∑ i∈panel N, p i * exp ((x:ℂ)* (wooden N c w i:ℂ)) := by
 classical
 obtain ⟨C,H,U⟩:=numerator N; refine ⟨C,H,?_⟩; intro c w z hz s hs
 let f:= fun x:ℝ=> Real.exp (x*w); let t:=s.image f
 have :∀ x∈t, 0<x:= by intro x hx; obtain ⟨y,h,rfl⟩:= Finset.mem_image.mp hx; exact Real.exp_pos _
 obtain ⟨p,h,P⟩:=U z hz t (Finset.card_image_le.trans hs) this; refine ⟨p,h,?_⟩; intro x hx; have he:=P (f x) (Finset.mem_image_of_mem _ hx); let A:ℂ:= ↑(f x); have hy:A=exp ((x:ℂ)*w):=by simp [A,f]
 have hA:A≠0:= hy ▸ Complex.exp_ne_zero ((x:ℂ)*w)
 let D:ℂ:= exp ((x:ℂ)*c); have G (i:ℕ): (A:ℂ)^i=exp ((i:ℂ)*x*w):= by rw [hy,← Complex.exp_nat_mul,mul_assoc]
 calc
 _=D*(A^z):=by
    unfold D; rw [cpow_def_of_ne_zero hA, hy,log_exp,←exp_add]; congr 1; ring
    all_goals simp [Real.pi_pos, Real.pi_pos.le]
 _=(∑ i∈panel N,p i*(A:ℂ)^i)*D/A^(M N):=by rw [show (∑ i∈panel N,p i*(A:ℂ)^i)=A^z*A^(M N) from he.symm]; field_simp
 _=_:=by
    rw [Finset.sum_mul,Finset.sum_div]; refine Finset.sum_congr rfl ?_; intro i hi
    change _ = _ * exp _; unfold D wooden; rw [G,G, mul_assoc,←exp_add, mul_div_assoc,← exp_sub]; push_cast; ring_nf
end YM.CF.VolumeRate
