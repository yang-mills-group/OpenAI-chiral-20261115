import YM.SU5.FiniteGaugeData.ArchiveK.Kestel
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable (G:E4≃ₗᵢ[ℝ] E4)(p:Space3)(x y:E4)
local notation "Σ"=> seedX G p
local notation "T"=> sailX G
local notation "Δ"=> depthG G x
local notation "Q"=> pulseG G p
lemma choir : pass (pulseG G p)=0:=by
 let f:= prodM; let P:= brushQ Σ; let R:= brushQ T; let z:=Complex.I*‖p‖; have hx: (Q)= P+ z • R:=rfl
 have he : (∑ i:Axis,P i* R i)=0:=by
    change (∑ i:Axis,(↑((Σ).ofLp i):ℂ)*(↑((T).ofLp i):ℂ))=0; norm_cast; rw [← pis, sail_zero]
 rw [hx,pass]; have ht:∑ i:Axis,P i^2=((‖p‖^2:ℝ):ℂ):=by unfold P; convert spendQ Σ using 1; rw [seed_size]
 have hb:∑ i:Axis,R i^2=(1:ℂ):=by change pass _=_; unfold R; rw [spendQ,sail_size]; norm_num
 simp_rw [Pi.add_apply,Pi.smul_apply, smul_eq_mul, show ∀ a b k:ℂ,(a+k*b)^2=a^2 + (2*k)*(a*b)+ k^2*b^2 from (by intros; ring),sum_add_distrib,← Finset.mul_sum]; rw [he,ht,hb]; unfold z; push_cast; ring_nf; simp
abbrev murmur(x:E4)(p:Momentum):ℂ:= Complex.I*(∑ i:Axis,p i*x i)
abbrev say(n:ℕ)(z:ℂ):= ∑ j∈Finset.range n,z^j/(j.factorial:ℂ)
lemma mur_fee: ‖murmur y (pulseG G p)‖ ≤8*‖y‖*‖p‖:=by
 unfold murmur; rw [norm_mul,norm_I,one_mul]; let c:=2*‖p‖*‖y‖; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>c) fun j t=> ?_).trans_eq ?_); · rw [norm_mul,Complex.norm_real]; exact mul_le_mul (pulse_pay ..) (arm_abs ..) (abs_nonneg _) (by positivity)
 unfold c; simp [Axis]; ring
-- basis polynomial powers modulo null. use fixed alternate finite set of tuples ABB(n)=ℕ³ each ≤2n to avoid addition re-index cost and work over ℕ max. at n, multiplying a term by any one axis increases ≤2 choose max ≤2n+2; odd parity. prove `BendX n f` and allows add,mul in spans. Need convert to exact coefficients. Keep post max; no explicit continuity y.
variable (n:ℕ)
abbrev EdgeM:= (ℕ × ℕ × ℕ) × Bool
def coon(n:ℕ):Finset EdgeM:=((range (2*n+1)) ×ˢ (range (2*n+1)) ×ˢ (range (2*n+1))) ×ˢ univ -- left? 
def kaon (u:EdgeM)(p:Momentum): ℂ:= (p 0)^u.1.1*(p 1)^u.1.2.1* (p 2)^u.1.2.2 * (p 3)^(if u.2 then 1 else 0:ℕ)
lemma coon_in (u v w:ℕ)(b:Bool): (((u,v,w),b):EdgeM)∈ coon n↔ u≤2*n ∧ v≤2*n∧ w≤2*n :=by simp [coon] -- fine
lemma coon_cnt : (coon n).card=2*(2*n+1)^3:=by rw [coon]; simp; ring
section spanC
open scoped Classical
def CrownX (n:ℕ)(f:Momentum→ℂ): Prop:= ∃ x:EdgeM→ℂ,∀ p:Momentum,pass p=0→ f p=∑ i∈coon n,x i*kaon i p
local notation "Φ"=> CrownX
local notation "Ο"=> coon
lemma crown_atom (n:ℕ)(u:EdgeM)(p:u∈coon n): CrownX n (kaon u):= by refine ⟨fun i=> if i=u then 1 else 0, fun i h=>?_⟩; simp [ite_mul,p];
lemma crown_times {f:Momentum→ℂ}(h:CrownX n f) (c:ℂ): CrownX n (fun p=> c*f p):=by obtain ⟨i,h⟩:=h; refine ⟨fun j=>c*i j,fun x b=>?_⟩; dsimp only; rw [h _ b]; simp_rw [Finset.mul_sum,mul_assoc]
lemma crown_zero : CrownX n 0:=⟨0,fun i _=>by simp⟩
lemma crown_func (n:ℕ){f g: Momentum→ℂ}(h:CrownX n f)(t:∀ p:Momentum,pass p=0→g p=f p): CrownX n g:=by obtain ⟨i,h⟩:= h; exact ⟨i,fun i he=>(t i he).trans (h i he)⟩
lemma crown_collect {J:Type*}(S:Finset J)(F:J→Momentum→ℂ)(h:∀ i∈S,CrownX n (F i)) : CrownX n (fun x=>∑ i∈ S,F i x):= by
 choose! x e using h; refine ⟨fun i=>∑ j∈ S,x j i,fun p t=>?_ ⟩; change _=∑ i∈ _, _; -- e j hi p
  dsimp only; rw [sum_congr rfl (g:=fun i=>∑ j∈ (coon n),x i j*kaon j p) (fun i hi=> e i hi p t),sum_comm]; simp_rw [Finset.sum_mul]
lemma crown_plus {f g:Momentum→ℂ}(h: CrownX n f)(t:CrownX n g): CrownX n (fun i=> f i+g i):=by obtain ⟨x,e⟩:=h; obtain ⟨y,g⟩:=t; refine ⟨x+y,fun i p=>?_⟩; dsimp only; rw [e i p,g i p]; simp_rw [Pi.add_apply,add_mul,sum_add_distrib]; -- tune name reuse g.
lemma pulse_last(q:Momentum)(h:pass q=0): q 3^2= -(q 0^2+q 1^2+q 2^2):=by unfold pass at h; norm_num [Axis,Fin.sum_univ_succ] at h; change q 0^2+(q 1^2+(q 2^2+q 3^2))=0 at h; linear_combination h
private lemma course0 (a b c:ℕ)(g:Bool)(e:((a,b,c),g)∈ coon n):
 CrownX (n+1) (fun p=>p 0*kaon ((a,b,c),g) p) ∧ CrownX (n+1) (fun p=>p 1*kaon ((a,b,c),g) p) ∧ CrownX (n+1) (fun p=>p 2*kaon ((a,b,c),g) p) ∧ CrownX (n+1) (fun p=>p 3*kaon ((a,b,c),g) p):= by
 obtain ⟨ha,hb,hc⟩:= (coon_in ..).1 e; have H(a' b' c':ℕ)(g':Bool)(x:a'≤a+2)(y:b'≤b+2)(z:c'≤c+2) : CrownX (n+1) (kaon ((a',b',c'),g')):=crown_atom _ _ ((coon_in ..).2 (by omega)); refine ⟨crown_func _ (H (a+1) b c g (by omega) (by omega) (by omega)) ?_,crown_func _ (H a (b+1) c g (by omega) (by omega) (by omega)) ?_, crown_func _ (H a b (c+1) g (by omega) (by omega) (by omega)) ?_, ?_⟩ <;> try (intro p _; unfold kaon; dsimp only; ring)
 cases g
 · refine crown_func _ (H a b c true (by omega) (by omega) (by omega)) fun p _=> ?_; simp [kaon]; ring
 let h1:= H (a+2) b c false (by omega) (by omega) (by omega); let h2:= H a (b+2) c false (by omega) (by omega) (by omega); let h3:= H a b (c+2) false (by omega) (by omega) (by omega); let h0:=(crown_plus _ (crown_plus _ h1 h2) h3); refine crown_func _ (crown_times _ h0 (-1)) (fun i j=>?_); simp [kaon]; linear_combination (i 0^a*i 1^b*i 2^c)*(pulse_last i j) -- tune direction
lemma crown_boost (f:Momentum→ℂ)(h:CrownX n f)(a:Axis): CrownX (n+1) (fun i=>f i*i a):=by
 obtain ⟨K,H⟩:=h; let F(x:EdgeM)(p:Momentum):=K x*(p a*kaon x p); have hx(x:EdgeM)(b:x∈coon n): CrownX (n+1) (F x):=by
    obtain ⟨⟨v,w,i⟩,z⟩:= x; unfold F; apply crown_times; obtain ⟨U,A,B,D⟩:= course0 n v w i z b; fin_cases a <;> assumption
 refine crown_func _ (crown_collect (n+1) (coon n) F hx) (fun p t=>?_); rw [H _ t,Finset.sum_mul]; unfold F; apply Finset.sum_congr rfl; intro i _; ring
lemma crown_inc (k:ℕ)(v:k≤n){f:Momentum→ℂ}(g:CrownX k f): CrownX n f:=by
 obtain ⟨x,c⟩:= g; let K:=coon k; let H:=crown_collect n K (fun i p=>x i*kaon i p) (fun i p=> by obtain ⟨⟨a,b,c⟩,u⟩:= i; apply crown_times n (crown_atom _ _ ?_); have hx: a ≤2*k ∧ b≤ _ ∧ _ := (coon_in k a b c u).1 p; exact (coon_in ..).2 (by omega)); exact crown_func _ H c
lemma crown_pow : CrownX n (fun p => murmur x p^n):= by
 induction n with
 | zero => refine crown_func 0 (crown_atom _ (((0,0,0),false):EdgeM) ?_) (fun i h=>?_ ); simp [coon]; simp [kaon] -- precedence
 | succ n ih=>
    let f(i:Axis)(p:Momentum):= (Complex.I*x i)*(murmur x p^n*p i); have he:= crown_collect (n+1) (univ:Finset Axis) f (fun i h=> crown_times _ (crown_boost _ _ ih i) _); refine crown_func _ he (fun i _=>?_); unfold f; rw [pow_succ]; nth_rw 2 [murmur]; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
lemma crown_say : CrownX n (fun p=>say n (murmur x p)):=by
 unfold say; refine crown_collect n (range n) _ (fun i h=>?_); refine crown_func _ (crown_times n (crown_inc n i (Finset.mem_range.mp h).le (crown_pow x i)) (i.factorial:ℂ)⁻¹) (fun p _=>?_); ring
#print axioms crown_say
end spanC
end YM.CF.Window.ArchiveK
