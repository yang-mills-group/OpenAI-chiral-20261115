import YM.CF.Emu.Quay
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Nova Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc MeasureTheory
variable {α:Type*}{N:Side}{o:Site N}{L B:Side}{j n:ℕ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{e b c v K a l r τ w u:ℝ}{P:Grasp Y B e}{H:Pearl P}{m:Side}{f:ℕ→Side}{R T W:ℕ→ℝ}
-- weight schedule local non RG stopping estimates allow tiny w rescaled. 
variable (D:Span H K b v c l r n)
include D
lemma dawn(q:ℕ)(p:BeamG D f T W q): Tendsto (fun i=> duty (Greek (aj B f i)) (T i) c (W i)) atTop (𝓝 0):=by
 have hx:0≤c:=zero_le_one.trans D.cP
 let N(i):= Greek (aj B f i); have he(i):1≤N i:=by unfold N Greek; exact_mod_cast (aj B f i).property
 have ht:= (p.wave.const_mul c).add (p.fine.mul_const (2*c)); simp only [zero_mul,mul_zero,add_zero] at ht; refine squeeze_zero' ?_ ?_ ht
 exact (p.ok.mono fun i g=>show 0≤_ from add_nonneg (mul_nonneg (mul_nonneg hx (pow_nonneg (show 0≤ N i by have hp:=he i; positivity) _)) g.2.1.le) (mul_nonneg g.2.2.2.2 (mul_nonneg (by norm_num) hx)))
 filter_upwards [p.ok] with i hp; obtain ⟨l,v,t,h,hv⟩:=hp; unfold duty; change _≤ c*(N i^_*_)+_; rw [← mul_assoc c]; apply add_le_add; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (he i) (Nat.le_add_right ..)) hx) v.le; exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hv (one_le_pow₀ (he i))) (mul_nonneg (by norm_num) hx)
variable {I:ℕ→Type*} [∀ i,MeasurableSpace (I i)] [∀ i,Nonempty (I i)]
lemma elfin (A:∀ i,I i→ℝ)(Q:Plot α R)(J:List α)(y:Yard (aj B f) R)(t:BeamG D f T W (3*J.length))(o:∀ i,Site (aj B f i))(M:ℕ→Jill.Male)(U:∀ i,I i→ Bkg (Sep B f i))(G:∀ i,I i→wit (f i) B)(μ:∀ i,Measure (I i))(bA:0<a)(p:∀ᶠ i in atTop, Tab H (U i) (μ i) (A i) (G i) (M i) (K*Greek (aj B f i)) (T i) (W i) a)(w:∀ᶠ i in atTop,0<∫ t,A i t ∂μ i) (hp:∀ᶠ i in atTop,Integrable (fun t=> A i t • valA (o i) (U i t) (R i) (Q.pal i) J (G i t)) (μ i)) : let V i:= ∫ t, A i t • valA (o i) (U i t) (R i) (Q.pal i) J (G i t)∂μ i; let P i:= integralF (f i) B (A i) (G i) (μ i)
      (∀ᶠ i in atTop, P i ≠0) ∧ Tendsto (fun i=> V i/P i) atTop (𝓝 (runes Q.rho J)):=by
 intro V X
 let B'(i):= Kea.angel (f i) P (M i); let Y i:=∫ x,A i x∂ μ i; let b':= a*b/(2*poseX); let t':=duty; have hz:0<b':=by unfold b'; have he:=pose_p; have hp:=D.pos; positivity
 have he: ∀ᶠ i in atTop, Y i *B' i *b' ≤ ‖X i‖∧ 0< B' i:=by
    filter_upwards [p,t.ok, (dawn D (3*J.length) t).eventually (gt_mem_nhds hz),w] with i u h he ht; obtain ⟨hi,h,hR,hz',v⟩:=h; -- tune
    have hp:= (poised D hi u h hR hz').1; let D':=Nova.gleam (f i) P (M i); let y:=duty (Greek (aj B f i)) (T i) c (W i); have hx : ‖D'‖=1:= (gleams D hi (M i)).1; have hD:0<B' i:= angel_p H D.stmt (D.plan _ hi).1 D.p D.eP _ (D.plan _ hi).2; refine ⟨le_trans ?_ ((Complex.re_le_norm (D'*X i)).trans_eq (by rw [norm_mul,hx,one_mul])),hD⟩
    refine le_trans ?_ hp; change _≤ Y i*B' i*(a*b/poseX-y); apply mul_le_mul_of_nonneg_left _ (mul_nonneg (show 0<Y i from ht).le hD.le); change y < b' at he; have hk:b'+b'=a*b/poseX:=(by unfold b'; ring)
    linarith only [he,hk]
 have hk : ∀ᶠ i in atTop, X i ≠0:= (he.and w).mono fun i e=> norm_pos_iff.mp (lt_of_lt_of_le (mul_pos (mul_pos e.2 e.1.2) hz) e.1.1); refine ⟨hk,Metric.tendsto_nhds.mpr fun l hl=>?_⟩
 have hm(i)(p:0<Y i):∃ x,0<A i x:=by by_contra h; push Not at h; exact not_lt.mpr (integral_nonpos h) p
 let T':=runes Q.rho J; let r' := l/2*b'
 have hh:= valQ D Q J y t o M U G μ A p (w.mono hm) r' (by unfold r'; positivity)
 filter_upwards [p,w,hp,hh,he,hk] with i hi w hp v ht hD
 let g(x:I i):= valA (o i) (U i x) (R i) (Q.pal i) J (G i x); let c':=r'*B' i
 let F(x:I i):= A i x • (g x-inner ℂ (mateK _) (G i x)*T')
 have hF(x): F x=A i x • (g x) - (A i x • beamM (f i) B (G i x))*T':= by unfold F; rw [smul_sub]; rw [Algebra.smul_mul_assoc]; rfl
 have he:Integrable F (μ i):=by rw [funext hF]; exact hp.sub (hi.rich.mul_const _)
 have hr:‖V i-X i*T'‖ ≤ l/2*‖X i‖:=by
    rw [← show (∫ y,F y ∂μ i)=V i-X i*T' from (by simp_rw [hF]; rw [integral_sub hp (hi.rich.mul_const _),MeasureTheory.integral_mul_const]; rfl)]; apply (norm_integral_le_integral_norm _).trans; refine le_trans (integral_mono (g:=fun x=> A i x*c') he.norm (hi.bright.mul_const c') ?_) ?_
    · intro j; change ‖F j‖≤_; unfold F; rw [norm_smul,Real.norm_of_nonneg (hi.same _)]; rcases eq_or_lt_of_le (hi.same j) with h|h; · change _≤ A i j * c'; rw [←h,zero_mul,zero_mul]
      exact mul_le_mul_of_nonneg_left (vigor _ _ _ _ _ _ _ (v j h)) h.le
    rw [integral_mul_const]; refine le_trans ?_ (mul_le_mul_of_nonneg_left ht.1 (by positivity : 0≤ l/2)); change Y i*c' ≤_; unfold c' r'; apply le_of_eq; ring
 rw [dist_eq_norm,show V i/X i-T'= (V i-X i*T')/ X i from (by field_simp),norm_div]; exact lt_of_le_of_lt ((div_le_iff₀ (norm_pos_iff.mpr hD)).mpr hr) (by linarith)
end YM.CF.Emu
