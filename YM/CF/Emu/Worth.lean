import YM.CF.Emu.Pit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Nova Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc MeasureTheory Vale RG Wilson Scree Skye
variable {α:Type*}{N:Side}{o:Site N}{L B:Side}{j n:ℕ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{e b c v K a l r τ w u:ℝ}{P:Grasp Y B e}{H:Pearl P}{m:Side}{f:ℕ→Side}{R T W:ℕ→ℝ}
variable (D:Span H K b v c l r n)
local notation "N'"=> CSide m B
include D
lemma earn(A:Clip)(M:Jill.Male)(T x:ℝ)(o:Site N')(R:ℝ)(z:α→TagT)(L:List α)(g:0<x)(s:x ≤ a)(C:CoolR D m τ a): Integrable (fun i:Bkg (Domain m B)=> primal A (Domain m B) T x i • valA o i R z L (changeM P i M)) (prior group (Domain m B)) :=by
 let F:= CapX m B e; let S:= Calm group (Domain m B) x; let H'(i):= Real.exp (-(T* basicP A (n:=Domain m B) i)); have hm:=D.plan m C.frame
 let K(y:F):= muni o y.val R z L; let Y(y:F):= changeM P y.val M; have hv:Continuous K:= (teg o R z L).comp continuous_subtype_val; have hp:Continuous (fun y:F=> H' y.val • valA o y.val R z L (Y y)):= by
    have he: Continuous fun y:F=>H' y.val:= (Real.continuous_exp.comp (Continuous.neg (continuous_const.mul (ren_c A)))).comp continuous_subtype_val
    exact he.smul (Continuous.inner continuous_const ((acts_cont.comp hv).clm_apply (concur H D.stmt D.eP D.p M hm.1)))
 let W(x:Bkg (Domain m B)):= H' x • valA o x R z L (changeM P x M); have hr : IntegrableOn W {x:Bkg (Domain m B)|Guard x e} (prior group (Domain m B)):= (continuousOn_iff_continuous_restrict.mpr hp).integrableOn_compact (Phase.cover_closed ..|>.isCompact) -- tune
 change Integrable _ _; rw [show (fun i:Bkg (Domain m B)=>primal _ _ _ _ i • valA o i R z L (changeM P i M))= S.indicator W from ?_]; swap;
 · funext i; unfold W primal H'; by_cases h:i∈S; · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
   rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,zero_smul]
 refine (integrable_indicator_iff (calm_m ..)).2 (hr.mono_set ?_); intro y h; have ht:0<primal A _ T x y:=by rw [primal, Set.indicator_of_mem h]; exact Real.exp_pos _
 obtain ⟨f,d,v,y'⟩:= (Calder D C x T g s M A).1.inner y ht; exact (CostKin D C.frame M _ f (spiral d v) y' C.pose C.data C.cap).1 -- inspect call implicit p
lemma skybed (C:∀ᶠ i in atTop, CoolR D (f i) (T i) (W i))(q:ℕ)(h:Tendsto (fun i=>Greek (aj B f i)^(10+q)*T i) atTop (𝓝 0)) : BeamG D f T 0 q:=by
 refine ⟨C.mono fun i k=>⟨k.frame,k.pose,k.data,k.cap,le_rfl⟩,h,?_⟩; simp
lemma strategy (T:ℝ)(p:0<T)(h:n≤(N').val): ∃ x v:ℝ,x>0∧ CoolR D m v x∧ v ≤T:=by
 let N:= N'; obtain ⟨W,b',hp,hW,Z⟩:= manyK (B:=B); let n:=Greek N; have ht:0<n:=nPos _; let t:=min (min T 1) (min ((min v 1)/n^10) (b/(2*poseX*c*n^10))) -- precedence! need (min v 1)/n^10
 have hc:0<c:=zero_lt_one.trans_le D.cP; have hv:0<t:=by unfold t; have he:=D.xP; have hx:=D.pos; have hp:=pose_p; exact lt_min (lt_min p one_pos) (lt_min (by positivity) (by positivity))
 let u:= ((More N).val:ℝ); have hu :0<u:= nPos _; let x:= b'*t^W/(u^2); have hs:t≤1:=le_trans (min_le_left ..) (min_le_right T 1); have hz:0<x:=by unfold x; positivity; -- tune
 refine ⟨x,t,hz,⟨hv, hs,h,?_,?_,fun U g=>Z _ U x t hz g hv hs ?_⟩,(min_le_left ..).trans (min_le_left T 1)⟩
 · have ht': t ≤ (min v 1)/n^10:=(min_le_right ..).trans (min_le_left ..); change n^10*t ≤_; rw [mul_comm]; exact (le_div_iff₀ (pow_pos ht _)).1 ht'
 · unfold duty; rw [zero_mul,add_zero]; have hj:=pose_p; change c*n^10*t≤_; have hp:t≤ b/(2*poseX*c*n^10):=(min_le_right ..).trans (min_le_right ..); field_simp at hp ⊢; linarith
 change u^2*x≤_; unfold x; field_simp; simp
omit D
lemma roam_n(y:Yard (aj B f) R) : Tendsto (fun i=>Greek (aj B f i)) atTop atTop:=tendsto_atTop_mono' _ ((growG y).mono fun _ u=>u.1) y.high
include D
theorem pilot(y:Yard (aj B f) R) : ∃ σ:ℕ→ℝ,(∀ᶠ i in atTop,0<σ i) ∧ ∀ A:Clip,∀ β x:ℕ→ℝ,(∀ᶠ i in atTop,0<x i∧x i≤σ i)→∀ M:ℕ→Jill.Male,∀ o:∀ i,Site (aj B f i),∀ Q:Plot α R,∀ J:List α,
  let Z i:= primal A (Sep B f i) (β i) (x i); let μ i:= prior group (Sep B f i); let X(i)(U:Bkg (Sep B f i)):= changeM P U (M i); let Ψ i:= fun u:Bkg (Sep B f i)=> Z i u • valA (o i) u (R i) (Q.pal i) J (X i u); let V i:= integralF (f i) B (Z i) (X i) (μ i); (∀ᶠ i in atTop,V i≠0∧ Integrable (Ψ i) (μ i))∧ Tendsto (fun i=>(∫ x,Ψ i x∂μ i)/V i) atTop (𝓝 (runes Q.rho J)):=by
 let t(i):= slim (aj B f i) 1 (10+i+1); let N(i):=Greek (aj B f i); have ht:= roam_n y; have hx:∀ᶠ i in atTop,n ≤ (aj B f i).val:=(ht.eventually (eventually_ge_atTop (n:ℝ))).mono fun i h=>by change ↑n ≤ (↑(aj B f i).val:ℝ) at h; exact_mod_cast h
 let U i (x:ℝ × ℝ):= 0<x.1 ∧ CoolR D (f i) x.2 x.1 ∧ x.2 ≤ t i
 obtain ⟨v,V⟩:= budgetO U (hx.mono fun i h=> by obtain ⟨x,v,e,H,T⟩:=strategy D (t i) (slim_p one_pos ..) h; exact ⟨(x,v),e,H,T⟩)
 let G(i):= (v i).2; let Pc(i):=(v i).1
 refine ⟨Pc,V.mono fun i u=>u.1,fun A β x u M o Q J=>?_⟩; intro Z μ X Ψ S; let l:= 3*J.length
 have he:∀ q:ℕ, BeamG D f G 0 q:=by
   intro q; refine skybed D (T:=G) (W:=Pc) (V.mono fun i u=>u.2.1) q (squeeze_zero' (V.mono fun i u=>mul_nonneg (pow_nonneg (nPos (aj B f i)).le _) (show 0<G i from u.2.1.pose).le) ?_ (show Tendsto (fun i=>(N i)⁻¹) _ _ from tendsto_inv_atTop_zero.comp ht)); filter_upwards [V,eventually_ge_atTop q] with i v u; have hv:1≤N i:=by unfold N Greek; exact_mod_cast (aj B f i).property
   have hx:=show G i≤ t i from v.2.2; refine (mul_le_mul_of_nonneg_left hx (pow_nonneg (nPos _).le _)).trans ?_; change N i^_*(1/N i^_)≤ _; apply le_trans (mul_le_mul_of_nonneg_left (show 1/N i^(10+i+1) ≤ 1/N i^(10+q+1) from div_le_div_of_nonneg_left one_pos.le (by positivity) (pow_le_pow_right₀ hv (by omega))) (show 0≤N i^(10+q) by positivity)); rw [pow_add (N i) (10+q) 1]; apply le_of_eq; field_simp -- tune
 have hI:∀ᶠ i in atTop,Integrable (Ψ i) (μ i) :=(V.and u).mono fun i e=> earn D A (M i) _ _ _ _ _ _ e.2.1 e.2.2 e.1.2.1
 obtain ⟨w,W⟩:= elfin (a:=1) D Z Q J y (he _) o M (fun _=>id) X μ (by norm_num) ((V.and u).mono fun i ⟨z,s⟩=> (Calder D z.2.1 (x i) (β i) s.1 s.2 _ A).1) (u.mono fun i e=>prim_score _ _ _ _ e.1) hI; exact ⟨w.and hI,W⟩
end YM.CF.Emu
