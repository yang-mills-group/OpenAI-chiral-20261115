import YM.CF.Emu.Town
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia)
variable {α:Type*}{s:ℕ→Side}{R:ℕ→ℝ}{j:ℕ}{r v B:ℝ}
lemma payM (B:ℝ){f g:ℕ→ℂ}(h:Tendsto f atTop (𝓝 0))(u:∀ᶠ i in atTop,‖g i‖≤B): Tendsto (fun i=>g i*f i) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢; apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ (g:=fun i=> B*‖f i‖); exact (mul_zero B) ▸ h.const_mul B
 filter_upwards [u] with i e; rw [norm_mul]; exact mul_le_mul_of_nonneg_right e (norm_nonneg _)
open Classical in
lemma budgetO {I:ℕ→Type*}[∀ i,Nonempty (I i)](P:∀ i,I i→ Prop)(h:∀ᶠ i in atTop,∃ a,P i a):∃ v:∀ i,I i,∀ᶠ i in atTop,P i (v i):=by
 let v(i):= if h:∃ a,P i a then h.choose else Classical.arbitrary _; exact ⟨v,h.mono fun i k=>by unfold v; rw [dif_pos k]; exact k.choose_spec⟩
namespace Plot
variable (Q:Plot α R) (d:ℕ→Candle)(T:∀ i,Slide (s i) (d i))(M:ℕ→Jill.Male)(G:ℕ→E)(o:∀ i,Site (s i))(k:Yard s R)(p:∀ i,Wave (Single (s i)))(h:∀ᶠ i in atTop,Sea (Dofu _ (field (T i) j (M i))) (p i))
include h k
def stanza {N:Side}(Q:Op (Single N))(y:Wave (Single N))(Z:α→ Reader0 (Single N))(L:List α)(x:ℂ):= pRead y (mateK N) Z (quant Q) L-skyGlow (mateK N) Q y*x
lemma soot (H:1≤j)(u:0<r)(b: heave r≤v)(L:List α) : let W i:= Dofu _ (portT (T i) (M i) j r v); let Y i:= Q.tag (o i) (Kea.tax (d i)) (G i); let I(i):= iceK j (T i) (M i) r; Tendsto (fun i=>stanza (W i) (p i) (Y i) L (runes Q.rho L)/(I i:ℂ)) atTop (𝓝 0):=by
 intro W Y I
 have hp(i): 0<I i:=ice_p _ _ _ u; have hv:∀ᶠ i in atTop,r*pinch (s i)^2≤1/8:= ((k.shore.pow 2|>.const_mul r).eventually (ge_mem_nhds (by norm_num)))
 obtain ⟨c,g,K⟩:=rod j v b u; obtain ⟨B,e,C⟩:=octant j H u b
 let O(i):=portT (T i) (M i) j r v; let F(i):=mateV (risky (T i) j (M i) r) (v*pinch (s i))
 let P i (U:Stag (s i)→ Peb):= (∀ x,Clad (field (T i) j (M i) x) Aop (O i x) (F i x) (U x))∧ (∀ x,‖U x‖≤ c*(s i).val) ∧∀ x,‖O i x‖≤ c
 obtain ⟨V,h'⟩:=budgetO P (hv.mono fun i he=>by obtain ⟨M,W,D,E,L⟩:=K _ (k.even i) he (d i) _ (M i) v ⟨b,le_rfl⟩; exact ⟨M,W,D,L⟩)
 let U(i):= tilt (O i) (V i)
 have he(c': Slot):∀ᶠ i in atTop,FormU ((T i).u c') j (M i) r (c^2*Real.pi) (trackF (T i) (U i) c'):= h'.mono fun i hi=> attire (Y:=F i) hi.1 (k.even i) u g hi.2.1 hi.2.2 _
 let f(i):=runes (fun a b=>rankG (Dofu (s i) (U i)) (Y i a) (Y i b)) L
 let N:=runes Q.rho L; have hx:Tendsto f atTop (𝓝 N):=Q.sun T M U o k u (by positivity) he H G L
 have hb:Tendsto (fun i=> f i-N) atTop (𝓝 0):=by simpa only [sub_self] using hx.sub_const N
 let S(i):ℂ:=skyGlow (mateK _) (W i) (p i)
 refine (payM B hb (g:=fun i=> S i / I i) ?_).congr' ?_
 · filter_upwards [h,hv] with i y z; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (hp i).le]; exact (div_le_iff₀ (hp i)).2 (C _ (k.even i) z (d i) _ (M i) v b le_rfl (p i) y)
 filter_upwards [h,h'] with i hh y; obtain ⟨l,u,v⟩:=y; unfold stanza; rw [frown (torn _ (k.even i) j _ _ _ _ l) (tickB _) hh (Y i) (fun a=>nac_k ..)]; change S i/_ *(f i-_)=(S i*_ - S i*_)/_
 rw [show laneP _ _ _= Dofu _ (U i) from (tall_s (O i) (V i)).symm]; change _= (S i*f i-S i*N)/_; ring
lemma hoot (H:1≤j)(u:0<r)(L:List α) : let Y i:= Q.tag (o i) (Kea.tax (d i)) (G i); let I(i):= iceK j (T i) (M i) r; Tendsto (fun i=>stanza 1 (p i) (Y i) L (runes Q.rho L)/(I i:ℂ)) atTop (𝓝 0):=by
 intro Y I; obtain ⟨A,V⟩:= risky_card j H _ u; let w:= A*4+1; let W(n:ℕ):ℝ:= (n+1:ℝ)*heave r
 let X(n:ℕ)(i:ℕ):= stanza (Dofu _ (portT (T i) (M i) j r (W n))) (p i) (Y i) L (runes Q.rho L)
 have ht(n:ℕ)(g:n<w):Tendsto (fun i:ℕ=>X n i/(I i:ℂ)) atTop (𝓝 0):=Q.soot d T M G o k p h H u (show heave r≤W n by unfold W; exact le_mul_of_one_le_left (heave_p _).le (by simp)) L
 have hm:Tendsto (fun i:ℕ=> ∑ n∈range w, (bead w (-1) n:ℂ)* (X n i/(I i:ℂ))) atTop (𝓝 (∑ n∈range w,(0:ℂ))):=by
    refine tendsto_finsetSum _ fun n vn=>?_ ; simpa only [mul_zero] using (ht n (mem_range.mp vn)).const_mul (bead w (-1) n:ℂ)
 rw [sum_const_zero] at hm; refine hm.congr (fun i=>?_); let N:= s i; let R:=risky (T i) j (M i) r; let X'(n:ℕ):= Dofu (s i) (portT (T i) (M i) j r (W n)); let B(n:ℕ):ℂ:=bead w (-1) n
 have hp: ∑ n∈range w,B n • quant (X' n)=(1:FC (Single _)):=by
    let t:= heave r * pinch (s i); have hp(n:ℕ): (W n*pinch (s i))= (n+1:ℝ)*t:=by unfold W; rw [mul_assoc]
    unfold X' portT; simp_rw [hp]; refine redeem R w ?_ t; have ht:R.card≤A:=V _ (k.even i) (d i) (T i) (M i); unfold w; omega
 let U:= mateK N; let Q:=runes Q.rho L; let F':=rollC (ton ∘ Y i) L; let M:=p i
 change (∑ n∈range w,B n*(X n i/(I i:ℂ))) =_
 have ht(A: FC (Single (s i))) : (∑ n∈range w,B n * inner ℂ U (acts (A*quant (X' n)) M))=inner ℂ U (acts A M):=by
    nth_rw 2 [show A=A*1 from (mul_one _).symm]; rw [←hp, Matrix.mul_sum,act_sum,inner_sum]; apply sum_congr rfl; intro n _; rw [Matrix.mul_smul,act_smul,inner_smul_right]
 -- rearr.
 simp_rw [← mul_div_assoc, ← Finset.sum_div]; unfold stanza pRead; rw [quant_one,mul_one,skyGlow,quant_one,act_one]; congr 1 -- tune
 change ∑ n∈range w,B n*(inner ℂ U (acts (F'*quant (X' n)) M)-inner ℂ U (acts (quant (X' n)) M)*Q)=inner ℂ U (acts F' M)-inner ℂ U M*Q; have he:=ht 1; simp only [one_mul,act_one] at he; simp_rw [mul_sub,sum_sub_distrib]; rw [ht F']; congr 1; simp_rw [← mul_assoc, ← sum_mul]; rw [he]
end Plot
end YM.CF.Emu
