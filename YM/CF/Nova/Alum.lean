import YM.CF.Nova.Rune
/-! Normalization estimates for ULTRAWEAK stop-scale on these tori. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Nova
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc Pic MeasureTheory Vale RG Wilson Scree Skye
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {m L B N:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l r t w η τ:ℝ}{P:Grasp Y B e}{H:Pearl P}(D:Span H K b v c l r n)(p:n≤ (CSide m B).val)
def slim (N:Side)(r:ℝ)(s:ℕ):ℝ:=r/(N.val:ℝ)^s
lemma slim_p(v:0<r)(N)(s):0<slim N r s:=by unfold slim; have:=nPos N; positivity
structure Size(m B:Side)(p:ℝ)where -- data threshold, all field cost k*...rel
 x:ℝ
lemma ratios (u:ℕ)(a v b c:ℝ)(g:0<a)(h:0<v)(w:0<b)(H:0<c)(V:ℕ):∃ s k K:ℝ,0<s ∧0<k∧0<K∧ ∀ n:Side,let t:= slim n s (V+10)
                        t ≤1 ∧ (n.val:ℝ)^10*t ≤ min v 1 ∧ a*(slim n K V)=c*(n.val:ℝ)^10*t ∧ a*K≤ b/(2*poseX)∧ ((More n).val:ℝ)^2*slim n k (2+(V+10)*u) ≤ a*t^u:=by
 let s:=min (min v (1:ℝ)) (b/(2*poseX*c)); have hp:0<s:=lt_min (lt_min h one_pos) (by apply div_pos w; have he:=pose_p; positivity)
 refine ⟨s, a*s^u/4,c*s/a,hp,by positivity,by positivity,fun n=>?_⟩; intro t; let N:ℝ:= n.val; have he:1≤N:=by unfold N; exact_mod_cast n.property
 have ht:0<N:=zero_lt_one.trans_le he; have hl:N^10*t=s/N^V:=by change N^10*(s/N^_)=_; rw [pow_add]; field_simp
 have hv:t≤1:=by unfold t slim; apply le_trans (div_le_self hp.le (one_le_pow₀ he)); exact (min_le_left ..).trans (min_le_right ..)
 refine ⟨hv,?_,?_,?_,?_⟩
 · change N^10*_≤_; rw [hl]; exact (div_le_self hp.le (one_le_pow₀ he)).trans (min_le_left ..)
 · rw [mul_assoc]; change a*((c*s/a)/N^V)=c*(N^10*t); rw [hl]; field_simp
 · have hg:=pose_p; calc
    _ = c*s:=by field_simp
    _ ≤ _:=by have he:s≤ b/(2*poseX*c):=min_le_right ..; rw [le_div_iff₀ (by positivity)] at he; rw [le_div_iff₀ (by positivity)]; linarith
 change ((↑(n.val*2):ℝ))^2*( (a*s^u/4)/N^ (2+(V+10)*u))≤ a*(s/N^ (V+10))^u; rw [div_pow,pow_add N (2:ℕ),pow_mul]; apply le_of_eq; push_cast; unfold N; field_simp; ring
lemma manyK:∃ (u:ℕ)(a:ℝ),1 ≤ u ∧0<a∧∀ (m:Side)(V:Bkg (Domain m B)) (x t:ℝ),0<x →flags x V=∅ →0<t→t≤1→ (Domain m B).val^2*x ≤ a*t^u→ ∃ F:Cart (Domain m B),∃ d:Candle,speedB d (Domain m B) ∧lawnK (gauge F V) (Kea.tax d) t:=by
 obtain ⟨J,k,K,u,v,c,Q⟩:= habits; obtain ⟨C,w,V⟩:= snow_b
 refine ⟨J,k/C,u,by positivity,fun m f x t p g H X Y=>Q (Domain m B) f (C*x) (by positivity) (V _ f x g) t H X ?_⟩; apply le_trans (b:=C*((Domain m B).val^2*x)); · exact le_of_eq (by ring)
 exact (mul_le_mul_of_nonneg_left Y w.le).trans_eq (by field_simp)
-- reusable size demand. connects Orbit/Z. small only. τ marker test orders.
structure CoolR (D:Span H K b v c l r n)(m:Side)(t:ℝ)(σ: ℝ):Prop where
 pose:t>0
 data:t≤1
 frame:n ≤ (CSide m B).val
 cap:(CSide m B).val^10*t≤ min v 1
 coat:duty (CSide m B).val t c 0≤ b/(2*poseX)
 roll:∀ U:Config group (Domain m B), flags σ U=∅→∃ f:Cart (Domain m B), ∃ d:Candle, speedB d (Domain m B)∧ lawnK (gauge f U) (Kea.tax d) t
lemma shiftC(V:ℕ):∃ m' q:ℕ,∃ s k:ℝ,0<s∧ 0<k ∧ ∀ m:Side,m'≤(CSide m B).val → CoolR D m (slim (CSide m B) s (V+10)) (slim (CSide m B) k q):=by
 obtain ⟨u,a,h,L,Y⟩:=manyK (B:=B); obtain ⟨s,k,K,hk,v,w,T⟩:= ratios u a v b c L D.xP D.pos (zero_lt_one.trans_le D.cP) V
 refine ⟨n,2+(V+10)*u,s,k,hk,v,fun m u' =>?_⟩; let N:= CSide m B; let t:= slim N s (V+10); obtain ⟨p,h,f,k',hN⟩:= T N; have ht:=slim_p hk N (V+10)
 refine ⟨ht,p,u',h,?_,fun U g=>Y _ U _ t (slim_p v _ _) g ht p hN⟩; unfold duty; rw [zero_mul,add_zero]; refine le_trans (le_of_eq (show _= _ from f.symm)) ?_; apply le_trans (mul_le_mul_of_nonneg_left (div_le_self w.le (one_le_pow₀ (a:=(N.val:ℝ)) (by exact_mod_cast N.property) (n:=V))) L.le); exact k'
lemma Calder (Q:CoolR D m t a)(x T:ℝ)(g:0<x)(s:x ≤ a)(M:Jill.Male)(A: Clip):
 let U:=primal A (Domain m B) T x; let μ:=prior group (Domain m B); let G:=fun i:Config group (Domain m B)=>changeM P i M; let z:=integralF m B U G μ; let B':=Kea.angel m P M*(∫ i,U i∂ μ); let S:=gleam m P M
 Tab H id μ U G M (K*(CSide m B).val) t 0 1 ∧ 0<B'∧ B'*(b/(2*poseX)) ≤(S*z).re∧ |(S*z).im|≤ duty (CSide m B).val t c 0* B' ∧ qpay U G μ ≤2*c*B' ∧ z≠0:=by
 intro U μ G z B' S; let P:=Q.pose; have hp:=Q.frame; have ht:=tab_z D hp A T x t a M g s P Q.data Q.cap Q.roll; obtain ⟨r,h,H'⟩:= poised D hp ht P Q.data Q.cap; have hh:0<B':=mul_pos (angel_p H D.stmt (D.plan _ hp).1 D.p D.eP M (D.plan _ hp).2) (prim_score _ _ _ _ g); -- tune
 have he:B'*(b/(2*poseX)) ≤(S*z).re:=by apply le_trans _ r; rw [mul_comm (∫ _,_ ∂ _), one_mul]; apply mul_le_mul_of_nonneg_left _ hh.le; have hv:= D.pos; have ht:= pose_p; apply le_trans _ (sub_le_sub_left Q.coat _); field_simp; linarith
 refine ⟨ht,hh,he,?_,?_,fun hv=>?_⟩
 · exact h.trans_eq (by unfold B'; rw [mul_comm (Kea.angel ..)]) -- check args
 · exact H'.trans_eq (by unfold B'; ring)
 rw [hv,mul_zero,Complex.zero_re] at he; have ht:= pose_p; exact not_lt.mpr he (by have :=D.pos; positivity)
end YM.CF.Nova
