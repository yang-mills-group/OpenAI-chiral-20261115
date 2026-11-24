import YM.CF.Onyx.Self
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{r C:ℝ}{M:Male}
lemma ding (H:1≤j)(p:0<r)(u:0<C)(a:Axis):∃ G:ℝ,0<G∧∀ {N: Side}{A B:Site N→Peb}{M:Male}{s x:Offset N}, Even N.val→FormU s j M r C A→FormU x j M r C B→16*pinch N<zone→∀ w:ℝ,|w|≤1→ x.val=s.val+beam a (w*(2*pinch N))→ ‖(∑ k,B k)-(∑ k,A k)‖≤ G/pinch N:=by
 obtain ⟨V,b,h,v,P⟩:=bedK H p a; obtain ⟨c,g,K⟩:=gross H p u; obtain ⟨u',z,Z⟩:=bead_bound 8; obtain ⟨D,hD,L⟩:=cost_c; let y:=(c+u'*c)*V^8; let W:= max y b; have hz:0<W:=lt_max_of_lt_right v
 refine ⟨W*D,by positivity,fun {N} {A B} {M} {s x} hN f l e w t ht=>?_⟩
 have ht'(i:ℕ): ∑ k:Site N, A (k+wrap N (i • step a))=∑ k,A k:= Equiv.sum_comp (Equiv.addRight _) A
 rw [← show ∑ k,countR w a k A B=(∑ k,B k)-(∑ k,A k) from (by unfold countR; rw [sum_sub_distrib,sum_comm]; simp_rw [← Finset.smul_sum,ht',← sum_smul, ← Complex.ofReal_sum,bead_one 8 (by decide), Complex.ofReal_one,one_smul])]
 have he:=pinch_pos N; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun k=>W/pinch N*(Jill.tall k^8)⁻¹) ?_).trans ?_)
 · intro i _; let m:= pinch N; let y':=tall i; have hp:0< y':=one_pos.trans_le (tall_p _); rw [← div_eq_mul_inv,div_div]; rcases le_total V (tall i) with h|h
   · exact (P hN f l e w t ht i h).trans (div_le_div_of_nonneg_right (le_max_right ..) (mul_nonneg he.le (show 0≤y'^8 by positivity))) -- tune
   refine le_trans ?_ (div_le_div_of_nonneg_right (le_max_left ..) (show 0≤m*y'^8 by unfold m; positivity))
   have hm: ∑ j∈range 8,‖(bead 8 w j:ℂ) • A (i+wrap N (j • step a))‖ ≤ u'*(c/m):=by
     refine (sum_le_sum (g:=fun j=> |bead 8 w j| *(c/m)) ?_).trans (by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (Z w t) (by unfold m; positivity))
     intro j _; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (K hN f _) (abs_nonneg _)
   unfold countR; refine (norm_sub_le ..).trans ((add_le_add (K hN l _) ((norm_sum_le ..).trans hm)).trans ?_); rw [le_div_iff₀ (show 0<m*y'^8 by unfold m; positivity)]; change _*(_*y'^8)≤_; rw [←mul_assoc,show (c/pinch N+u'*(c/m))*m=c+u'*c from (by unfold m; field_simp)]; unfold y; gcongr
 rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (L _) (by positivity : 0≤ W/pinch N)).trans_eq (by ring)
lemma berth(H:1≤j)(p:0<r)(u:0<C): ∃ D:ℝ,0<D∧∀ {N: Side}{A:Site N→Peb}{M:Male}{s:Offset N},Even N.val→ FormU s j M r C A→16*pinch N<zone→ ‖∑ k,A k‖ ≤ D/pinch N:=by
 choose K h P using fun a=> ding H p u a; let D:= K 0+∑ a,K a; have hz:0<D:=add_pos_of_pos_of_nonneg (h _) (sum_nonneg fun _ _=>(h _).le); refine ⟨D,hz,fun {N} {A} {M} {s} hN f t=>?_⟩; let V(s:Offset N):=fac s j M r
 have h'(o:Finset Axis): ‖∑ k,V (fill s o) k‖≤∑ i∈o,K i/pinch N:=by
   induction o using Finset.induction_on with
   | empty=> rw [show fill s ∅=zeroF N from (by apply Subtype.ext; funext i; simp [fill,zeroF]),show ∑ k,V _ k=_ from nil_t j M r N hN]; simp
   | @insert i o h g=>
     let w:= s.val i/(2*pinch N); have hz:=pinch_pos N; have he:w*(2*pinch N)=s.val i:=by unfold w; field_simp
     have hx:= (b_abs s.val i).trans s.property; have hw:|w|≤1:=by have hk :|w| *(2*pinch N)= |s.val i|:=(by rw [← he,abs_mul,abs_of_pos (by positivity : 0<2*pinch N)]); nlinarith
     have ht: (fill s (insert i o)).val=(fill s o).val+beam i (w*(2*pinch N)):=by rw [he]; funext j; by_cases v:j=i<;> simp [fill,v,h,step,beam]
     rw [sum_insert h]; exact (norm_le_norm_sub_add _ (∑ k,V (fill s o) k)).trans (add_le_add (P i hN (fab _ _ M _ _ u) (fab _ _ _ _ _ u) t w hw ht) g)
 have he:= h' univ; rw [show fill s univ=s from (by apply Subtype.ext; funext i; simp [fill])] at he
 rw [show D=K 0+_ from rfl, add_div,sum_div]; exact (norm_le_norm_sub_add _ (∑ k,V s k)).trans (add_le_add (P 0 hN (fab _ _ M _ _ u) f t 0 (by norm_num) (by simp [beam])) he)
lemma Yard.shore{S:ℕ→Side}{R:ℕ→ℝ}(h:Yard S R): Tendsto (fun i=>pinch (S i)) atTop (𝓝 0):=by
 refine squeeze_zero' (Eventually.of_forall fun _=>(pinch_pos _).le) ?_ h.water; filter_upwards [h.high.eventually (eventually_ge_atTop 1)] with i u; exact le_mul_of_one_le_left (pinch_pos _).le u
lemma Yard.sol{S:ℕ→Side}{R:ℕ→ℝ}(h:Yard S R)(H:1≤j)(p:0<r)(u:0<C)(A:∀ i,Site (S i)→Peb)(M:ℕ→Male)(s:∀ i,Offset (S i))(f:∀ᶠ i in atTop,FormU (s i) j (M i) r C (A i)) : Tendsto (fun i=> bore (s i) (R i) 0 (A i)) atTop (𝓝 0):=by
 obtain ⟨D,d,P⟩:=berth H p u; rw [tendsto_zero_iff_norm_tendsto_zero]; have he:=h.water.pow 3|>.const_mul (D/(Real.pi^4)); simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero] at he
 apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ he; filter_upwards [f,h.shore.eventually (gt_mem_nhds (show 0<zone/16 by exact div_pos zone_pos (by norm_num)))] with i u q; simp only [bore,liv,charK,mode_zero,one_smul]; have hR:=h.pos i; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; refine (mul_le_mul_of_nonneg_left (P (h.even _) u (by change pinch (S i)<zone/16 at q; linarith)) (by positivity : 0≤R i^3/((S i).val:ℝ)^4)).trans_eq ?_; unfold pinch; have ht:=nPos (S i); field_simp
end YM.CF.Onyx
