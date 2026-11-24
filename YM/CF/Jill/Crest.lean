import YM.CF.Jill.Pine
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Jill
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
variable {N:Side}{j:ℕ}{r:ℝ}{M:Male}
lemma neigh {x y u:Bin}(p:Bound Real.pi x)(q:Bound Real.pi u)(h:peers (x+y) u): |‖x‖-‖u‖| ≤‖y‖ :=by
 have he:= (peaks q h.flip).trans (norm_add_le ..)
 have hx:= h.both (-y); rw [add_neg_cancel_right] at hx; have hu:= (peaks p hx).trans (norm_add_le ..); rw [norm_neg] at hu; rw [abs_le]; constructor <;> linarith
lemma high_cost(t s:RayH)(h:t.M=s.M)(x:Bin)(g:tmap x∈realCube zone)(hx:peers x s.x)(p:0<r)(k:cup N j t.M r t.x=disk j t.M t.x)(l:cup N j s.M r s.x=disk j s.M s.x): Complex.log (shell j t.M.val (tmap x)/shell j t.M.val (tmap t.x))= (cold N j s.M r s.x:ℂ)-(cold N j t.M r t.x:ℂ):=by
 have ht:tmap t.x∈realCube zone:= base_subset_realCube zone_pos (b_base t.cap); have hp:=hx.map_shell g (base_subset_realCube zone_pos (b_base s.cap)) s.M.val j
 unfold cold; rw [k,l]; have hK:0<disk j t.M t.x := k ▸ cup_p t.M p t.x; have hL:0<disk j s.M s.x:= l ▸ cup_p s.M p s.x
 rw [h,← hp,express _ s.x _ (base_subset_realCube zone_pos (b_base s.cap)) s.M.property,express _ t.x _ ht s.M.property]; rw [h] at hK
 change Complex.log ((disk j s.M s.x:ℂ)/(disk j s.M t.x:ℂ))=_; rw [← Complex.ofReal_div,← Complex.ofReal_log (div_nonneg hL.le hK.le), Real.log_div hL.ne' hK.ne']; push_cast; ring
variable (s:Offset N)(a:Axis)(w:ℝ)
def pingH (k:Site N)(f:ℕ):Bin:=pm (k+wrap N (f • step a))+s.val
def tipC (k:Site N):Bin:=pm k+s.val+beam a (w*(2*pinch N))
def cot (k:Site N)(j p:ℕ)(r:ℝ)(M: Male):=cold N j M r (tipC s a w k)-∑ i∈range p,bead p w i * cold N j M r (pingH s a k i)
lemma rod_u(n:ℕ)(h:n<8): (↑n:ℝ) ≤ 8:= le_of_lt (by exact_mod_cast h)
lemma rod_q(c:ℝ)(h:|c|≤8):‖beam a (c*(2*pinch N))‖≤16*pinch N:=by
 have hp:=pinch_pos N; refine (beam_cost ..).trans ?_; rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*pinch N)]; nlinarith
variable {a s w}
lemma crest (k:Site N)(s:Offset N): (tall k-1)*pinch N ≤ ‖pm k+s.val‖∧ ‖pm k+s.val‖≤ (tall k+1)*pinch N:=by
 have he:‖pm k+s.val‖≤ ‖pm k‖+‖s.val‖:=norm_add_le ..; have hv:‖pm k‖≤‖pm k+s.val‖+‖s.val‖:=by simpa using (norm_sub_le (pm k+s.val) s.val)
 have hp:=pinch_pos N; unfold tall; have hg:‖s.val‖≤pinch N:=s.property; constructor
 · rw [sub_mul,div_mul_cancel₀ _ hp.ne',one_mul]; linarith
 rw [add_mul,div_mul_cancel₀ _ hp.ne',one_mul]; linarith
lemma clout (g:Even N.val)(k:Site N)(q:0<r)(H:1≤j)(b:ℝ)(h:|w| ≤1)(u:Bound (pinch N) (s.val+beam a (w*(2*pinch N)))) :
 ∀ i∈range 8, |‖pm k+s.val‖-‖pingH s a k i‖|≤16*pinch N:=fun i hi=> by
 have he:= neigh (orb k s g) (orb _ s g) (sprout a s.val k i)
 exact he.trans (rod_q a _ (by rw [abs_of_nonneg (by positivity : 0≤(i:ℝ))]; exact rod_u i (mem_range.mp hi)))
set_option maxHeartbeats 600000 in
lemma bluff (H:1≤j)(p:0<r)(a:Axis):∃ A V:ℝ,0<A∧0<V∧∀ N:Side,Even N.val → 18*pinch N < zone →∀ (M:Male) (k:Site N)(s:Offset N)(w:ℝ), A ≤ tall k→ |w|≤1→ Bound (pinch N) (s.val+beam a (w*(2*pinch N))) → ‖cot s a w k j 8 r M‖≤ V*(tall k ^8)⁻¹:=by
 obtain ⟨D,hD,W⟩:=high_frost H p; obtain ⟨u,C,hu,hc,L⟩:=plunge (out_b' j H RayH.M RayH.x (t:=crop) (fun _=>rfl) RayH.cap a) 8 (by decide)
 let A:= D+4/u+20; have hA:20+D<A:=by unfold A; have he:0<4/u:=(by positivity); linarith
 refine ⟨A,C*4^8,(by linarith),mul_pos hc (by positivity),fun N q g M k s w l b ht=>?_⟩
 let x:=pm k+s.val; have hp:=pinch_pos N; have hh:= crest k s; have he:tall k >20+D:=hA.trans_le l; have hk: (D+19)*pinch N< ‖x‖ :=lt_of_lt_of_le (by nlinarith : (D+19)*pinch N<(tall k-1)*pinch N) hh.1; have hx:0<‖x‖:=by nlinarith
 let i:RayH:=⟨M,x,orb _ _ q,hx⟩; let v:= 2*pinch N / ‖x‖; have hv:0<v:=by unfold v; positivity
 have hV:v * tall k ≤ 4:=by
   dsimp only [v]; rw [div_mul_eq_mul_div,div_le_iff₀ hx]; have hf:(_ : ℝ) ≤ ‖x‖:= hh.1; change (tall k-1)*pinch N ≤ ‖x‖ at hf; nlinarith
 have hg:‖(v:ℂ)‖=v:=by rw [Complex.norm_real,Real.norm_of_nonneg hv.le]
 have hm:= L i w b (v:ℂ) (hg.trans_lt (show v<u from ?_)); rotate_left
 · have hr:4/u<tall k:=(by dsimp only [A] at l; linarith); rw [div_lt_iff₀ hu] at hr; nlinarith
 simp only [zpow_zero,mul_one,hg] at hm; let P:=cold N j M r x
 have hf(c:ℝ)(y:Bin)(hc:|c|≤8)(e:Bound Real.pi y)(t:peers (x+beam a (c*(2*pinch N))) y):
    Complex.log (shell j i.M.val (tmap i.x+spark a (raf crop i ((c:ℂ)*(v:ℂ))))/shell j i.M.val (tmap i.x))=(cold N j M r y:ℂ)-(P:ℂ):=by
    let F:=beam a (c*(2*pinch N)); have he:= rod_q (N:=N) a c hc; have hh:= (neigh (y:=F) i.cap e t).trans he
    have hj:D*pinch N≤‖y‖:= by change |_ - _|≤_ at hh; obtain ⟨h,l⟩:= abs_le.mp hh; change ‖x‖-_≤_ at l; linarith
    let Q:RayH:=⟨M,y,e,by nlinarith⟩
    rw [snap,show ‖i.x‖*v=2*pinch N from (by change ‖x‖*_=_; unfold v; field_simp)]
    refine high_cost (t:=i) (s:=Q) rfl _ ?_ t p (W _ _ _ i.cap (by change D*_≤‖x‖; nlinarith)) (W _ _ _ e hj)
    refine ⟨tmap_physical _, fun j=>?_⟩; have ht:= (b_abs (x+F) j).trans (norm_add_le ..); have hv:‖x‖≤Real.pi:= i.cap; change ‖F‖≤_ at he
    change |((_ : ℝ):ℂ).re|<_; rw [Complex.ofReal_re]; change |(x+F) j|<_; linarith
 have hy:Bound Real.pi (tipC s a w k):=by unfold tipC; rw [add_assoc]; exact orb k ⟨_,ht⟩ q
 rw [hf w _ (b.trans (by norm_num)) hy (peers.roll _), sum_congr rfl (fun n hn=> show (bead 8 w n:ℂ) • _ = ((bead 8 w n*(cold N j M r (pingH s a k n)-P):ℝ):ℂ) from ?_)] at hm; swap -- tune
 · rw [show (n:ℂ)=((n:ℝ):ℂ) by simp, hf (n:ℝ) _ (by rw [abs_of_nonneg (by positivity : 0≤(n:ℝ))]; exact rod_u n (mem_range.mp hn)) (orb _ _ q) (sprout a s.val k n)]; simp [pingH]
 rw [←Complex.ofReal_sum] at hm; simp only [mul_sub,sum_sub_distrib, ←sum_mul, bead_one 8 (by norm_num), one_mul, Complex.ofReal_sub,sub_sub_sub_cancel_right] at hm; rw [←Complex.ofReal_sub, Complex.norm_real] at hm -- simp loop!
 apply hm.trans; rw [mul_assoc, ←div_eq_mul_inv]; gcongr; rw [le_div_iff₀ (by have he:=tall_p k; positivity : 0<tall k^8),←mul_pow]; gcongr
 exact mul_nonneg hv.le (zero_le_one.trans (tall_p k))
end YM.CF.Jill
