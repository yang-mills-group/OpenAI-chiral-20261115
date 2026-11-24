import YM.CF.Jill.Crest
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jill
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
variable {N:Side}{j:ℕ}{r:ℝ}{M:Male}
lemma low_t (H:1≤j)(p:0<r)(A:ℝ)(ha:0<A):∃ C:ℝ,0<C∧∀ N:Side,Even N.val→∀ (M:Male) (k:Site N)(s:Offset N)(w:ℝ)(a:Axis), tall k≤ A → |w|≤1→ Bound (pinch N) (s.val+beam a (w*(2*pinch N))) → ‖cot s a w k j 8 r M‖≤ C*(tall k ^8)⁻¹:=by
 obtain ⟨T,u,U⟩:=local_frost H p (A+17) (by linarith); obtain ⟨b,v,V⟩:=bead_bound 8
 refine ⟨(T+b*T)*A^8,by positivity,fun N g M k s w a h he e=>?_⟩
 let F:= pm k+s.val; have hx:‖F‖≤ (A+1)*pinch N:= (crest k s).2.trans (mul_le_mul_of_nonneg_right (add_le_add_left h _) (pinch_pos _).le) -- tune add right
 have hu:tipC s a w k=pm k+(s.val+beam a (w*(2*pinch N))):= add_assoc ..
 have ht:‖tipC s a w k‖≤ (A+17)*pinch N:= (norm_add_le F _).trans ((add_le_add hx (rod_q a w (he.trans (by norm_num)))).trans_eq (by ring))
 let X(n:ℕ):= pingH s a k n
 have hv : ∀ i∈range 8,‖cold N j M r (X i)‖ ≤ T:=fun i hi=> by
   have hm:= abs_le.mp (clout g k p H 0 he e i hi); apply U N M _ (orb _ s g); change ‖X i‖ ≤ _; obtain ⟨t,v⟩:=hm; change -_≤‖F‖-‖X i‖ at t; linarith
 have hp:‖cot s a w k j 8 r M‖ ≤ T+b*T:=by
   unfold cot; refine (norm_sub_le ..).trans (add_le_add (U N M (tipC s a w k) (hu.symm ▸ orb _ ⟨_,e⟩ g) ht) ((norm_sum_le ..).trans ?_))
   refine (sum_le_sum (g:=fun i=> |bead 8 w i| * T) fun i hi=>?_).trans (by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (V _ he) u.le)
   rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hv i hi) (norm_nonneg _)
 refine hp.trans ?_; rw [←div_eq_mul_inv,le_div_iff₀ (show 0<tall k^8 by have hh:= tall_p k; positivity)]; gcongr; exact zero_le_one.trans (tall_p _)

variable (N j M r)
def slurry(x:Offset N):=∑ k:Site N,cold N j M r (pm k+x.val)
variable {N j M r}
lemma swim (H:1≤j)(p:0<r)(a:Axis):∃ V:ℝ,0<V∧∀ N:Side,Even N.val → 18*pinch N < zone →∀ (M:Male) (s y:Offset N)(w:ℝ), |w|≤1→ y.val=s.val+beam a (w*(2*pinch N)) → ‖slurry N j r M y-slurry N j r M s‖≤V:=by
 obtain ⟨A,b,h,hb,F⟩:=bluff H p a; obtain ⟨C,hC,G⟩:= low_t H p A h; obtain ⟨D,hv,K⟩:=cost_c
 refine ⟨max b C*D,mul_pos (lt_max_of_lt_left hb) hv,fun N g hx M s y w t r'=>?_⟩
 let S:= tipC s a w; let R:= cold N j M r; have hk(k:Site N): pm k+y.val=S k:=by rw [r']; exact (add_assoc ..).symm
 have he(i:ℕ): ∑ k:Site N, R (pingH s a k i)=∑ k:Site N,R (pm k+s.val):=by exact Equiv.sum_comp (Equiv.addRight _) (fun k:Site N => R (pm k+s.val))
 let Q k:= cot s a w k j 8 r M; have hp: ∑ k:Site N, Q k=slurry N j r M y-slurry N j r M s:=by
   unfold Q cot slurry; rw [sum_sub_distrib, sum_comm]
   simp_rw [hk,← mul_sum]
   congr 1 -- inspect
   change ∑ i∈ range 8, bead 8 w i * (∑ k:Site N,R (pingH s a k i))= _; simp_rw [he]; rw [←sum_mul,bead_one 8 (by norm_num) w,one_mul]
 have ht:Bound (pinch N) (s.val+beam a (w*(2*pinch N))):= r' ▸ y.property
 rw [← hp]; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun k:Site N=>max b C*(tall k^8)⁻¹) fun k _=>?_).trans (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (K _) (hb.le.trans (le_max_left ..))) -- apply works?
 have hz :0≤(tall k^8)⁻¹:=by have he:= tall_p k; positivity
 rcases le_total A (tall k) with l|l
 · exact (F N g hx M k s w l t ht).trans (mul_le_mul_of_nonneg_right (le_max_left ..) hz)
 exact (G N g M k s w a l t ht).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hz)

def fill (x:Offset N)(S:Finset Axis):Offset N := ⟨fun i=> if i∈ S then x.val i else 0, (pi_norm_le_iff_of_nonneg (pinch_pos _).le).mpr fun i=> by split_ifs; exact (norm_le_pi_norm _ i).trans x.property; simp [(pinch_pos _).le]⟩
def zeroF(N:Side):Offset N:=⟨0,by unfold Bound; simpa using (pinch_pos _).le⟩
lemma punch(H:1≤j)(p:0<r): ∃ V:ℝ,0<V∧∀ N:Side,Even N.val → 18*pinch N < zone →∀ (M:Male)(s:Offset N),‖slurry N j r M s-slurry N j r M (zeroF N)‖ ≤ V:=by
 choose V hv K using (fun a=>swim H p a); refine ⟨1+∑ i,V i,(by linarith [sum_nonneg (fun i (_:i∈univ)=>(hv i).le)]),fun N g hx M s=>?_⟩
 let Y(S:Finset Axis):=slurry N j r M (fill s S)
 have he(S:Finset Axis):‖Y S-Y ∅‖≤∑ i∈S,V i:=by
   induction S using Finset.induction_on with
   | empty=> simp
   | @insert a S ha H=>
     have hp:=pinch_pos N
     let w:ℝ:= s.val a /(2*pinch N); have hw:w*(2*pinch N)=s.val a:=by unfold w; field_simp
     have ht:|w|≤1:=by
       have he:|w| *(2*pinch N)=|s.val a|:=by rw [← hw,abs_mul,abs_of_nonneg (by positivity : 0≤2*pinch N)]
       have hx:= (b_abs s.val a).trans s.property; nlinarith
     have hR: (fill s (insert a S)).val=(fill s S).val+beam a (w*(2*pinch N)):=(by rw [hw]; funext i; by_cases h:i=a<;> simp [h,ha,fill,beam,step])
     rw [sum_insert ha]; exact (norm_sub_le_norm_sub_add_norm_sub _ (Y S) _).trans (add_le_add (K a N g hx M _ _ w ht hR) H) -- tune
 have hx1:fill s univ=s:=by apply Subtype.ext; funext i; simp [fill]
 have hx2:fill s ∅=zeroF N:=by apply Subtype.ext; funext i; simp [fill,zeroF]
 rw [←hx2,←hx1]; convert! (he univ).trans (by linarith : _ ≤ 1+∑ i,V i) using 1
end YM.CF.Jill
