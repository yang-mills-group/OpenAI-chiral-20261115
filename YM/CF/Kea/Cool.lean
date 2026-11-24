import YM.CF.Kea.Pith
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{N B m:Side}{r l:ℝ}{d:Candle}
def iceK (j:ℕ)(F:Slide N d)(M:Jill.Male)(r:ℝ):ℝ:=∏ i:Stag N,cup N j M r (angle F i)
lemma ice_p(j:ℕ)(F:Slide N d)(M:Jill.Male)(hp:0<r):0 < iceK j F M r:= prod_pos fun i _=>cup_p _ hp _
lemma phase_p(x:ℝ)(k:ℕ):pw (k*x)=pw x^k:=by unfold pw BZ.phase; push_cast; rw [mul_assoc,Complex.exp_nat_mul]
def Medal(N:Side)(d:Candle)(l:ℝ):Prop:=∀ i,∃ a,l≤‖BallG N d i a+1‖
lemma gild(p:0<l):∃ A:ℝ,0<A∧∀ N:Side,∀ d:Candle,∀ s:Slide N d, Medal N d l→∀ i,A*pinch N ≤ ‖angle s i‖:=by
 obtain ⟨u,b,h⟩:=Metric.continuousAt_iff.mp (phase_cont.continuousAt (x:=0)) _ p
 refine ⟨u/Real.pi,by positivity,fun N d s f i=>?_⟩; obtain ⟨a,ht⟩:=f i.2
 let x:=angle s i; by_contra! k; let v:ℝ:=N.val*x a; have hp:|v|<u:=by
   unfold v; rw [abs_mul,abs_of_nonneg (show 0≤(N.val:ℝ) by positivity)]; have he:=mul_lt_mul_of_pos_left ((b_abs x a).trans_lt k) (nPos N)
   exact he.trans_eq (by unfold pinch; field_simp)
 have hh:=h (show dist v 0<u from by rw [dist_zero_right,Real.norm_eq_abs]; exact hp)
 have hg:=catchV N d _ s i rfl a; change pw (x a)^N.val= _ at hg; rw [phase_z, dist_eq_norm, show v = _ from rfl,phase_p,hg, show (-1:ℂ)*BallG N d i.2 a-1= -(BallG N d i.2 a+1) by ring,norm_neg] at hh; linarith
lemma zipper (p:1≤j)(h:0<l): ∃ r:ℝ,0<r∧∀ N:Side,Even N.val →∀ d:Candle,∀ S:Slide N d,∀ M:Jill.Male,Medal N d l→∀ i,cup N j M r (angle S i)=disk j M (angle S i):=by
 obtain ⟨A,hA,W⟩:=gild h; obtain ⟨c,C,hc,ht,H⟩:= zip p; refine ⟨c*A^2,by positivity,fun N t d s M g i=>?_⟩
 unfold Jill.cup; rw [max_eq_right]; apply le_trans _ (H M _ (up_p s t i)).1; rw [mul_assoc,←mul_pow]; have hp:=pinch_pos N; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (W N d s g i) 2) hc.le
-- equality for emptyS for any r: from point-shift weight zero via peers of taps within [-π,π], cup by peers. use zero Slide
lemma visor :∀ i:Slot, rise emptyC i=0:=by rintro ⟨l,i|i⟩ <;> funext a <;> simp [emptyC,rise,pulse,freqD,skyV]; -- tune

def too(N:Side):Slide N emptyC where
 u _:=zeroF N
 z _:=0
 f i:=by rw [visor]; unfold zeroF; funext a; simp
lemma too_u(N:Side)(i:Stag N):angle (too N) i=pm i.1:=by simp [angle,too,zeroF]
lemma empty_m(t:l≤2)(N:Side):Medal N emptyC l:=by
 intro i; refine ⟨0,?_⟩; unfold BallG; rw [visor,Pi.zero_apply,phase_z,one_pow, ←two_mul (1:ℂ),mul_one]; simpa using t
lemma ice_z (p:0<r)(F:Slide N d)(M:Jill.Male): Real.log (iceK j F M r)=∑ l:Slot,(slurry N j r M (F.u l)+∑ _k:Site N,Real.log (r*pinch N^2)):=by
 unfold iceK slurry cold; rw [Real.log_prod (fun i _=> (cup_p _ p _).ne'),Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro i _; rw [sum_sub_distrib,sub_add_cancel]; exact Equiv.sum_comp (Equiv.addRight (wrap N (F.z i))) (fun k:Site N=> Real.log (cup N j M r (pm k+(F.u i).val)))
lemma log_b(H:1≤j)(p:0<r): ∃ C:ℝ,0<C∧∀ N:Side,Even N.val →18*pinch N<zone→∀ (d:Candle)(F:Slide N d)(M:Jill.Male),‖Real.log (iceK j F M r) - Real.log (iceK j (too N) M r)‖≤ C:=by
 obtain ⟨u,t,U⟩:= punch H p; refine ⟨45*u,mul_pos (by norm_num) t,fun i g h d F M=>?_⟩; rw [ice_z p,ice_z p,←sum_sub_distrib]; simp_rw [add_sub_add_right_eq_sub]; apply (norm_sum_le ..).trans
 exact (sum_le_sum fun i _=>U _ g h M (F.u i)).trans (le_of_eq (by rw [sum_const,card_univ,slots]; simp))
lemma pole (H:1 ≤ j)(p:0<r): ∃ c C:ℝ,0<c∧0<C∧∀ N:Side, Even N.val→18*pinch N < zone→∀ (d:Candle)(F:Slide N d)(M:Jill.Male), c*iceK j (too N) M r ≤ iceK j F M r ∧ iceK j F M r ≤ C*iceK j (too N) M r:=by
 obtain ⟨K,v,V⟩:= log_b H p; refine ⟨Real.exp (-K),Real.exp K, Real.exp_pos _,Real.exp_pos _,fun N h u d F M=>?_⟩
 let B:=iceK j (too N) M r; let A:=iceK j F M r; have t:= ice_p j (too N) M p; have u':=ice_p j F M p
 have ht:= V N h u d F M; change |Real.log A-Real.log B|≤K at ht; rw [abs_le] at ht
 have hp:Real.exp (Real.log A)=A:=Real.exp_log u'; have he:Real.exp (Real.log B)=B:=Real.exp_log t
 change _*B ≤ A∧A≤ _*B; nth_rw 1 [← he,←hp]; constructor
 · rw [←Real.exp_add]; exact Real.exp_monotone (by linarith)
 apply le_trans (le_of_eq hp.symm); apply (Real.exp_monotone (by linarith : Real.log A ≤ K+ Real.log B)).trans; rw [Real.exp_add,he]
end YM.CF.Kea
