import YM.CF.BProof.Gauss.Spectral

/- Polynomial passport for sqrt inverse. Use expansion at the upper real PL bound p.
Adjust by a constant correction in the fare, same PL tail, so the **polynomial itself** is
identity on the severe slots. This particular polynomial works without separate overriding. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.Bin
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
variable (p a c:ℝ)(n:ℕ)(r:ℝ)

def fee (n:ℕ)(z:ℝ) := ∑ i∈Finset.range n,SignScalar.c i*z^i
abbrev pay := (Real.sqrt p)⁻¹
def afford (r:ℝ) := 1-p⁻¹*r
def tap := pay p*fee n (afford p r)
def fare := tap p n r+(1-tap p n 1)
@[simp] lemma fare_one : fare p n 1=1:=by unfold fare; ring
lemma fees (u:ℝ)(k:0<n)(h:0≤u) : 1 ≤ fee n u:=by
 apply le_trans _ (single_le_sum (f:=fun i=>SignScalar.c i*u^i) (fun i _=>mul_nonneg (c_nn i) (pow_nonneg h _)) (Finset.mem_range.mpr k)); simp [SignScalar.c]
lemma fee_limit (z:ℝ)(g:0≤z)(h:z≤r)(hv:r<1) : let t:=bin z-fee n z; 0≤t ∧ t ≤ r^n*(1-r)⁻¹:=by
 obtain hr:= g.trans h; have heu:=summable_geometric_of_lt_one hr hv
 have hx := ((bin_summable z (by rw [Real.norm_of_nonneg g]; exact h.trans_lt hv)).of_norm); intro t; unfold t fee bin; rw [← hx.sum_add_tsum_nat_add n,add_sub_cancel_left]
 let f(k:ℕ):= (SignScalar.c (k+n))*z^(k+n); have hp(k:ℕ): 0≤ f k:= mul_nonneg (c_nn _) (pow_nonneg g _); change 0≤ ∑' k,f k ∧ (∑' k,f k)≤_
 refine ⟨tsum_nonneg hp,?_⟩; have hh(k):f k≤ r^(k+n):=(mul_le_of_le_one_left (pow_nonneg g _) (c_le _)).trans (pow_le_pow_left₀ g h _); apply le_trans (b:=∑' k:ℕ,r^(k+n)) (Summable.tsum_mono ((summable_nat_add_iff n).2 hx) ((summable_nat_add_iff n).2 heu) hh); simp_rw [pow_add]; rw [tsum_mul_right,tsum_geometric_of_lt_one hr hv,mul_comm]
variable {p a r} (hp:1≤p)(ha:0<a)(h:a≤1)
include hp ha h
lemma pay_pos : 0 < pay p:=by unfold pay; have hv:=zero_lt_one.trans_le hp; positivity -- remove ha h
lemma aff_range (v:a≤r)(u:r≤p) : 0≤ afford p r ∧ afford p r ≤ afford p a ∧ afford p a <1:=by
 have he:=zero_lt_one.trans_le hp; unfold afford; rw [sub_nonneg, inv_mul_le_iff₀ he]; refine ⟨by simpa,sub_le_sub_left ?_ _,sub_lt_self _ ?_⟩; gcongr; positivity
abbrev tail (p a:ℝ) (n:ℕ):= (pay p) * ((afford p a)^n*(1-afford p a)⁻¹)
lemma scalar_fee (v:a≤ r)(u:r≤p): let t:=pay r-tap p n r; 0≤t ∧ t≤tail p a n:=by
 obtain ⟨hz,hv,hl⟩:= aff_range hp ha h v u; have hq:=zero_lt_one.trans_le hp; have hh:= ha.trans_le v
 have he : bin (afford p r)= Real.sqrt p * (Real.sqrt r)⁻¹:=by
    rw [← sq_eq_sq₀ (bin_nonneg _ hz) (by positivity),bin_sq _ hz (hv.trans_lt hl)]; unfold afford; rw [mul_pow,inv_pow, Real.sq_sqrt hq.le,Real.sq_sqrt hh.le]; field_simp; rw [sub_sub_cancel,div_self hh.ne'] -- tune
 intro t; have hk:t=pay p*(bin (afford p r)-fee n (afford p r)):=by unfold t tap; rw [mul_sub,he, show pay p*(Real.sqrt p*(Real.sqrt r)⁻¹)=pay r by unfold pay; field_simp]; -- tune
 rw [hk]; exact ⟨mul_nonneg (pay_pos hp ha h).le ((fee_limit n _ _ hz hv hl).1), mul_le_mul_of_nonneg_left ((fee_limit n _ _ hz hv hl).2) (pay_pos hp ha h).le⟩
def maximum (a:ℝ):= pay a+1
lemma max_ge : 1≤ maximum a:=by
 have ht:0≤pay a:=by unfold pay; positivity
 unfold maximum; linarith
lemma shift_size (v:a≤ r)(u:r≤p): |pay r-fare p n r|≤tail p a n:=by
 obtain ⟨p1,p2⟩:= scalar_fee n hp ha h v u; obtain ⟨p3,p4⟩:= scalar_fee (r:=1) n hp ha h h hp; change 0 ≤ _ at p1; change pay 1 - tap p n 1 ≤ _ at p4; have he:pay 1=1:=by simp [pay]
 unfold fare; rw [abs_le]; constructor <;> linarith
lemma fares_bound (k:0 < n)(d:tail p a n≤1)(v:a≤ r)(u:r≤p) : pay p≤ fare p n r ∧ fare p n r≤maximum a:=by
 have hh:=fees n (afford p r) k (aff_range hp ha h v u).1 -- tune
 obtain ⟨h3,h4⟩:=scalar_fee (r:=1) n hp ha h h hp; have he:pay 1=1:=by simp [pay]
 have hx:= pay_pos hp ha h; unfold fare; refine ⟨le_trans (b:=tap p n r) (le_mul_of_one_le_right hx.le hh) (le_add_of_nonneg_right (by linarith)),?_⟩
 have hz: pay r≤pay a:=inv_anti₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt v); unfold maximum; linarith [(scalar_fee n hp ha h v u).1] -- tune
lemma perfect (h':0<r): pay r*r*pay r=1:=by unfold pay; calc
    _ = r/((Real.sqrt r)^2) := by ring
    _ = 1 :=by rw [Real.sq_sqrt h'.le, div_self h'.ne']
abbrev scope (p a:ℝ)(n:ℕ):= p*(tail p a n*(2*maximum a))
lemma disburse (k:0<n)(d:tail p a n≤1)(v:a≤r)(u:r≤p): |1-fare p n r*r*fare p n r|≤ scope p a n:=by
 let z:=pay r; let b:= fare p n r; have ht:=fares_bound n hp ha h k d v u; have hZ:=pay_pos hp ha h; have hr:=ha.trans_le v; have hb:0≤b:=hZ.le.trans ht.1
 have he: |z+b|≤2*maximum a:=by
   have ho:0≤z:=by unfold z pay; positivity
   have hl:z≤pay a:= inv_anti₀ (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt v); rw [abs_of_nonneg (by positivity)]; unfold maximum; linarith only [show b≤pay a+1 from ht.2,hl]
 rw [show 1-fare p n r*r*fare p n r=r*((z-b)*(z+b)) from by rw [← show z*r*z=1 from perfect hp ha h hr]; unfold b; ring]; simp only [abs_mul,abs_of_nonneg hr.le]; exact mul_le_mul u (mul_le_mul (shift_size n hp ha h v u) he (abs_nonneg _) ((abs_nonneg _).trans (shift_size n hp ha h v u))) (by positivity) (le_trans hr.le u)
end YM.CF.BProof.Gauss.Bin
