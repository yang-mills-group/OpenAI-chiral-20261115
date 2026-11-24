import YM.CF.BPress.Weave.Harbor
import YM.CF.Operator.SignScalar
import YM.CF.BPress.Scale
/-! B-poly binomial approximation scalar with PL buy. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Weave
open Function Filter Finset SignScalar Pressure
open scoped Topology BigOperators Classical InnerProductSpace
-- A scalar upper spectral bound p≥1; r lower
variable (p r z y:ℝ)(n:ℕ)
def haloFee (u:ℝ):=1-p⁻¹*u
def limitFee:= haloFee p r
def short (z:ℝ)(n:ℕ) := ∑ i∈range (n+1), c i * z^i
def shortA (u:ℝ):=(Real.sqrt p)⁻¹* short (haloFee p u) n
def peak (r:ℝ) := (Real.sqrt r)⁻¹
def brink (p r:ℝ)(n:ℕ):=peak p* Real.exp (-(r/p)*(n+1))*(p/r)
lemma geo_fee (x l:ℝ)(g:0≤x)(p:x≤ 1-l)(n:ℕ): x^n≤ Real.exp (-l*n):=by rw [mul_comm _ (n:ℝ), Real.exp_nat_mul]; apply pow_le_pow_left₀ g; exact p.trans ((le_of_eq (by ring)).trans (Real.add_one_le_exp (-l)))
lemma tick_valid (e:0<r)(h:z∈ Set.Icc r p): haloFee p z ∈ Set.Ico 0 1∧ haloFee p z ≤ 1-r/p:=by
 obtain ⟨a,b⟩:=h; have hp:= e.trans_le (a.trans b); have ht:=e.trans_le a; unfold haloFee; rw [mul_comm p⁻¹ z,← div_eq_mul_inv] -- tune
 exact ⟨⟨sub_nonneg.mpr ((div_le_one hp).mpr b), sub_lt_self _ (div_pos ht hp)⟩,sub_le_sub_left (div_le_div_of_nonneg_right a hp.le) _⟩
lemma short_err (e:0≤z)(h:z<1): 1≤short z n ∧ 0 ≤ bin z-short z n ∧ bin z-short z n ≤ z^(n+1)*(1-z)⁻¹:=by
 have hz(i:ℕ): 0 ≤ c i*z^i:= mul_nonneg (c_nn _) (pow_nonneg e _)
 have hs:= Summable.of_norm (bin_summable z (by rwa [Real.norm_of_nonneg e])); have hv:= (summable_nat_add_iff (n+1)).mpr hs; unfold short
 refine ⟨?_,(sub_nonneg.mpr (hs.sum_le_tsum _ (fun i _=> hz _))),?_⟩
 · exact le_trans (Eq.le (by rw [pow_zero,mul_one,c])) (single_le_sum (f:=fun i=>c i*z^i) (fun i _=> hz _) (mem_range.mpr (show 0<n+1 by omega))) -- tune
 unfold bin; rw [← hs.sum_add_tsum_nat_add (n+1), add_sub_cancel_left]; have he:= summable_geometric_of_lt_one e h; apply le_trans (hv.tsum_le_tsum (g:=fun i=> z^(i+(n+1))) (fun i=> mul_le_of_le_one_left (pow_nonneg e _) (c_le _)) ((summable_nat_add_iff (n+1)).mpr he)); simp_rw [pow_add z _ (n+1),tsum_mul_right,tsum_geometric_of_lt_one e h]; rw [mul_comm]
lemma peak_price (e:0<r)(h:z∈ Set.Icc r p) : shortA p n z∈ Set.Icc (peak p) (peak r) ∧ 1-shortA p n z ^2*z ∈ Set.Icc 0 (p* (2*peak r) * brink p r n):=by
 obtain ⟨⟨a,b⟩,c⟩:=tick_valid p r z e h; let V:=haloFee p z; let S:=peak p; let L:=short V n; let J:=peak p * bin V; have A : S*L=shortA p n z:=rfl; let W:=peak r
 have hrz:=h.1; have hzp:=h.2; have hz:=e.trans_le hrz; have hp:=hz.trans_le hzp; have hc:=Real.sqrt_pos.mpr hp; have hd:=Real.sqrt_pos.mpr e; have hS:0<S:= inv_pos.mpr hc; have hW:0<W:=inv_pos.mpr hd; have h₁:S^2=p⁻¹:=by unfold S peak; rw [inv_pow,Real.sq_sqrt hp.le]
 have h₂:W^2=r⁻¹:=by unfold W peak; rw [inv_pow, Real.sq_sqrt e.le]
 have h₃:J^2=z⁻¹:=by unfold J V; rw [mul_pow,show peak p^2=p⁻¹ from h₁, bin_sq (haloFee p z) a b]; unfold haloFee; rw [sub_sub_cancel]; field_simp -- tune
 have hJ:0≤J:= mul_nonneg hS.le (bin_nonneg _ a); obtain ⟨h₄,h₅,h₆⟩:= short_err V n a b; have hL:0 ≤ L:= zero_le_one.trans h₄; rw [← A]; have H:S*L ≤ J:= mul_le_mul_of_nonneg_left (sub_nonneg.mp h₅) hS.le; have Hw:J ≤ W:= (sq_le_sq₀ hJ hW.le).mp (by rw [h₃,h₂]; exact inv_anti₀ e hrz); have Hd : J-S*L ≤ brink p r n := by
   change S*bin V-_ ≤ _; rw [← mul_sub]; apply le_trans (mul_le_mul_of_nonneg_left h₆ hS.le); unfold brink; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hS.le; apply mul_le_mul (by simpa using geo_fee V (r/p) a c (n+1)) ?_ (by have he: 0<1-V:=sub_pos.mpr b; positivity) (Real.exp_pos _).le
   calc (1-V)⁻¹ ≤ (r/p)⁻¹ :=inv_anti₀ (div_pos e hp) (by linarith only [show V≤1-r/p from c])
        _ = _ := by field_simp -- tune
 have he:J^2 * z=1:=by rw [h₃,inv_mul_cancel₀ hz.ne']
 have hl:0≤S*L:= by positivity
 refine ⟨⟨le_mul_of_one_le_right hS.le h₄,H.trans Hw⟩,?_⟩; rw [← he]; rw [show J^2*z-(S*L)^2*z=z*(J+S*L)*(J-S*L) by ring]; exact ⟨by have he:=sub_nonneg.mpr H; positivity,mul_le_mul (mul_le_mul hzp (by change J+S*L≤2*W; linarith) (by positivity) hp.le) Hd (sub_nonneg.mpr H) (by change 0≤ p*(2*W); positivity)⟩

-- Eventually PL powers at polynomial byte budget from degrees. 
lemma npl_inv : NPL (fun y:ℝ => y⁻¹):= (npl_g.mul npl_g.pl).mono (by filter_upwards [eventually_gt_atTop (0:ℝ)] with i pi; rw [← gscale pi.le,pow_two])
lemma peak_pl (p:ℝ→ℝ)(e:∀ᶠ i in atTop, 1 ≤ p i): PL (fun y=>peak (p y)) := (PL.const 1).mono <| e.mono fun i e=> by
 have hp:=zero_lt_one.trans_le e; have ht:= Real.sqrt_pos.mpr hp; rw [peak,abs_of_pos (by positivity : 0<(Real.sqrt (p i))⁻¹), abs_one]; exact inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt e) -- tune
lemma ip_PL (p:ℝ→ℝ)(h:PL p)(e:∀ᶠ i in atTop,1≤ p i): PL (fun i=> (peak (p i))⁻¹):=h.mono <| e.mono fun i ht=> by
 have hp:=zero_lt_one.trans_le ht; rw [peak, inv_inv, abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hp]; nlinarith only [hp,ht,Real.sq_sqrt hp.le] -- tune
lemma fullseat (p:ℝ→ℝ)(r:ℝ)(h:PL p)(e:∀ᶠ i in atTop,1≤p i)(t:0<r): ∃ (n:ℝ→ℕ), PL (fun y=>(n y:ℝ)) ∧ ∀ᶠ y in atTop,(p y * (2*peak r)*brink (p y) r (n y))≤ y⁻¹^2:=by
 -- enough to take 3 logs p/r
 let L (i:ℝ):= Real.log i*3*(p i*r⁻¹); let n(i:ℝ):=⌈L i⌉₊; let P (y:ℝ) := p y*(2*peak r)*peak (p y)*(p y*r⁻¹)
 have hz := (((h.mul (PL.const (2*peak r))).mul (peak_pl p e)).mul (h.mul (PL.const r⁻¹))).times npl_inv; have he:= hz.drop; refine ⟨n,(PL.log.mul (PL.const 3) |>.mul (h.mul (PL.const r⁻¹))).ceil (F:=L) ?_, ?_⟩ -- tune
 · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,e] with i hi e; unfold L; positivity
 filter_upwards [e,he.eventually (ge_mem_nhds zero_lt_one),eventually_gt_atTop (0:ℝ)] with i v u p'; have hp:=zero_lt_one.trans_le v; have hs:=mul_nonneg hp.le (show 0≤2*peak r by unfold peak; positivity); have hu:P i*i⁻¹≤1:= u; let l:=Real.exp (-(r/p i)*(n i+1)); have hk:l≤ i⁻¹^3:=by
   have hg : -(r/p i)*((n i:ℝ)+1)≤ -Real.log i * 3:=by
     rw [neg_mul, neg_mul (Real.log i),neg_le_neg_iff]; have h': L i ≤ (n i:ℝ)+1:= (Nat.le_ceil _).trans (by linarith); apply le_trans _ (mul_le_mul_of_nonneg_left h' (by positivity : 0≤ r/p i)); unfold L; field_simp; nlinarith -- tune
   apply (Real.exp_monotone hg).trans; rw [mul_comm (-Real.log i),show Real.exp (3*(-Real.log i))=Real.exp (-Real.log i)^3 from Real.exp_nat_mul (-Real.log i) 3,Real.exp_neg,Real.exp_log p'] -- tune
 have hP:0 ≤ P i:= by unfold P peak; positivity
 suffices p i*(2*peak r)*brink (p i) r (n i)=P i*l by rw [this]; apply le_trans (mul_le_mul_of_nonneg_left hk hP); simpa only [mul_assoc, ← pow_succ',one_mul] using mul_le_mul_of_nonneg_right hu (sq_nonneg i⁻¹)
 unfold P l brink; ring
end YM.CF.BPress.Weave
