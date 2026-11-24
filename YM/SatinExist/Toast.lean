import YM.SatinExist.Iambic
import YM.SatinExist.Lede
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2400
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
open SatinTails
variable {H:Hilbert}{j:Axis}(S: OS.Semigroup H j) {r:ℕ}
local notation "U"=> S.E
local notation "K"=> Cache S
local notation "R"=> saucer S
variable (A:H.Op)(e:ℕ→ℝ≥0) (p:Tendsto e atTop (𝓝 0))(h:∀ i,0<e i)
local notation "D" i:max=> duration (e i)
include p h
private lemma swingD : Tendsto (fun i=> duration (e i)) atTop (𝓝[≠] (0:ℂ)):=by
 apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
 · simpa using! (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.comp p
 apply Eventually.of_forall; intro i q; exact lt_irrefl (0:ℝ) ((show duration (e i)=0 from q) ▸ (dur.mpr (h i)): (0:ℂ)∈inside)
-- sign cost of moved label. even if d(s)=0. not sensing zero
lemma at_plus {t:ℝ≥0}(g:0<t): Tendsto (fun i=> (D i)⁻¹ • (U (t+e i)- U t)) atTop (𝓝 (slug S (duration t))):=by
 let q:=swingD e p h; let z:=duration t; have hz:z∈inside:= dur.mpr g
 have hD:= (S.localHeat z hz).differentiableAt.hasDerivAt.tendsto_slope_zero.comp q
 refine hD.congr fun i=>?_; change (D i)⁻¹ • (S.F (z+D i)-S.F z)=_; rw [show z+D i= duration (t+e i) from (by unfold z duration; push_cast; rfl), S.roots_heat (add_pos g (h i)), show S.F z=U t from S.roots_heat g]
lemma at_minus {t:ℝ≥0}(g:0<t): Tendsto (fun i=> (D i)⁻¹ • (U t- U (t-e i))) atTop (𝓝 (slug S (duration t))):=by
 have q:Tendsto (fun i=> -duration (e i)) atTop (𝓝[≠] (0:ℂ)):=by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa only [neg_zero] using ((swingD e p h).mono_right nhdsWithin_le_nhds).neg
    apply Eventually.of_forall; intro i q; exact lt_irrefl (0:ℝ) ((neg_eq_zero.mp (show -duration (e i)=0 from q)) ▸ (dur.mpr (h i)): (0:ℂ)∈inside)
 let z:=duration t; have hz:z∈inside:= dur.mpr g
 have hD:= (S.localHeat z hz).differentiableAt.hasDerivAt.tendsto_slope_zero.comp q
 refine hD.congr' ?_; filter_upwards [p.eventually (gt_mem_nhds g)] with i v; change (-D i)⁻¹ • (S.F (z+-D i)-S.F z)=_; rw [show z+-D i= duration (t-e i) from (by unfold z duration; rw [NNReal.coe_sub v.le, ofReal_sub]; abel), S.roots_heat (tsub_pos_of_lt v), show S.F z=U t from S.roots_heat g]; rw [inv_neg, neg_smul, ←smul_neg, neg_sub]
-- derivative accumulator. formula R. independence of t
abbrev oneJet(A:H.Op):= R * A - A* R
abbrev plated {r:ℕ}(A:H.Op)(v:ℝ): H.Op:= Par S r v.toNNReal * A * Par S r v.toNNReal -- r not bound
#check slug
omit h p
lemma slug_price {t:ℝ≥0}(u:0<t): slug S (duration t)= U t - Par S 1 t:=by
 let z:=duration t; have he:z∈inside:=dur.mpr u
 suffices g:looper S z= Par S 1 t by rw [← g]; unfold looper; rw [show S.F z=U t from S.roots_heat u]; exact Eq.symm (sub_sub_cancel _ _)
 ext1 x; apply cache_I S 1; refine DFunLike.congr_fun (?_ : K 1 * looper S z = K 1 * Par S 1 t) x; refine (Eq.trans ?_ (recover S 1 z he).symm : K 1*looper S z= _); unfold Cache; rw [pow_one]; exact dorsal S z he
lemma PP'_S (n m:ℕ){x y:ℝ≥0}(hx:0<x)(hy:0<y):Par S n x*Par S m y=Par S (n+m) (x+y):=by
 have h:= part_par S n m _ _ (show 0<(x:ℝ) from hx) (show 0<(y:ℝ) from hy); simp_rw [←NNReal.coe_add,Real.toNNReal_coe] at h; exact h
lemma PtK {t:ℝ≥0}(p:0<t): R*Par S (r+1) t=Par S r t:=by
 let z:=Par S (r+1) t
 ext1 x; apply cache_I S r; refine DFunLike.congr_fun (?_ : K r * (R * Par S (r+1) t)= K r * Par S r t) x
 change K r *(R*z)=_; rw [← mul_assoc,show K r*R= K (r+1) from by unfold Cache; rw [pow_succ], show K (r+1)*z= _ from P_Heq S t _ p]; exact (P_Heq S t r p).symm
lemma PKt {t:ℝ≥0}(p:0<t): Par S (r+1) t * R=Par S r t:=by
 exact (gear S (duration t) (dur.mpr p) (r+1)).eq.symm.trans (PtK S p)
lemma jet_paid {t:ℝ≥0}(g:0<t)(r:ℕ):
    slug S (duration t)* (Par S r t * A * Par S r t) * U t - (U t)* (Par S r t * A * Par S r t) * slug S (duration t)= plated S (r:=r+1) (oneJet S A) ((t+t:ℝ≥0):ℝ):=by
 let L:= Par S 1 t; let Y:=Par S r t; let T:=Par S (r+1) (t+t); let X:= U t
 have hb(z:ℕ): Par S z (t+t+0)=Par S z (t+t):=by rw [add_zero]
 have hp:L*Y=T:=by unfold L Y T; rw [PP'_S S _ _ g g]; rw [Nat.add_comm]
 have hz:Y*L=T:=PP'_S S _ _ g g
 have he:Y*X= T * R:=by unfold X; rw [show U t= Par S 0 t from (S.roots_heat g).symm]; refine (PP'_S S r 0 g g).trans ?_; exact (PKt S (add_pos g g)).symm
 -- want Y*X = R*T, X*Y=T*R. equality
 have hy:X*Y=T*R:=by unfold X; rw [show U t= Par S 0 t from (S.roots_heat g).symm]; refine (PP'_S S 0 r g g).trans ?_; rw [Nat.zero_add]; exact (PKt S (add_pos g g)).symm
 have he':Y*X= R*T:=he.trans (gear S (duration (t+t)) (dur.mpr (add_pos g g)) (r+1)).eq.symm
 unfold plated; rw [Real.toNNReal_coe]; unfold oneJet; rw [slug_price S g]; change (X-L)*(Y*A*Y)*X-X*(Y*A*Y)*(X-L)= _
 calc
    _=(X*Y)*A*(Y*L)-(L*Y)*A*(Y*X):= by rw [sub_mul, sub_mul,mul_sub]; simp only [mul_assoc]; abel
    _= _:=by rw [hy,hz,hp,he']; change T*R*A*T-T*A*(R*T)=T*(R*A-A*R)*T; rw [mul_sub,sub_mul]; simp only [mul_assoc]
abbrev jerk {r:ℕ}(e:ℝ≥0) (G:H.Op) (d:ℝ≥0):H.Op:=(duration e)⁻¹ • (S.E (d+e)* G * S.E (d-e) - S.E d * G * S.E d)
variable {A':ℕ→H.Op}
-- sum transport.export
lemma spline_sum {H₁:Hilbert}{A B:ℕ→H₁.Op}{a b:H₁.Op}(p:Brakes A a)(q:Brakes B b): Brakes (fun i=> A i + B i) (a+b):=by
 obtain ⟨r,h⟩:=p.costs; obtain ⟨s,t⟩:=q.costs
 refine ⟨⟨r+s,(h.and t).mono fun i u=> (norm_add_le ..).trans (add_le_add u.1 u.2)⟩,fun y=> (p.brakes y).add (q.brakes y),fun y=>?_⟩
 simp_rw [star_add]; exact (p.heels y).add (q.heels y)
lemma spline_sub {H₁:Hilbert}{A B:ℕ→H₁.Op}{a b:H₁.Op}(p:Brakes A a)(q:Brakes B b): Brakes (fun i=> A i - B i) (a-b):=by
 simpa only [neg_one_smul,sub_eq_add_neg] using spline_sum p (q.pump (-1))
include p h
lemma braid (d:ℝ≥0)(u:0<d)(r:ℕ) (hZ:Brakes A' (plated S (r:=r) A (d:ℝ))) : Brakes (fun i=> jerk S (r:=r) (e i) (A' i) d) (plated S (r:=r+1) (oneJet S A) ((d+d:ℝ≥0):ℝ)):=by
 let X:= U d; let L(i:ℕ):=U (d+e i); let R'(i:ℕ):=U (d-e i);
 let Δ(i:ℕ):= (D i)⁻¹; have h1:= Brakes.by_budget (at_plus S e p h u); have h₂:= Brakes.by_budget (at_minus S e p h u); let A₀:=plated S (r:=r) A (d:ℝ)
 have h': Tendsto (fun i=>d-e i) atTop (𝓝 d):=by simpa [tsub_zero] using ((tendsto_const_nhds (x:=d)).sub p)
 have hv:= Brakes.heatT S h'; have hh: Brakes (fun _:ℕ=> X) X:= Brakes.by_budget tendsto_const_nhds
 apply (spline_sub ((h1.weave hZ).weave hv) ((hh.weave hZ).weave h₂)).sameC
 · apply Eventually.of_forall; intro i; let A:=A' i; change Δ i • (L i-X) * A * R' i - X * A * (Δ i • (X-R' i))= _; unfold jerk;
   rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]; unfold Δ; rw [←smul_sub]; apply congrArg (_ • ·); unfold L R' X A; rw [sub_mul,sub_mul,mul_sub]; abel
 unfold plated at *; simp_rw [Real.toNNReal_coe] at *; exact (by simpa only [plated,Real.toNNReal_coe] using jet_paid S A u r)
end YM.SatinJets
