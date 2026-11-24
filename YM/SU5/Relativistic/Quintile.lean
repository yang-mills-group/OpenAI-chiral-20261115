import YM.SU5.FiniteGaugeData.Tower.Accord
/-! # Uniform double-cluster
No angular continuity premise. Need both orthogonal axis registration and
positive-energy semiGroup each chart on same test pricing locally. Here
K may be particular to each elected character. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.Signs
open Filter Function MeasureTheory Metric Set InnerProductSpace
open scoped Topology NNReal InnerProductSpace Classical
open CF.Buffered.Afterglow.Tower.Vacancy

-- quadrant costs can vary H' and entries/axes independently by signs.
-- If time displacements eventually permit, and K can submit all transverse moves
-- with same entry weights, this criterion all-angles-near-zero ax-frame intersection purchases
-- a uniform large-quadrant limit. Does not say decay at Euclidean infinity in strips.
-- H-space no nontriviality demand, v normalization/corner fixed shifts can absorb. `E` readers via permits externally.
variable {K:ℤ→ℤ→ℂ}
variable {H H':Hilbert}
private lemma matrix_est(A B C:H): ‖inner ℂ A C-inner ℂ B C‖≤ ‖A-B‖*‖C‖:=by rw [←inner_sub_left]; apply norm_inner_le_norm

/-- uniform in all of the second coordinate. -/
def Stock (L:ℤ→ℤ→ℂ) (P:Rolls H) (ξ η:H) := ∀ ε> (0:ℝ), ∀ᶠ t:ℕ in atTop,∀ r:ℤ, dist (L t r) (inner ℂ ξ (P.wind r η))< ε
lemma full_stock {a:Axis}(S:OS.Semigroup H a) (ξ η:H)(p:ℕ→ℝ≥0)(t:Tendsto p atTop atTop) (P:Rolls H)(z:∀ᶠ n:ℕ in atTop, ∀ x:ℤ, K n x=inner ℂ ξ (S.E (p n) (P.wind x η))) : Stock K P (S.orth ξ) η:=by
 intro ε e; filter_upwards [z, Metric.tendsto_nhds.mp ((S.emerges ξ).comp t) (ε/(1+‖η‖)) (by positivity)] with n i q x
 change dist (S.E (p n) ξ) (S.orth ξ) < _ at q
 rw [dist_eq_norm, i,← S.swing]; refine lt_of_le_of_lt (matrix_est _ _ _) ?_; rw [P.solid,←dist_eq_norm]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by exact (le_add_of_nonneg_left zero_le_one)) dist_nonneg); exact (lt_div_iff₀ (by positivity : 0 < 1+‖η‖)).mp q
-- proof supplies slope converge along x positive to some y, then average to determine using TRUE projected limit. Plans for uniform over other offsets by preobserved rows
variable (P:Rolls H)(U:Rolls H')(ξ η:H)(A B:H')
lemma two_purse {f g:ℕ→ℂ} {K:ℕ→ℕ→ℂ}(l:∀ε>(0:ℝ),∀ᶠ n:ℕ in atTop,∀m,dist (K n m) (f m)<ε)(k:∀ε>(0:ℝ),∀ᶠ m:ℕ in atTop,∀n,dist (K n m) (g n)<ε): ∃ z:ℂ, Tendsto (fun x:ℕ×ℕ=>K x.1 x.2) atTop (𝓝 z) ∧ Tendsto f atTop (𝓝 z) ∧ Tendsto g atTop (𝓝 z):=by
 have hp:CauchySeq f:= by
    apply Metric.cauchySeq_iff'.2; intro ε e
    obtain ⟨d,v⟩:= (l (ε/5) (by positivity)).exists
    obtain ⟨N,H⟩:=eventually_atTop.mp (k (ε/5) (by positivity)); refine ⟨N,fun j t=>?_⟩
    have he(b)(p:N ≤ b): dist (f b) (g d)<2*ε/5:=by have ht:= dist_triangle (f b) (K d b) (g d); rw [dist_comm (f b) (K d b)] at ht; linarith only [v b,H b p d,ht,e]
    have hh:= dist_triangle_right (f j) (f N) (g d); linarith [he N le_rfl, he j t] -- ≤ vs <
 obtain ⟨z,h⟩:= cauchySeq_tendsto_of_complete hp
 refine ⟨z, Metric.tendsto_nhds.mpr (fun ε e=>?_),h,Metric.tendsto_nhds.mpr (fun ε e=>?_)⟩
 · obtain ⟨d,v⟩:= eventually_atTop.mp (l (ε/2) (by positivity)); obtain ⟨m,t⟩:= eventually_atTop.mp (Metric.tendsto_nhds.mp h (ε/2) (by positivity)); filter_upwards [eventually_ge_atTop (d,m)] with u hg; exact (dist_triangle _ (f u.2) _).trans_lt ((add_lt_add (v u.1 hg.1 u.2) (t u.2 hg.2)).trans_eq (add_halves ..))
 obtain ⟨m,hh,hq⟩:= ((k (ε/3) (by positivity)).and (Metric.tendsto_nhds.mp h (ε/3) (by positivity))).exists
 filter_upwards [l (ε/3) (by positivity)] with n hn
 have hu:= dist_triangle (g n) (K n m) z; rw [dist_comm (g n) (K n m)] at hu
 have ht:= dist_triangle (K n m) (f m) z; linarith only [hh n,hq,hn m,ht,hu]

lemma spot {z:ℂ}(s:Bool)(p:Tendsto (fun i:ℕ=>inner ℂ ξ (P.wind (if s then (i:ℤ) else -(i:ℤ)) η)) atTop (𝓝 z)) : z=inner ℂ ξ (P.calm η):=by
 let D(n:ℕ):ℤ:=if s then (n:ℤ) else -(n:ℤ)-(n:ℤ)
 let L(n:ℕ)(i:Fin (n+1)):=P.wind (D n + ↑↑i) η
 have hp:Tendsto (fun n:ℕ=>Average.center fun i=>inner ℂ ξ (L n i)) atTop (𝓝 z) := by
    apply Metric.tendsto_nhds.mpr; intro ε e
    obtain ⟨d,h⟩:= eventually_atTop.mp (Metric.tendsto_nhds.mp p (ε/2) (by positivity)); filter_upwards [eventually_ge_atTop d] with n t
    have V(i:Fin (n+1)): dist (inner ℂ ξ (L n i)) z≤ ε/2:=by
       unfold L D; cases s
       · change dist (inner ℂ ξ (P.wind (-(n:ℤ)-(n:ℤ)+i.val) η)) _ ≤_
         let m:=2*n-i; have hx:n≤m:=by unfold m; omega
         specialize h m (t.trans hx); change dist (inner ℂ ξ (P.wind (-(m:ℤ)) η)) z < _ at h; rw [show -(n:ℤ)-(n:ℤ)+i.val= -(m:ℤ) from (by unfold m; omega)]; exact h.le
       change dist (inner ℂ ξ (P.wind ((n:ℤ)+i.val) η)) _ ≤_
       specialize h (n+i) (by omega); change dist (inner ℂ ξ (P.wind (↑(n+i.val:ℕ)) η)) z < _ at h; push_cast at h; exact h.le
    exact lt_of_le_of_lt (by simpa only [Average.constant] using Average.norm_dist V) (half_lt_self e)
 have hP:= (tendsto_const_nhds (x:=ξ)).inner (𝕜:=ℂ) (P.shifted D η) -- name
 apply tendsto_nhds_unique hp; convert hP using 1
 funext i; exact Average.natural _ (innerSL ℂ ξ)

include P U ξ η A B in
lemma quadrant (h: Stock K P ξ η)(u: Stock (fun a b=> K b a) U A B): Tendsto (fun t:ℕ×ℕ=> K t.1 t.2) atTop (𝓝 (inner ℂ ξ (P.calm η))) :=by
 obtain ⟨z,v,w,_⟩:= two_purse (f:=fun i:ℕ=>inner ℂ ξ (P.wind i η)) (g:=fun i:ℕ=>inner ℂ A (U.wind i B)) (K:=fun i j:ℕ=>K i j) (fun ε e=> (h ε e).mono fun i hi m=> hi m) (fun ε e=> (u ε e).mono fun i hi m=> hi m)
 rw [spot P ξ η true w] at v; exact v

-- flip extends if orientation changed (U')
lemma aftB (h:Stock K P ξ η)(r:Stock (fun m n=> K n (-m)) U A B): Tendsto (fun t:ℕ×ℕ=> K t.1 (-(t.2:ℤ))) atTop (𝓝 (inner ℂ ξ (P.calm η))) :=by
 obtain ⟨z,v,w,_⟩:= two_purse (f:=fun i:ℕ=>inner ℂ ξ (P.wind (- (i:ℤ)) η)) (g:=fun i:ℕ=>inner ℂ A (U.wind i B)) (K:=fun i j:ℕ=>K i (- (j:ℤ))) (fun ε e=> (h ε e).mono fun i hi m=> hi (- (m:ℤ))) (fun ε e=> (r ε e).mono fun i hi m=> hi m)
 rw [spot P ξ η false w] at v; exact v
end YM.Signs
#print axioms YM.Signs.aftB
