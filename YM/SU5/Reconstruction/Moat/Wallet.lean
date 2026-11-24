import YM.SU5.Reconstruction.Moat.Sonic
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Moat
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup ConePrice
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x
local notation "D" p:max t:max => Real.exp (-(p a)*(t:ℝ))
open Finset
variable {ι:Type}[Fintype ι] (x:ι→Cross a)(r:ℝ≥0) (v f:H)(u u' C:ℝ)
local notation "N"=> (Fintype.card ι:ℝ)
variable (Q: Forward S) (U:∀ i j:ι, u'*‖x i-x j‖ ≤ 1) {k:ℝ} (z:0≤k) (t:k*(r:ℝ) ≤ 1-Real.exp (-u*(r:ℝ))) (g: ‖v‖≤C)(h:‖f‖≤C)
include Q U z t g h
lemma wallet (q:ℝ)(p:0≤q)(L : ∀ i j:ι, i≠j→tariff S v r (x i-x j)+tariff S f r (x i-x j)≤ q) :
 (N^2/2)*(k*r)* (‖(P).region (band a u u') v‖^2+‖(P).region (band a u u') f‖^2) ≤ (N*q+4*C^2)*N:=by
 classical
 rw [mul_add] -- danger matches RHS!
 have hh:= add_le_add (bandCost S x r u u' Q U z t v) (bandCost S x r u u' Q U z t f); apply hh.trans; rw [←sum_add_distrib]; simp_rw [←sum_add_distrib]
 let ξ (i j:ι):= tariff S v r (x i-x j) + tariff S f r (x i-x j)
 have he (i:ι): ∑ j:ι,ξ i j ≤ N*q+4*C^2:= calc
    _ ≤ ∑ j:ι, (q+ if i=j then 4*C^2 else 0) := sum_le_sum fun j _=> by
              split_ifs with e
              · exact ((add_le_add (tariff_cap S g r _) (tariff_cap S h r _)).trans (b:=2*C^2+2*C^2) (by linarith)) -- proofs
              simpa using L i j e
    _ = _ := by rw [sum_add_distrib]; simp -- tune
 calc
    _ ≤ ∑ _ : ι,(N*q+4*C^2):=sum_le_sum fun i _=> he i
    _ = _:=by simp; ring

omit Q U z t g h
section
-- economics Abel Bound. Can arrange with two time units (h and d in meshes) and arbitrarily small slack at SAME barrier
variable {d l' M:ℝ}
lemma winnow (Z:ℝ)(p:0<Z)(h:0<k)(u:0<l')(M:ℝ)(t:0<M)(C:ℝ) : ∀ᶠ n:ℕ in atTop,∀ r:ℝ, 1/(n:ℝ)^5≤r → r ≤ 2/(n:ℝ)^5 → (let v:= l'/(4*(n:ℝ)^2); let q:= M*r^2/v^2; ((n:ℝ)^6*q+4*C^2)*(n:ℝ)^6 < ((n:ℝ)^6)^2/2*(k*r)*Z^2):= by
 -- choose n to meet; scale. parameter D unused adjust
 let a:ℝ:= 64*M/l'^2+4*C^2
 filter_upwards [eventually_gt_atTop 0,(tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2*a/(k*Z^2))))] with n hn e
 intro r w v b q
 let K:ℝ:= n; change 2*a/(k*Z^2) < K at e; have hK:0<K:= Nat.cast_pos.mpr hn
 have vv:r ≤ 2/K^5:=v; have rr:1/K^5≤r:=w; have r':0 < r:=lt_of_lt_of_le (by positivity) rr
 have hq: K^6*q ≤ 64*M/l'^2:= calc
       _ ≤ K^6*(M*(2/K^5)^2/b^2):= by unfold q; gcongr
       _ = _:= by unfold b; change K^6*(M * (2 / K^5)^2 / (l'/(4*K^2))^2)=_; field_simp; ring
 refine ((mul_le_mul_of_nonneg_right (add_le_add_left hq _) (by positivity : 0≤ K^6))).trans_lt (b:=a*K^6) ?_
 calc
    _ < (K*(k*Z^2)/2)*K^6:= mul_lt_mul_of_pos_right (by have hz:2*a<K*(k*Z^2):=(div_lt_iff₀ (by positivity)).mp e; linarith) (by positivity)
    _ = (K^6)^2/2*(k*(1/K^5))*Z^2:=by field_simp
    _ ≤ _:= by change _ ≤ _/ (2:ℝ)*(k*r)*Z^2; gcongr
end
end YM.Moat
