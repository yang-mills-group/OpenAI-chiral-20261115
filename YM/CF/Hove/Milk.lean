import YM.CF.Hove.Prune
import YM.CF.Haro.Wind
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable (j m:ℕ)(e:Even j)(p:4≤j)
variable {c f :Side}(o:Site c)(G:Ratio c f)(w:Odd G.count.val)(L:Op (Single f))(M:Male)
local notation "Sρ"=> (heel G o)
local notation "W"=> nook_T o m
local notation:max "φ"=> nook_T (heel G o) m
open Haro Branch Laic
variable {t:ℝ}(Y:cro G t)(P:Meter TailB G t){a b A C a' c' :ℝ}{l k n j':ℕ}(X:∀ i:TailB,Support (More f)→ Toll (Iota G))(pR:∀ i x,Suite (badge _) (pinH G t true) (pinH G t false) x (X i x) (P i x))(hk:∀ i,incline (hall G t) j' a' (fun _=>C) b (X i))(hc:0≤a')(hb:3*a≤b)(hp:0<a)(he:a ≤ 1)(h:0≤ C)
local notation "Π"=> (2:ℝ)^m
local notation "Zp(" l ")"=> (mintY m (a:=a) (C:=C) l)
include w
private lemma hop(x:Single f)(y:Single c): W y≤ Π* φ x * Tap.streak G m x y:=by
 let S:=node Sρ; let X:= place_x x; let T:=place_x y; let Δ:= (ratio G).parent X; have he:(ratio G).parent S=node o:=by unfold S heel; rw [embed_node G w]; simp [Ratio.embed_parent] -- lift
 have hx: separation (node o) T ≤ separation S X+1+ separation Δ T:= (separation_triangle _ Δ _).trans (Nat.add_le_add_right (he ▸ Work.E04.parent_separation (ratio G) S X) _)
 have hp:(separation (node o) T:ℝ)≤ separation S X +1 +(separation Δ T:ℝ):=by exact_mod_cast hx
 unfold nook_T Tap.streak gum; rw [← mul_pow,← mul_pow]; apply pow_le_pow_left₀ (by positivity); change 1+(separation (node o) T:ℝ) ≤ 2*(1+(separation S X:ℝ))*(1+(separation Δ T:ℝ)); nlinarith only [hp,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (separation S X)) (Nat.cast_nonneg (α:=ℝ) (separation Δ T)),Nat.cast_nonneg (α:=ℝ) (separation S X),Nat.cast_nonneg (α:=ℝ) (separation Δ T)] -- change
include pR hk hc hb hp he h
private lemma hi_k(J:Finset (Support (More f)))(hJ:∀ D∈J,l ≤ D.card)(A:Bool)(x:Single f): let F:=fun i:Single c=>cops G Y P J A x i; paidX W F ≤ Π* φ x * Zp(l) ∧ paidX (fun _=>1) F ≤ Zp(l):=by
 intro F; have he:0 ≤ Haro.frost m (a:=a) l :=by unfold Haro.frost polV; positivity
 have ht: paidX (Tap.streak G m x) F≤ Zp(l):=by
    apply le_trans (sum_le_sum fun y _=>reachV m G w Y P X pR hk hc hb hp (by assumption) J A x y l hJ)
    unfold mintY; rw [←sum_mul,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (coin_l G hp x) he) h
 constructor
 · unfold paidX; refine le_trans ?_ (mul_le_mul_of_nonneg_left ht (mul_nonneg (by positivity) (zero_le_one.trans (nook_l ..)))) -- ht is paidX reduc rewrite
   unfold paidX; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hop m o G w x i) (norm_nonneg _) -- note hop w implicit
 refine le_trans (sum_le_sum fun y _=> mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) ht -- maybe can't infer
 exact one_le_pow₀ (show 1≤1+(dish G x _ :ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg _))
local notation "ϵ"=> Π
local notation "Zτ"=> paid_M
variable (J K: Finset (Support (More f)))(hJ:∀ D∈J,l≤ D.card)(hK:∀ D∈K,k≤D.card)
include hJ hK
private lemma veil_P : paid_M o (saltW G Y P L J K) m ≤ Π*Zp(l)*Zp(k)*paid_M Sρ L m:=by
 let A_:= cops G Y P J true; let B:=cops G Y P K false; let F (x:Single f × Single f):= dishV (fun y=>A_ x.1 y) (fun y=>B x.2 y)
 have hz(x:Single f×Single f): paidX (coyF W) (F x)≤Π* Zp(l)* Zp(k) * coyF φ x:=by
    obtain ⟨p,q⟩:=hi_k m o G w Y P X pR hk hc hb hp he h J hJ true x.1; obtain ⟨z,s⟩:=hi_k m o G w Y P X pR hk hc hb hp he h K hK false x.2; let T:=coyF φ x; have hu:0≤ W:= fun i=>zero_le_one.trans (nook_l ..)
    unfold F; rw [fork_p,dish_p,dish_p]; refine (add_le_add (mul_le_mul p s (windL _ _ (fun _=>zero_le_one)) ((windL _ _ hu).trans p)) (mul_le_mul q z (windL _ _ hu) ((windL _ _ (fun _=>zero_le_one)).trans q))).trans_eq ?_; unfold coyF; ring -- tune
 let Yf(x:Single f×Single f): Single c×Single c→ℂ:= L x.1 x.2 • F x; -- name drop shadow
 unfold paid_M; rw [show pinF (A_ᴴ* L * B)= ∑ i,Yf i from ?_ ] -- rw under reveal. proof
 swap
 · ext1 x; change (A_ᴴ * L* B) x.1 x.2 = _; rw [Finset.sum_apply]; conv_rhs=>rw [Fintype.sum_prod_type, sum_comm]
   rw [Matrix.mul_apply]; apply Finset.sum_congr rfl; intro i _; rw [Matrix.mul_apply,Finset.sum_mul]; apply sum_congr rfl; intro j _; change star (A_ j x.1)*L j i*B i x.2 = L j i*(star (A_ j x.1)*B i x.2); ring
 apply (p_posts (coyF W) (fun x=>add_nonneg (zero_le_one.trans (nook_l o m x.1)) (zero_le_one.trans (nook_l o m x.2))) _ _).trans; unfold paidX; rw [Finset.mul_sum]; apply sum_le_sum; intro i _; change paidX (coyF W) (Yf i)≤ _; unfold Yf; rw [p_smul]; exact (mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)).trans_eq (by rw [mul_comm, mul_assoc]; rfl)
omit hJ hK
lemma melt (J:Finset (Support (More f)))(hJ:∀ i:Support (More f),i∉J→ l ≤ i.card): paid_M o (pulled G Y P L J-pulled G Y P L univ) m ≤2*(Π*Zp(l)*Zp(0))*paid_M Sρ L m:=by
 let V:= univ\J; let C:= saltW G Y P L V J; let Xp:= saltW G Y P L univ V; have ht(A):pulled G Y P L A = saltW G Y P L A A:=by unfold pulled saltW cops; simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum]; rw [sum_comm]
 have he(A):cops G Y P univ A=cops G Y P V A+cops G Y P J A:=by unfold cops; rw [Finset.sum_sdiff (subset_univ _)]
 have hz(i)(x:i∈V):l ≤ i.card:= hJ i (mem_sdiff.mp x).2
 rw [show pulled G Y P L J-pulled G Y P L univ= - (C+Xp) from ?_]; swap; · rw [ht,ht]; unfold C Xp saltW; rw [he,he, Matrix.mul_add, Matrix.conjTranspose_add,Matrix.add_mul]; simp_rw [Matrix.add_mul]; abel -- tune
 rw [show paid_M o (- (C+Xp)) m = paid_M o (C+Xp) m from p_negative (coyF W) (pinF _)]
 exact (paidp_sum ..).trans ((add_le_add (veil_P m o G w L Y P X pR hk hc hb hp (by assumption) h V J hz (fun _ _=>Nat.zero_le _)) (veil_P m o G w L Y P X pR hk hc hb hp (by assumption) h univ V (fun _ _=>Nat.zero_le _) hz)).trans_eq (by ring))
end YM.CF.Hove
