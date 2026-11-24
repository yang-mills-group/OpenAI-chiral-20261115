import YM.SU5.May.LunarWickets
import YM.SU5.FiniteGaugeData.ArchiveK.Belling
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar.Rink
open Function Filter Finset Real Complex
open scoped Topology BigOperators ENNReal Classical
variable {D Q d:ℕ}{α:Type*} {Z:ℝ}(v:0<Z)
open Window.ArchiveK Polynomial
variable (u:ℂ) (θ:ℝ)
include v
lemma at_pow (e:d<D): ∑ i∈fling D, lagD Z D i * (ferryD Z i:ℂ)^d=(-1:ℂ)^d:=by
 have he:(_root_.Polynomial.X^d:Polynomial ℂ).degree < ↑D:=by rw [degree_X_pow]; exact_mod_cast e -- tune
 simpa only [eval_pow,eval_X] using report v he
lemma tableQ : ∑ i∈fling D, lagD Z D i * (say D (u*(ferryD Z i:ℂ)))=say D (u*(-1)):=by
 unfold say; simp_rw [mul_pow,mul_sum]; rw [sum_comm]; refine sum_congr rfl fun i h=>?_
 simp_rw [show ∀ k, lagD Z D k * (u^i*↑(ferryD Z k)^i/(i.factorial:ℂ))=u^i * (lagD Z D k*(ferryD Z k:ℂ)^i)/(i.factorial:ℂ) from fun k=>by ring, ← Finset.sum_div,←Finset.mul_sum]; rw [at_pow v (mem_range.mp h)]
noncomputable def chillD (D:ℕ):ℝ:= Real.exp (-(D:ℝ))
omit v in
lemma chill_pos(D:ℕ):0<chillD D:=Real.exp_pos _ -- include v warning
omit v
noncomputable def flight :ℝ:= Real.exp (Real.exp 1)
lemma flight_p : 0 <flight:= Real.exp_pos _
lemma fares (ε:‖u‖≤1) : ‖Complex.exp u-say D u‖ ≤ chillD D * flight:= by
 let t:= Real.exp (- (1:ℝ)); have he: t^D=chillD D:=by unfold t chillD; rw [←Real.exp_nat_mul]; ring_nf
 have ht:‖u‖/t ≤ Real.exp 1:=by apply le_trans (div_le_div_of_nonneg_right ε (Real.exp_nonneg _)) (le_of_eq ?_); rw [Real.exp_neg]; field
 exact (murmurE D (show 0<t from Real.exp_pos _) (Real.exp_le_one_iff.mpr (by norm_num)) u).trans (by rw [he]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone ht) (Real.exp_nonneg _))
local notation "S"=> fling D
include v
lemma pennies (ε:‖u‖≤1) (e:∀ i∈ fling D,‖u*(ferryD Z i:ℂ)‖ ≤1): ‖Complex.exp (-u)-∑ i∈fling D,lagD Z D i * Complex.exp (u*ferryD Z i)‖ ≤ (5*flight)*chillD D:=by
 let b:= (5*flight)*chillD D; let d:= chillD D*flight; let w(i):= lagD Z D i; let z(i):=u*ferryD Z i; let B:=∑ i∈S,w i*Complex.exp (z i); let A:=say D (-u)
 have he:A= ∑ i∈S,w i*say D (z i):=by unfold A; nth_rw 1 [show -u=u*(-1) from (by ring)]; exact (tableQ v _).symm
 have hv:‖A-B‖≤4*d:=by
    rw [he]; unfold B; rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (windowPrice v D) (mul_nonneg (Real.exp_nonneg _) flight_p.le)); rw [sum_mul]; apply sum_le_sum; intro i v; rw [←mul_sub,norm_mul,norm_sub_rev]; exact mul_le_mul_of_nonneg_left (fares _ (e i v)) (norm_nonneg _)
 exact (norm_sub_le_norm_sub_add_norm_sub _ A B).trans ((add_le_add (fares _ (norm_neg u ▸ ε)) hv).trans_eq (by unfold d; ring)) -- arg p orientation
section packt
variable [Fintype α] {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E](f: α→ℂ)(a:α→E)
noncomputable def showers (x:ℝ):E:=∑ i:α,Complex.exp (f i*x) • a i
local notation "ι'" => showers f a
local notation "G"=> lagD Z D
variable (e:∀ i,‖f i‖≤1) (k:∀ i∈ fling D,∀ a, ‖f a*(ferryD Z i:ℂ)‖≤1)
include e k
lemma roof_meter : ‖ (ι') (-1) - ∑ i∈fling D, lagD Z D i • (ι') (ferryD Z i)‖ ≤ (5*flight)*chillD D * ∑ i:α,‖a i‖:=by
 unfold showers; simp_rw [ofReal_neg,ofReal_one,mul_neg,mul_one,Finset.smul_sum,smul_smul]; rw [(sum_comm (s:=S)), ← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; rw [mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [← Finset.sum_smul,← sub_smul, norm_smul]; exact mul_le_mul_of_nonneg_right (pennies v (f i) (e i) (fun i' v=> k i' v i)) (norm_nonneg _)
lemma talented (h:0<D): ∃ i∈fling D,‖(ι') (-1)‖ ≤4*‖(ι') (ferryD Z i)‖+5*flight*chillD D*(∑ u:α,‖a u‖):=by
 let f'(i):=(ι') (ferryD Z i); obtain ⟨i,v',hi⟩:= exists_max_image (S) (fun i=> ‖f' i‖) ⟨D,(fling_up _).2 ⟨h,le_rfl⟩⟩; let A:= ∑ i∈fling D,(G) i • f' i; refine ⟨i,v',?_⟩; rw [add_comm]; apply (norm_le_norm_sub_add _ A).trans; refine add_le_add (roof_meter v f a e k) ?_; refine (norm_sum_le ..).trans <| le_trans ?_ (mul_le_mul_of_nonneg_right (windowPrice v D) (show 0≤‖f' i‖ from norm_nonneg _)); rw [sum_mul]; exact sum_le_sum fun j q=> by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hi _ q) (norm_nonneg _)
#print axioms talented
end packt
end YM.CF.May.Lunar.Rink
