import YM.OS.Flow
/-! # An inspector for seven scalar-propagation modes.
 Keep precision requirements finite and separate from the purchase. Uses only priced forward matrix entries. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.SatinJets
open Function Filter NormedSpace InnerProductSpace Finset Set MeasureTheory
open scoped Topology BigOperators Matrix ComplexOrder InnerProductSpace Classical
variable {H: Hilbert}
abbrev Seven:= Fin 7
def stride(i:Seven):ℕ:= 1000^i.val
def leader(i:Seven):ℝ:= ↑(stride i)
lemma leader_pos (i:Seven): 0<leader i:= Nat.cast_pos.mpr (pow_pos (by decide) _)
abbrev bill7(i j:Seven):ℝ:= (leader i+leader j)^8
def weight7(i:Seven):ℝ:= leader i^4
lemma weight7_p(i:Seven): 0<weight7 i:=pow_pos (leader_pos i) _
private lemma hold_price (i:Seven):512*(weight7 i)^2 =2*(bill7 i i):=by unfold bill7 weight7; ring
private lemma splitUnit {i j:Seven}(h:i<j): 1000* leader i≤ leader j:=by
 unfold leader; exact_mod_cast (show 1000*stride i ≤ stride j from (pow_succ' .. |>.symm).trans_le (Nat.pow_le_pow_right (by omega:0<1000) h))
private lemma wide (i j:Seven)(h:i<j): 65536*(weight7 i * weight7 j) ≤ bill7 i j:= by
 have hx:=leader_pos i; have hp:=leader_pos j
 have hv:= pow_le_pow_left₀ (show 0≤1000*leader i by positivity) (splitUnit h) 4; rw [mul_pow] at hv; let k:=weight7; change _*(k i*k j) ≤ _; refine le_trans (b:= (leader j)^8) ?_ (pow_le_pow_left₀ hp.le (le_add_of_nonneg_left hx.le) _)
 unfold k weight7; suffices 65536*leader i^4≤ leader j^4 by linarith only [mul_le_mul_of_nonneg_right this (sq_nonneg (leader j^2)|>.trans (show (leader j^2)^2≤leader j^4 from Eq.le (by ring)))] -- tune
 linarith only [hv,pow_nonneg hx.le 4]
private lemma spread {i j:Seven}(h:i≠j): 65536*(weight7 i * weight7 j) ≤ bill7 i j:=by
 rcases lt_or_gt_of_ne h with h|h; exact wide i j h; simpa [bill7,mul_comm,add_comm] using wide j i h -- order
lemma bill_p (i j:Seven):0<bill7 i j:=pow_pos (add_pos (leader_pos _) (leader_pos _)) _
local notation "R" i:max j:max=> bill7 i j
local notation "Ω"=> weight7
variable (v w : Seven→ H)(b:ℝ)(g:0<b)
/-- Keep even on rays after arbitrary paid errors. -/
def tempo (v w: Seven→ H)(p:ℝ)(δ:ℝ): Prop := ∀ i j:Seven, ‖ (bill7 i j:ℂ)* inner ℂ (w i) (v j)-(p:ℂ)‖≤δ
variable (q:tempo v w b (b/2))
noncomputable abbrev subU (v:Seven → H) (i:Seven):= ((weight7 i):ℂ) • v i
local notation "S" i:max j:max=> inner ℂ (subU w i) (subU v j)
include g q
private lemma scaled (i j:Seven): b/2 ≤ (R i j)*‖inner ℂ (w i) (v j)‖ ∧ (R i j)*‖inner ℂ (w i) (v j)‖ ≤ 2*b :=by
 let z:= inner ℂ (w i) (v j); let x:=(R i j:ℂ)*z; have hx: ‖x‖= (R i j)*‖z‖:= by rw [show x=(_:ℂ) *z from rfl,norm_mul,Complex.norm_real,Real.norm_of_nonneg (bill_p i j).le]
 have he : |‖x‖-‖(b:ℂ)‖| ≤ b/2 := (abs_norm_sub_norm_le x (b:ℂ)).trans (q i j); rw [Complex.norm_real,Real.norm_of_nonneg g.le] at he; obtain ⟨p,e⟩:=abs_le.mp he; change _ ≤ _*‖z‖ ∧ _*‖z‖≤_; constructor <;> linarith only [p,e,g,hx]
-- scaled diagonal norm, not entry sign. Hermitian not even required.
omit g q in
private lemma norm7 (i j:Seven) : ‖S i j‖=Ω i*Ω j*‖inner ℂ (w i) (v j)‖:=by
 unfold subU; rw [inner_smul_left,inner_smul_right]; simp_rw [Complex.conj_ofReal,norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight7_p _|>.le)]; ring
private lemma head_price (i:Seven): b/512 ≤ ‖S i i‖:=by rw [norm7]; have hx:=(scaled v w b g q i i).1; rw [show R i i=256*(Ω i*Ω i) from (by linarith only [hold_price i])] at hx; linarith only [hx]
private lemma tail_price (i j:Seven)(a:i≠j) : ‖S i j‖≤ b/32768:=by rw [norm7]; have hx:=(scaled v w b g q i j).2; linarith only [hx,mul_le_mul_of_nonneg_right (spread a) (norm_nonneg (inner ℂ (w i) (v j)))]
lemma tempos_price : LinearIndependent ℂ v:=by
 let x(i:Seven):ℂ:= Ω i; let U(i:Seven):ℂˣ:= Units.mk0 (x i) (by unfold x; exact_mod_cast (weight7_p i).ne'); refine (LinearIndependent.units_smul_iff v U).mp ?_; apply Fintype.linearIndependent_iff.mpr; intro c f i; change ∑ j:Seven,c j • subU v j=0 at f; by_contra! h
 obtain ⟨k,_,p⟩:= Finset.exists_max_image univ (fun j:Seven=>‖c j‖) univ_nonempty; have hp:0<‖c k‖:=lt_of_lt_of_le (norm_pos_iff.mpr h) (p i (mem_univ _)); let t(j:Seven):=c j *S k j; let V:= univ.erase k
 have hx: ∑ j:Seven,t j=0:=by unfold t; simp_rw [← inner_smul_right,←inner_sum,f,inner_zero_right]
 have ht:t k= - ∑ j∈V,t j:=by rw [← Finset.sum_erase_add _ _ (mem_univ k)] at hx; change ∑ j∈V,t j + t k=0 at hx; linear_combination hx
 have hq: ‖t k‖ ≤ ∑ j∈ V, ‖c k‖*(b/32768):=by
    rw [ht,norm_neg]; refine (norm_sum_le ..).trans (sum_le_sum fun i hi=> ?_); unfold t; rw [norm_mul]; exact mul_le_mul (p i (mem_univ _)) (tail_price v w b g q _ _ (mem_erase.mp hi|>.1.symm)) (norm_nonneg _) hp.le -- Ne.symm no `.symm`?
 rw [show (∑ j∈ V, ‖c k‖*(b/32768))=6*(‖c k‖*(b/32768)) from ?_, show ‖t k‖= ‖c k‖*‖S k k‖ from norm_mul ..] at hq; nlinarith only [hq, mul_pos hp g, mul_le_mul_of_nonneg_left (head_price v w b g q k) hp.le ]
 simp [V,Seven]
end YM.SatinJets
#print axioms YM.SatinJets.tempos_price
