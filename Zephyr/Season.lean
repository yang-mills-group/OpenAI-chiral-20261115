
import YM.CF.Sere.Gilt
import Zephyr.Poly

/-! Return to tiny scales. y and g take the slope *shift*, temp
takes x itself. w is defined with the latter argument. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Zephyr
open Lattice RG Pressure Filter SectorNext.Remainder Py
open scoped Topology
variable (L:Side)

abbrev q124 (x:ℝ):=(Scales.g SU.group L x)^2
def w124 (x:ℝ):=Real.exp ((Real.log (Real.log x))^2)

lemma w124_one (x:ℝ): 1 ≤ w124 x:= Real.one_le_exp (sq_nonneg _)

theorem dleaf_cmp : ∀ᶠ x:ℝ in atTop,
    0 ≤ dleaf L x ∧ dleaf L x ≤ 2*(q124 L x*w124 x):= by
 filter_upwards [(Scales.year SU.group L).eventually_gt_atTop 0,eventually_gt_atTop 0,eventually_ge_atTop (SU.group.slopeConstant*Real.log L.val)] with x hx ht hk
 let y:=Scales.y SU.group L x
 let x':=Real.sqrt x; let y':=Real.sqrt y
 have x0:0 < x':=Real.sqrt_pos.mpr ht
 have y0:0 < y':=Real.sqrt_pos.mpr hx
 have x1:0 ≤ w124 x:=(Real.exp_pos _).le
 have t:y ≤ 4*x:= (by unfold y Scales.y betaF; linarith only [ht,hk])
 have e:y' ≤ 2*x':=by 
   dsimp only [x',y']
   exact (Real.sqrt_le_sqrt t).trans_eq (by rw [Real.sqrt_mul] <;> norm_num)

 have j:x'⁻¹ ≤ 2*y'⁻¹:=by rw [←one_div,← div_eq_mul_inv,div_le_div_iff₀ x0 y0]; rwa[one_mul]
 constructor
 · change 0≤ y'⁻¹*(x'⁻¹*w124 x); positivity
 change y'⁻¹*(x'⁻¹*w124 x) ≤ 2*((y'⁻¹)^2*w124 x)
 exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right j x1) (inv_nonneg.mpr y0.le)).trans_eq (by ring)

theorem polyDash {f:ℕ→ℝ}(p:Poly f): ∀ᶠ x:ℝ in atTop,
    Real.exp (-(radiusB x:ℝ)/2)* f (radiusB x) ≤ q124 L x:=by
 obtain ⟨C,h,m,hp⟩:=p.maj
 let z x:=Scales.y SU.group L x
 let b(x:ℝ):=radiusB x
 have g: Tendsto (fun x=>C*(z x *(((b x:ℝ)+1)^m * Real.exp (-(1/2:ℝ)*(Stores.till x))))) atTop (𝓝 (0:ℝ)):=by
   simpa only [Scales.b,b,z,pow_zero,mul_one,mul_zero,add_comm] using
     (Scales.cutoff SU.group L m 0 (τ:=1/2) (by norm_num)).const_mul C
 filter_upwards [g.eventually (ge_mem_nhds zero_lt_one),(Scales.year SU.group L).eventually_gt_atTop 0] with x t h0
 let i:=b x; let j:=Stores.till x
 have hB : (j:ℝ)≤ i:=by exact_mod_cast Nat.div_le_self (b x) 100000

 have hi:Real.exp (-(i:ℝ)/2)≤Real.exp (-(1/2:ℝ)*j):= Real.exp_le_exp.mpr (by linarith only [hB])
 apply le_of_mul_le_mul_left (a:=z x) _ h0
 rw [show z x*q124 L x=1 from Scales.yg2 SU.group L h0]
 apply le_trans _ t
 calc
   _ ≤ z x * (Real.exp (-(i:ℝ)/2)*(C*((i:ℝ)+1)^m)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hp i) (Real.exp_pos _).le) h0.le
   _ ≤ z x * (Real.exp (-(1/2:ℝ)*j)*(C*((i:ℝ)+1)^m)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi (by positivity)) h0.le
   _ = _ :=by dsimp only [i,j]; ring
end YM.CF.Zephyr
