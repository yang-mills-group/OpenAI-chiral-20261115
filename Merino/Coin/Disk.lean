import Merino.Corolla.Seasons

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Coin
open Function Finset Lattice Cube RG Scree Skye Fock
open scoped Topology Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Rive Py Roots QuadClock Oise Mew Neon Waxy
open Vow TreasuryFog Dial Paige Vault
open scoped YM.CF.Mew
variable {N B:Side}
variable {I:Type}[Fintype I][LinearOrder I]
local notation "X"=>mid N B

open Filter
open BPress (lscale NPL PL)
open SectorNext.Remainder
open Pressure


open Fief
variable (R:Patch)
local notation "L"=> R.L
local notation "ι"=>(1/256:ℝ)

lemma tithe (j:ℕ): sizeK L (2*(j+1)) (fun x:ℝ=> Real.exp (-ι*(radiusB x:ℝ))):=by
 let k:=ι/(j+1); have he:0<k:=by unfold k; positivity
 apply ((sizeK.tip L k he).square (j+1)).cost_d
 filter_upwards with x; rw [abs_of_pos (Real.exp_pos _)]
 refine le_trans ?_ (le_abs_self _); unfold Neige.tipPay; rw [←Real.exp_nat_mul]; apply Real.exp_monotone
 push_cast
 have ht:(↑(radiusB x/60):ℝ) ≤ (radiusB x:ℝ):=by exact_mod_cast (Nat.div_le_self (radiusB x) 60)
 rw [neg_mul,neg_mul, mul_neg,←mul_assoc,show ((j:ℝ)+1)*k= ι from by unfold k;field_simp ] -- may comm
 linarith



-- solution for t calls per hub, each powered to lscale^k.
lemma profile0 (t k:ℕ):
 ∀ᶠ x in atTop,(2*(Corolla.cur L k x)⁻¹)^t ≤ Real.exp (ι*radiusB x):= by
 let g:=Scales.g SU.group L
 have h:=pill_R (k:=4*t) (d:=1) _ (by norm_num)
      (((tithe R (2*t)).scale ((2:ℝ)^t)).low (by omega))
 have s:=((nq L).vanish k).eventually (ge_mem_nhds one_pos)
 filter_upwards [draft_π L,h,s] with x p u w
 let b:= lscale x^k
 let q:=pinpr L x
 have hz:0<q:=pow_pos p.2.1 _
 have ht:0<b:=pow_pos (zero_lt_one.trans_le (BPress.lscale_one x)) _
 have hv: (Corolla.cur L k x)⁻¹ ≤ 1/q^2:=by
      change (q/b)⁻¹ ≤ 1/q^2
      rw [inv_div,le_div_iff₀ (by positivity : 0<q^2), pow_two,←mul_assoc,div_mul_cancel₀ _ hz.ne']
      exact w
 refine (pow_le_pow_left₀ (by change 0 ≤ 2*(q/b)⁻¹; positivity) (mul_le_mul_of_nonneg_left hv zero_le_two) t).trans ?_
 -- rest
 change 2^t * Real.exp (-ι*radiusB x)<1*g x^(4*t) at u


 rw [neg_mul, Real.exp_neg,←div_eq_mul_inv,div_lt_iff₀ (Real.exp_pos _),one_mul] at u
 rw [mul_one_div,div_pow,div_le_iff₀ (by positivity : 0 < (q^2)^t), mul_comm]
 exact u.le.trans_eq (by rw [show q^2=g x^4 from by unfold q pinpr;rw [←pow_mul], ←pow_mul])

lemma profile (t k:ℕ): ∀ᶠ x in atTop, Nice_B (radiusB x) t (2*(Corolla.cur L k x)⁻¹) (1/8):=by
 filter_upwards [profile0 R t k,Work.E01.radiusB_tendsto.eventually
    (chill_K (1/16) 1 t le_rfl (by norm_num)),draft_π L,
    Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x g h z e m vm
 let B:=radiusB x
 let c:=chip_B B m/cape_B B
 let f:= 2*(Corolla.cur L k x)⁻¹
 have hs:0≤ f:=by
    have :0<pinpr L x:=pow_pos z.2.1 _
    have :=BPress.lscale_one x
    unfold f Corolla.cur; positivity
 have t0:= h m vm
 have hb:(c:ℝ)*B≤6*m:=by exact_mod_cast sev_B B m e


 have hx:=mul_le_mul t0 (pow_le_pow_left₀ (pow_nonneg hs _) g (c+1))
     (pow_nonneg (pow_nonneg hs t) _) (Real.exp_pos _).le
 have hh:Real.exp ((1/16)*(m:ℝ))*Real.exp (ι*(B:ℝ))^(c+1) ≤ Real.exp ((1/8)*(m:ℝ)):=by
   rw [←Real.exp_nat_mul,←Real.exp_add]; apply Real.exp_le_exp.mpr
   push_cast
   have m1: (B:ℝ) ≤ m:=Nat.cast_le.mpr vm
   nlinarith only [hb,Nat.cast_nonneg (α:=ℝ) m,m1]
 refine le_trans (le_of_eq ?_) (hx.trans hh)
 change rentP f B m t= rentP 1 B m t*(f ^ t)^(c+1)
 rw [←pow_mul, Nat.mul_comm t]
 unfold rentP; rw [mul_pow (2:ℝ) f,mul_one]
 exact (mul_assoc ..).symm


lemma seats (t k:ℕ): ∀ᶠ x in atTop, let b:=Corolla.cur L k x
  0<b∧b ≤ pinpr L x ∧ wish_E (radiusB x) (Corolla.wovenV b t) ≤ pinpr L x∧ wish_E (radiusB x) b ≤ pinpr L x:=by
 let a(x:ℝ):= Real.exp ((- (1/4:ℝ))*(radiusB x:ℝ))*KZ
 have h:Tendsto a atTop (𝓝 0):=by
    have hh: Tendsto (fun x:ℝ=>(radiusB x:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
    have yy:Tendsto (fun x:ℝ=> (-(1/4:ℝ))*(radiusB x:ℝ)) atTop atBot:=
        hh.const_mul_atTop_of_neg (by norm_num)
    exact zero_mul KZ ▸ (Real.tendsto_exp_atBot.comp yy).mul_const KZ
 have j:Tendsto (fun x=> a x*(2*t+1)) atTop (𝓝 0):=by simpa using h.mul_const (2*(t:ℝ)+1)
 filter_upwards [draft_π L,h.eventually (ge_mem_nhds zero_lt_one),j.eventually (ge_mem_nhds zero_lt_one)] with x u v w b
 have hc:=BPress.lscale_one x
 have hz:0<pinpr L x:=pow_pos u.2.1 _
 have hy:0<b:=by unfold b Corolla.cur;positivity
 have hq:b ≤ pinpr L x:= div_le_self hz.le (one_le_pow₀ hc)


 refine ⟨hy,hq,?_, (mul_le_of_le_one_left hy.le v).trans hq⟩
 rw [show wish_E (radiusB x) (Corolla.wovenV b t)=(a x*(2*t+1))*b from by unfold a wish_E Corolla.wovenV;ring]
 exact (mul_le_of_le_one_left hy.le w).trans hq
end YM.CF.Merino.Coin

