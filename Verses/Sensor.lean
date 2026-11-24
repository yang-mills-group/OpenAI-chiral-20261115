import Verses.Cleat
import LusterS.Sleet
import YM.SU5.FiniteGaugeData.Pannier.Exacts
/-! # Wisp ecost. Adapted from `Exacts` (private tools copied to this namespace), `Graph/Zing` -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Pannier.Damask
namespace VelvetC
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
open Pressure RG YM.Gleam YM.Gleam.Luster YM.Gleam.Luster.Almanac CF.BProof Grade
open CF.Window
set_option linter.unusedVariables false
variable {N:Side}{R:GramM N}{V:Loom N}{h v η a C u t:ℝ}{r:ℕ}
-- volume expansion
abbrev kios (K:ℝ)(x:ℝ):ℝ:= temp x+2*Real.exp (-(K*radiusB x))
abbrev villar (K u:ℝ)(x:ℝ):ℝ:= u*(kios K x+(kios K x)^2)
lemma kios_grade {K:ℝ}(p:0<K): Grade (-1/2) (kios K):=by
 have he:=trail_b p; have hh:∀ i:ℝ,trail K (radiusB i)=Real.exp (-(K*radiusB i)):=by intro i; unfold trail; ring_nf
 simp_rw [hh] at he; exact temp_b.plus ((he.scaleB 2).grow (by norm_num))
lemma active_min {K u:ℝ}(p:0<K):Grade (-1/2) (villar K u):=by
 let h:=kios_grade p
 exact (h.plus ((h.pwr 2).grow (by norm_num))).scaleB _
lemma clear_q (c:ℝ)(q:Clip)(r:ℕ):∀ᶠ x in atTop,c*quake r (radiusB x) 1 ≤ (x/2)*(q.linear*temp x^2)/20:=by
 have hp:q.linear>0:=q.tail_pos
 let W(x:ℝ):= c*quake r (radiusB x) 1; have ht: PL W:=by
    unfold W quake; push_cast
    let H:=PL.ceil (PL.log_y.pow 2) (Eventually.of_forall fun i=>sq_nonneg _)
    let F:=radius_log.add (PL.const 1)
    exact (PL.const c).mul (((PL.const _).mul ((((radius_log.add radius_log).add (PL.const 1)).pow 4))).mul (PL.const _)) -- actually d+d+1, not d+1+d+1+1? quake d+d+1 so F+radius?? F=R+1, F+R+1 mismatch
 let a:=40/q.linear
 filter_upwards [eventually_gt_atTop (0:ℝ), coin_strongLt (f:=fun x=>a*W x) (a:=0) (b:=2) (by norm_num) ((PL.const a).mul ht)] with x hx g
 have he: x*temp x^2= coin x 0 2 0:=by rw [scale_shock hx]; unfold scaleY; rw [coin_pow]; norm_num -- imported scale_shock? namespace Almanac
 unfold a at g
 change W x≤_
 rw [←he] at g
 field_simp [hp.ne'] at g
 have hz:=le_abs_self (40*W x)
 have hf:=le_abs_self (40*W x/q.linear); nlinarith only [(div_lt_iff₀ hp).mp (hf.trans_lt g)]
lemma hunt_γ (u₀:ℝ)(p:0≤u₀)(s:0<a)(d:0≤C)(z:0<u)(p0:Clip): ∀ᶠ x in atTop,∀ {N:Side}{V:Loom N}{R:GramM N}{h v η:ℝ},(radiusB x) ≤ N.val → Ledger h v η a C R → Roof N u t r V → ∀ y:Orbit N,
 u₀*entryBudget (R.J.P.den (V y))+ ‖Pec.pigment R.J.I (V y)‖ ≤ x^(-tauA)*(More N).val^4+(x/2)*(p0.linear*temp x^2)/20*flakes (temp x) y.1:=by
 let B:= u₀*180*180*45*180+C+1 -- coefficients. C input multiplicative. adjust
 let c:=u₀*180*180*45*180*C+C
 let δ:=u₀*180*180*45*6*C+4*C
 have hd:0≤ c:=by unfold c; positivity
 filter_upwards [(active_min (u:=c) s).cost_p (b:=-tauA) (by norm_num [tauA]),clear_q δ p0 r,eventually_gt_atTop (0:ℝ),(temp_b.roots (by norm_num)).eventually (ge_mem_nhds z)] with x he hk hx ht N V R hg1 vg η hi H W y
 obtain ⟨a0,b⟩:= renewal_mini y R H W ht s.le (Work.E09.temp_pos hx).le (hi.trans (Nat.le_mul_of_pos_right _ two_pos)) d (kios a x) le_rfl
 apply (add_le_add (mul_le_mul_of_nonneg_left a0 p) b).trans
 let e:=kios a x; have H':0≤e:=by unfold e kios; have h:= Work.E09.temp_pos hx; positivity
 let m:=quake r (radiusB x) 1
 let Z:=flakes (temp x) y.1; have hZ:0≤Z:=by unfold Z flakes; positivity
 let q:= (N.val:ℝ)^4; have hv:q ≤ ((More N).val:ℝ)^4:=by unfold q; gcongr; exact_mod_cast (Nat.le_mul_of_pos_right N.val (by decide:(0:ℕ)<2))
 have hh:c*(e+e^2)≤ x^(-tauA):=(le_abs_self _).trans he
 have hb:0≤x^(-tauA):=Real.rpow_nonneg hx.le _
 unfold storm paintE pittance; rw [Pic.units_t]
 change u₀*(180*180*((180*(N.val:ℝ)^4*(45*(e^1*C))+quake r (radiusB x) Z*(45*(2^1*C)))+(180*q*(45*(e^2*C))+quake r (radiusB x) Z*(45*(2^2*C)))))+(e^2*C*q+quake r (radiusB x) 1*4*C*Z) ≤ _ -- Pic.units_t ℕ or ℝ?
 have he' : quake r (radiusB x) Z=Z*m:=by unfold m quake; ring
 rw [he']
 have hk:=mul_le_mul_of_nonneg_right hk hZ
 have hf: c*(e+e^2)*q ≤ x^(-tauA)*((More N).val:ℝ)^4:= mul_le_mul hh hv (pow_nonneg (Nat.cast_nonneg _) _) hb
 unfold c at hf; unfold δ at hk; unfold q m at *; nlinarith only [hk,hf,mul_nonneg (mul_nonneg d H') (pow_nonneg (Nat.cast_nonneg (α:=ℝ) N.val) 4)]
end VelvetC
end YM.CF.Pannier.Damask
