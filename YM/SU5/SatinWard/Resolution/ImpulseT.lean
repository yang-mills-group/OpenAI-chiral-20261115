import YM.SU5.Assay.Spacers
import YM.SU5.Assay.Lamp
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.OS.Semigroup
namespace BasinWake
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}{j:Axis} (S:Semigroup H j)(v:H)(t:ℝ)
local notation "φ" => S.wax
local notation "V"=> H.Op
local notation "ω"=> S.wax
lemma wax_alive (a:ℝ)(p:0≤a): Function.Injective (ω a):=by
 let G(n:ℕ):= a*(1/2:ℝ)^n; have ht(n:ℕ):0 ≤ G n:= by unfold G; positivity
 have hp(n:ℕ): G (n+1) + G (n+1)=G n:=by unfold G; rw [pow_succ]; ring
 suffices Hx: ∀ v:H, ω a v=0 → v=0 by intro v u h; exact sub_eq_zero.mp (Hx (v-u) (by rw [map_sub,h,sub_self]))
 intro v h; have hh(n:ℕ):ω (G n) v=0:=by
    induction n with
    | zero=>simpa [G] using h
    | succ n ih=>
       let T:=ω (G (n+1)); have ht':T*T=ω (G n):=(S.wax_sq (ht _) (ht _)).trans (congrArg (ω) (hp n)); have he: inner ℂ (T v) (T v) = 0:=by rw [show inner ℂ (T v) (T v)=inner ℂ v ((T*T) v) from S.swing _ v (T v),ht',ih, inner_zero_right]
       exact inner_self_eq_zero.mp he
 have hn:Tendsto G atTop (𝓝 0):=by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).const_mul a
 have hv:Tendsto (fun n=>ω (G n) v) atTop (𝓝 v):=by have he := (S.wax_strong v).continuousAt.tendsto.comp hn; rw [S.wax_zero] at he; exact he
 exact tendsto_nhds_unique hv (tendsto_const_nhds.congr fun i=> (hh _).symm)
end BasinWake
end YM.OS.Semigroup
