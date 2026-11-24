import YM.SU5.Reconstruction.AllGrades.Lubricant
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {H W:Hilbert} {a: Axis} {Γ: AddSubgroup ℝ} (K: OS.Semigroup H a)(T:Germ.Alliance (CF.Buffered.Afterglow.Tower.Trans a) Γ H)(S:OS.Semigroup W a)
local notation "U" j:max v:max=> (T.crew j).play v

local notation "S₀"=> Coupon a Γ
/-! # From literal square-moments to continuity on double grid. -/
variable (i:CF.Buffered.Afterglow.Tower.Trans a) (v t : Γ) (p:0 ≤ (t:ℝ))(x:H)
local notation "R"=>sun a i v t p
local notation "cr"=> cross a i.val i.property
local notation "toℝ" p:max=> (p:ℝ).toNNReal
local notation "A"=> Lore K T x
lemma source(t:Γ)(p:0≤ (t:ℝ)): A (sun a i 0 t p)=inner ℂ x (K.E (toℝ t) x):=by unfold Lore; rw [sun_crew,(T.crew i).play_zero]; rfl
-- avoid measurable orbits assumptions; does not use any Thing other than heat strong continuity, crew, arity price.
local notation "xP"=> inner ℂ x x
def warmer (v:Γ): Γ:= if 0 ≤ (v:ℝ) then v else -v
local notation "τ" v:max=> warmer v
lemma true_norm (v:Γ): ((τ v):ℝ)= |(v:ℝ)|:=by unfold warmer; split_ifs with h; exact (abs_of_nonneg h).symm; exact (abs_of_neg (lt_of_not_ge h)).symm
local notation "p₀" v:max=> (show 0≤ ((τ v):ℝ) from (true_norm v).symm ▸ abs_nonneg _)
local notation "ν"=> 𝓝 (0:Γ)
lemma true_time{Γ:AddSubgroup ℝ}: Tendsto (fun v:Γ=> Real.toNNReal ((τ v):ℝ)) (𝓝 (0:Γ)) (𝓝 0):=by -- notation call
 have h: Continuous (fun v:Γ=> Real.toNNReal |(v:ℝ)|):= by fun_prop
 simp_rw [true_norm]; convert h.continuousAt (x:=0) |>.tendsto using 1; simp
local notation "θ" h:max v:max=> K.E (Real.toNNReal (((τ v):Γ):ℝ)*h)
local notation "g₁" v:max=> K.E (Real.toNNReal (((τ v):Γ):ℝ))
local notation "g₂" v:max=> K.E (Real.toNNReal ((τ v+(τ v):Γ):ℝ))
local notation "cc" v:max=> A (sun a i v ((τ v)+(τ v)) (show 0≤_ from add_nonneg (p₀ v) (p₀ v)))
local notation "kP" v:max => inner ℂ x ((U i v) x)
lemma less_time (x:H)(s:ℝ≥0):‖K.E s x‖ ≤ ‖x‖:= ((K.E s).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (K.shrinks s))
private lemma limitHeat {j:Γ→ℝ≥0}(h:Tendsto j ν (𝓝 0)) (x:H) : Tendsto (fun i=>K.E (j i) x) ν (𝓝 x):=by have ht:= ((K.continuousE x).tendsto 0).comp h; rw [K.eZero] at ht; exact ht
local notation "Rt" v:max=> Real.toNNReal ((τ v):ℝ)
private lemma τ₀ : Tendsto (fun v:Γ=> Real.toNNReal ((τ v+(τ v):Γ):ℝ)) ν (𝓝 0):=by
 simp_rw [AddSubgroup.coe_add]; let z(v:Γ):= p₀ v
 have ht(v:Γ): Real.toNNReal (((τ v):ℝ)+((τ v):ℝ))= Rt v + Rt v:= Real.toNNReal_add (z v) (z v)
 simp_rw [ht]; exact (zero_add (0:ℝ≥0)).symm ▸ true_time.add true_time -- tune ▸
local notation "m" => ‖x‖^2
local notation "Uq" => T.crew i
local notation "Θ" => (Uq).play
variable (Z:∀ (v:Γ) (s:ℝ≥0), ((T.crew i).play v).comp (K.E s)=(K.E s).comp ((T.crew i).play v))
include Z
lemma τ_dry : Tendsto (fun v:Γ=> (cc v)^2 - (kP v)^2) ν (𝓝 0):=by
 let Y(z:Γ):= (g₂ z) x; have ht: Tendsto Y ν (𝓝 x):= limitHeat K τ₀ _
 have he(v:Γ): (cc v)= inner ℂ x (Θ v (Y v)):= by unfold Lore; rw [sun_crew]; apply congrArg (inner ℂ x); exact DFunLike.congr_fun (Z v _).symm x
 let r(z:Γ):=kP z; let z(g:Γ):=cc g
 have bound(v:Γ): ‖z v + r v‖≤ 2*m:=by
    unfold z r; rw [he]; refine (norm_add_le ..).trans ?_
    have h(y:H)(v:Γ)(q:‖y‖ ≤ ‖x‖): ‖inner ℂ x (Θ v y)‖ ≤ m:=by rw [pow_two]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left ((((Uq).pulls v y).trans q)) (norm_nonneg _))
    linarith [(show _ from h (Y v) v (less_time ..)),(show _ from h x v le_rfl)]
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 refine squeeze_zero (fun _=> norm_nonneg _) (g:=fun v:Γ=>2*m* (‖x‖*dist (Y v) x)) ?_ ?_
 · intro v; change ‖z v^2-r v^2‖≤_; rw [sq_sub_sq,norm_mul]; refine mul_le_mul (bound v) ?_ (norm_nonneg _) (by positivity)
   unfold z r; rw [he,←inner_sub_right,←map_sub, dist_eq_norm]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left ((Uq).pulls ..) (norm_nonneg _))
 simpa using (((tendsto_iff_dist_tendsto_zero.mp ht).const_mul ‖x‖).const_mul (2*m))
variable (P:(Lore K T x)^2∈ Coupon.Population S Γ)(Q:Forward S)
include Q P
lemma wet_progress : Tendsto (fun v:Γ=> ((kP v)^2).re) ν (𝓝 (m^2)):=by
 let r₀:=(T.crew i)
 let z:Γ→ℝ := fun v=> ((kP v)^2).re
 let t(v:Γ):=(cc v)^2
 let L0(g: ℝ≥0):= ((inner ℂ x (K.E g x))^2).re
 have ht: Continuous L0:= Complex.continuous_re.comp (((continuous_const.inner (K.continuousE x)).pow 2))
 let F(v:Γ):= L0 (Real.toNNReal ((τ v+(τ v):Γ):ℝ)); let G(v:Γ):= L0 (Rt v)
 have he : L0 0=m^2:=by unfold L0; rw [K.eZero,ContinuousLinearMap.id_apply,inner_self_eq_norm_sq_to_K]; push_cast; norm_cast
 have LF: Tendsto F ν (𝓝 (m^2)):=by rw [←he]; exact (ht.continuousAt.tendsto).comp τ₀
 have Ly: Tendsto G ν (𝓝 (m^2)):=by rw [←he]; exact ht.continuousAt.tendsto.comp true_time
 let Y(v:Γ):= (t v).re-z v
 have L3:Tendsto Y ν (𝓝 0):=by unfold Y t z; exact (Complex.continuous_re.continuousAt.tendsto.comp (τ_dry K T i x Z))|>.congr (fun k=> Complex.sub_re ..) -- tune arguments order
 let k(v):= (F v - m^2+2*G v)/2-Y v
 apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g:=k) (h:=fun _:Γ=>m^2) (_: Tendsto k ν _) tendsto_const_nhds ?_ ?_
 · change Tendsto k ν (𝓝 (m^2)); convert (((((LF.sub_const _).add (Ly.const_mul _)).div_const 2)).sub L3) using 1; ring_nf -- type underscores?
 · intro v; have h:= bill_safe S i v (τ v) (p₀ v) (true_norm v).ge Q _ P
   unfold meterBill at h; simp only [Pi.pow_apply, source K T i,AddSubgroup.coe_zero,Real.toNNReal_zero] at h -- tune simp source C vs A etc
   change 2*(F v-(t v).re)-(L0 0-2* G v+F v)≤ 0 at h
   change k v≤z v; unfold k Y; rw [he] at h; linarith
 · intro v; refine le_trans (Complex.re_le_norm _) ?_; rw[norm_pow]; refine pow_le_pow_left₀ (norm_nonneg _) ?_ _; rw [pow_two]; exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left ((Uq).pulls ..) (norm_nonneg _))

end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.wet_progress
