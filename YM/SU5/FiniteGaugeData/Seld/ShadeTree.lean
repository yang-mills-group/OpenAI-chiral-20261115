import YM.SU5.FiniteGaugeData.Seld.Draw
import YM.SU5.FiniteGaugeData.Seld.Mercans
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
open Function Filter Metric Complex Set MeasureTheory Lattice Mist Celeritas Land OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) {H:Hilbert} {a:Axis}
namespace Breve
variable (a b:Axis)(L A B R:Shrine K) (m n:ℕ) (o y x z:E4)(t:ℝ)
local notation "S" u:max=> sites_r o (jeer a y u) x z
local notation "Θ"=> choice4 L A B R
local notation "I" i:max o:max t:max=> orbit_on W i o t
local notation "J"=> Ω b
local notation "Y"=> W b
local notation "ι"=> parabola (W b)
local notation "η"=> Par (W b)
local notation "d"=> OS.Semigroup.duration
local notation "Γ" x:max=> coast W b (week m n) (Θ) x
variable (e:b≠a) (P': Cinema (W b))
local notation "uL"=> prefixT W b L A m o x
local notation "Lv"=> star (uL) J
local notation "Rv"=>orbit_on W b z R (Ω b)
-- b budget exact requirements.Height.Ye.
variable (s δ:ℝ≥0)(U:Set (Shrine K)) (H': Modicum W Ω a b U) (D: Tableau W L A B R m n U) (p:Line2 a L A B R o o x z) (o0:o a=0)(v₁:0<s)(v₂:0<δ)
variable (g:Boundary.Test4) (q:∀ y∈tsupport g, |y a|<(s:ℝ)∧ WaveK b L A B R o y x z (s+δ))
local notation "xv"=> soup W Ω a L true x
local notation "xw"=> soup W Ω a R false z
abbrev shadow(i:ℕ):= g y*(foreA W Ω a L A B R m n o y x z (squirt i)-rearA W Ω a L A B R m n o y x z (squirt i))
local notation "s₀"=> scope W Ω a b L A B R m n o (pz a y) x z e P' s
include P' e H' D v₁ v₂ p o0 q
local notation "Go"=> upto W Ω b L A B R m n o x z δ
local notation "f" x':max => shadow W Ω a L A B R m n o x' x z g
-- support wave function. give ∀ i bound incl q_t displacements.
lemma cape : Tendsto (shadow W Ω a L A B R m n o y x z g) atTop (𝓝 0) ∧ ∀ i:ℕ, ‖(f y) i‖ ≤ ‖g y‖*(Go+Go):=by
 by_cases yy:g y=0; · refine ⟨tendsto_const_nhds.congr (fun b=>by simp [shadow,yy]),fun i=>by simp [yy,shadow]⟩
 obtain ⟨q,k⟩:= q y (subset_closure yy); have pz': WaveK b L A B R o (pz a y) x z (s+δ):=by refine ⟨k.halo,?_,?_⟩; rw [pzb a b y e.symm]; exact k.soil; rw [pzb a b y e.symm]; exact k.wake
 let Θ'(u:ℂ):= s₀ u; let G:=sideways (y a)
 have he(i:ℕ):= foamR W Ω a b L A B R m n o y x z e P' s δ k v₁ v₂ U H' D (show Line2 a L A B R o (pz a y) x z from { p with same_a:=by rw [o0,pza] }) o0 (squirt i) (squirtP i) (tsub_pos_iff_lt.mp (dearthP i)) q
 have hL(i:ℝ): (i:ℂ)+G∈ lanes (s:ℝ):=by change |( (i:ℂ)+sideways _).im|< _; simpa [sideways]
 have H₁: G∈lanes (s:ℝ):= by simpa only [Complex.ofReal_zero,zero_add] using hL 0
 have hT:ContinuousAt Θ' G:= (sprawlA _ _ _ _ _ _ _ _ _ _ _ _ G H₁).continuousAt
 let v(i:ℕ):= d (squirt i); have hv:Tendsto v atTop (𝓝 0):=by
    refine (show d 0=(0:ℂ) from by simp [OS.Semigroup.duration]) ▸ ?_; exact (continuous_ofReal.continuousAt.tendsto.comp (NNReal.continuous_coe.continuousAt.tendsto.comp squirtL)) -- cast maybe ▸ wrong
 have Hh : Tendsto (fun i=> v i+G) atTop (𝓝 G):=by simpa only [zero_add] using hv.add (tendsto_const_nhds (x:=G))
 have Hh':Tendsto (fun i=> -v i+G) atTop (𝓝 G):=by simpa only [neg_zero,zero_add] using hv.neg.add (tendsto_const_nhds (x:=G))
 have hr(i:ℕ): (f y) i = g y*(Θ' (v i+G)-Θ' (-v i+G)):= by unfold shadow; rw [(he i).1,(he i).2]
 constructor
 · apply Tendsto.congr' _ (show Tendsto (fun i=> g y * (Θ' (v i+G)-Θ' (-v i+G))) atTop (𝓝 0) from (by simpa only [comp_apply,sub_self,mul_zero] using ((hT.tendsto.comp Hh).sub (hT.tendsto.comp Hh')).const_mul (g y))); exact Eventually.of_forall fun i=> (hr i).symm
 intro i; let w:ℝ:=↑(squirt i); rw [hr,norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact (norm_sub_le ..).trans (add_le_add (Mornorm W Ω a b L A B R m n o (pz a y) x z e P' s δ pz' v₂ _ (hL w)) (Mornorm W Ω a b L A B R m n o (pz a y) x z e P' s δ pz' v₂ _ (ofReal_neg w ▸ hL (-w))))
set_option maxHeartbeats 380000 in
lemma avail : DotComm (W a) (A.f a) (B.f a) o g m n (flame (W a) 2 zero_lt_two xv) (flame (W a) 2 zero_lt_two xw):= by
 apply flanks; let F(i:ℕ)(y:E4):=(f y) i; have H(i:ℕ) : Integrable (F i):= by unfold F shadow; simp_rw [mul_sub]; exact (fountainP ..).sub (fountainR ..) --b parsing.R?
 have t(y:E4):= cape W Ω a b L A B R m n o y x z e P' s δ U H' D p o0 v₁ v₂ g q; have hb:= fun i:ℕ=> (show ∀ᵐ x∂(volume (α:=E4)),‖F i x‖≤‖g x‖*(Go+Go) from Eventually.of_forall (fun x=> (t x).2 i)) -- shadow x expand caution macro Go
 have hc:= tendsto_integral_of_dominated_convergence (fun x=> ‖g x‖*(Go+Go)) (fun i=>(H i).aestronglyMeasurable) (g.integrable.norm.mul_const _) hb (Eventually.of_forall (fun x:E4=>(show Tendsto (fun n=>F n x) atTop (𝓝 ((fun _=> (0:ℂ)) x)) from (t x).1))); rw [integral_zero] at hc; exact hc
#print axioms cape
#print axioms avail
end Breve
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
