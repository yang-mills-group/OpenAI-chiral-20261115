import YM.SU5.FiniteGaugeData.Seld.Marin
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
local notation "Z"=> HiL b L A B R o y x z
local notation "uL"=> prefixT W b L A m o x
local notation "Lv"=> star (uL) J
local notation "Rv"=>orbit_on W b z R (Ω b)
-- b budget exact requirements.Height.Ye.
variable (s δ:ℝ≥0) (k:WaveK b L A B R o y x z (s+δ)) -- Lean coerces `s+δ` into NN? Wave last ℝ usually coe operands before plus.Numerics.L.
variable (v₁:0<s)(v₂:0<δ)
lemma barry : orbit_on W b y B= coreSp (W b) y (B.f b):=by unfold coreSp optx orbit_on opt; simp only [acts_leg]; rw [map_neg]; rfl
lemma fundsO : ‖orbit_on W b y B‖≤ ‖B.f b‖:=by rw [barry]; exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x=> vcost ..
abbrev upto : ℝ:= slu (Y) (Lv) (Rv) (m+n) n δ (B.f b)
local notation "S0" y:max=> scope W Ω a b L A B R m n o y x z e P' s
local notation "Go"=> upto W Ω b L A B R m n o x z δ
include k v₂
lemma Mornorm(l:ℂ)(t:l∈ lanes ↑s): ‖scope W Ω a b L A B R m n o y x z e P' s l‖ ≤ upto W Ω b L A B R m n o x z δ:= by
 obtain ⟨u,v⟩:=genre b L A B R o y x z s δ k; refine le_trans (abound _ _ _ _ _ P' _ _ _ _ _ _ _ _ t v₂ u v) ?_; unfold upto slu; gcongr; exact fundsO ..
omit k v₂
local notation "∂"=> sideways
local notation "χ"=> (W a)
def pz(q:E4):= (SEP a q).val
lemma pza : pz a y a=0:= (SEP a y).property
lemma pzb (p:a≠b) : pz a y b=y b:= by change (y-y a • basis a) b=y b; simp [basis,p.symm]
lemma zed : coreSp (W a) (pz a y) (B.f a)=coreSp (W a) y (B.f a):= shrike _ _ _ (pza a y)
variable (U:Set (Shrine K)) (H': Modicum W Ω a b U) (D: Tableau W L A B R m n U) (p:Line2 a L A B R o (pz a y) x z) (o0:o a=0)
local notation "xv"=> soup W Ω a L true x
local notation "xw"=> soup W Ω a R false z
abbrev foreA (w:ℝ≥0) :=backE (W a) xv xw 2 (A.f a) (B.f a) o m n (2-w) w y
abbrev rearA (w:ℝ≥0) :=forE (W a) xv xw 2 (A.f a) (B.f a) o m n (2-w) w y
local notation "s₀"=> scope W Ω a b L A B R m n o (pz a y) x z e P' s
include e H' D p o0 k v₁ v₂
lemma foamR (q:ℝ≥0)(u:0<q)(v:q<2)(K₁:|y a|<(s:ℝ)): foreA W Ω a L A B R m n o y x z q = (s₀) ((d q)+ sideways (y a)) ∧ rearA W Ω a L A B R m n o y x z q= (s₀) (-(d q)+ sideways (y a)):=by
 have hc : WaveK b L A B R o (pz a y) x z (s+δ):=by refine ⟨k.halo,?_,?_⟩; rw [pzb a b y e.symm]; exact k.soil; rw [pzb a b y e.symm]; exact k.wake
 -- compute wake argument order see type print
 have h:= wakeA W Ω a b L A B R m n o (pz a y) x z (y a) e P' s δ hc v₁ v₂ U H' D p q u v K₁
 let X:=W a; rw [rpair (W a) ..,vpair (W a) ..] at h <;> try assumption -- try lem.Tune.K.B.
 rw [barry W a A o, barry W a B (pz a y), zed W a B y, shrike (W a) (A.f a) o o0, regain] at h; exact h
#print axioms Mornorm
#print axioms foamR
end Breve
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
