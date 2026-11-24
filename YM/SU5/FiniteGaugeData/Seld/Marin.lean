import YM.SU5.FiniteGaugeData.Seld.Altitude
import YM.SU5.FiniteGaugeData.Seld.FrameR
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
local notation "τ" z:max=> (z:ℝ)
include k
lemma genre : δ≤ (Z 1 2)-s ∧ δ ≤ (Z 2 3)-s:=by
 -- cp gap.CoeNN. show s+δ≤...
 have he (p q:FHorizon)(h:(s:ℝ)+(δ:ℝ)≤ startX Θ (sites_r o y x z) b q-endX Θ (sites_r o y x z) b p):δ ≤ Z p q-s:=by
    have hz:s+δ≤ Z p q:= by apply NNReal.coe_le_coe.mp; rw [NNReal.coe_add]; exact h.trans (Real.le_coe_toNNReal _)
    exact le_tsub_of_add_le_right (by rwa [add_comm]) -- orientation
 exact ⟨he 1 2 k.soil, he 2 3 k.wake⟩
variable (U:Set (Shrine K)) (h₁:A∈Magic W U m) -- syntax Magic W U m is Set, f as fn prop.Warning
structure Modicum(U:Set (Shrine K)):Prop where
 biz : Philos (σ:=FHorizon) W Ω a b U
 cover : saucer (W a) (Ω a)=Ω a
 leave : saucer (W b) (Ω b)=Ω b
structure Tableau(ν: Set (Shrine K)):Prop where
 left : L∈ν
 right : R∈ν
 front : A∈ Magic W ν m
 back : B∈ Magic W ν n
variable (H': Modicum W Ω a b U) (D: Tableau W L A B R m n U) (p:Line2 a L A B R o y x z)
local notation "Θb"=> orbit_on W a o A
local notation "Ξb"=> orbit_on W a y B
local notation "xv"=>soup W Ω a L true x
local notation "xw"=>soup W Ω a R false z
local notation "S0"=>scope W Ω a b L A B R m n o y x z e P' s
include p H' D v₁ k v₂
lemma wakeA (w:ℝ≥0)(p':0<w)(v:w<2)(L':|t|<(s:ℝ)):
 backwards (W a) (xv) (xw) Θb Ξb m n ((d w)+ sideways t)= S0 ((d w)+ sideways t) ∧ forwards (W a) (xv) (xw) Θb Ξb m n ((d w)+sideways (-t))= S0 (-(d w)+sideways t):=by
 have h : ∀ i:FHorizon, Θ i∈ Magic W U (week m n i):=by
    intro i; fin_cases i; exact magic0 W U L D.left; exact D.front; exact D.back; exact magic0 W U R D.right
 have v_ : 0<(s:ℝ)+(δ:ℝ):= add_pos (show (0:ℝ)<↑s from v₁) (show (0:ℝ)<↑δ from v₂)
 have he(u:ℝ)(l:List FHorizon)(p':l.Perm porder)(q:l.Pairwise (Seers Θ (S u) a)):chalk W Ω a (week m n) Θ (S u) l=S0 u:=by
    obtain ⟨ys,yr⟩:=genre b L A B R o y x z s δ k; -- y shadows! replace
    rw [bright W Ω a b L A B R m n o y x z u e P' s v₁ (tsub_pos_iff_lt.mp (v₂.trans_le ys)) (tsub_pos_iff_lt.mp (v₂.trans_le yr))]; exact Cords W Ω a b l _ Θ _ U H'.biz H'.cover H'.leave h porder p' (p'.nodup_iff.mpr (by decide)) q (stare a b L A B R o y x z (s+δ) v_ k e u)
 refine rills (W a) xv xw t s Θb Ξb m n (S0) (fun z p=> sprawlA _ _ _ _ _ _ _ _ _ _ _ _ z p) v₁ ?_ ?_ w p' v L' -- missing hyp
 · intro i r v; exact (act_p W Ω a L A B R m n o y x z i p r v).symm.trans (he i porder (.refl _) (turf a L A B R o y x z i p r v).1)
 intro i r v; rw [← ofReal_neg]; exact (act_r W Ω a L A B R m n o y x z i p r v).symm.trans (he (-i) rorder (List.Perm.cons 0 (List.Perm.swap ..)) ((turf a L A B R o y x z i p r v).2))
#print axioms wakeA
end Breve
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
