import Merino.JadeEye.Lent
import Merino.JadeEye.Blank

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

open Dial BProof Brooch
open TreasuryFog Paige Vault
attribute [local instance] loreM loreN
open Roots

section
open Window Buffered
variable {n:Side}
variable (K:Scree.Loom n)(P:BudgetPoint)(y:Spool n)(s:Sweep n)(z:ℝ)
def highZ : Evaluation n := Bide.move s⁻¹ ((z:ℂ) • y.scalar K P)
abbrev extra := ((actB s).xor (actR s)).xor s.charge

lemma shine {d a b:ℝ} (t:y.Hem K P a b d)(V:Pane n):
 highZ K P y s z V =
 (z:ℂ) • pearl P (boxA s y.post) K (julStep s y.color) (extra s) V • 1:=by
 let S:=actSpin s
 have e(b r:Bool):tourP S b r 1=1:=by
    cases r
    · change twist _ (windX _ 1)=1;rw [win_i,map_one]
    change theta _ (windX _ 1)=1;rw [win_i,theta_one]
 change tourP S (actB s) (actR s) ((z:ℂ) • traceCost K P y.post y.color (flashA s⁻¹⁻¹ V) • 1)=_
 rw [sew_scale,sew_scale,e]
 rw [show cSignX ((actB s).xor (actR s)) z=z from (by
    cases ((actB s).xor (actR s))<;>simp [cSignX])]
 unfold traceCost pearl

 rw [inv_inv,← mask_move s t.skylight t.sign t.sip V,ech,singT,trace_twist,win_trace]
 unfold traceCost extra
 cases (actB s) ^^ (actR s) <;> cases s.charge <;> simp [cSignX]



end

variable {G B L:Side}{j:ℕ}{jY:Odd L.val}{Yk:Pricing j L jY (Thread j)}{d:ℝ}
variable {U:Grasp Yk B d}{R:GramM (mid G B)}{K:Scree.Loom (mid G B)}
variable {a b v r C e S c h:ℝ}{q:ℕ}
local notation "N"=>mid G B
variable {o:Site (mid G B)}{y:Spool (mid G B)}

def outlay (P:BudgetPoint)(C S Δ b:ℝ):ℝ:=
 7 * (Δ+quota^2*b*C*lime P S^2) * icost

lemma credit (z:ℝ)(s:Sweep (mid G B))(p:Potion R.p N e v r C S)(t:y.Hem K R.p a b e)(w:0≤b)
   (wide:12≤R.p.B)(g:24*y.stepY≤R.p.B)
   (ord:R.p.order=6)(ρ:inReach R.p o s y)
   {Δ:ℝ}(l: cap0 y.color ≤ Δ)
   (fee:|z| * outlay R.p C S Δ b ≤ c):
 ∃ V T, Office U R K q h c c o (highZ K R.p y s z) V T:=by
 refine gives (streak p t.skylight (trunk_move t.sip s) t.sign (mul_nonneg (sq_nonneg _) w) (extra s)
      o ρ wide ord) z
      (Bide.mode_p (outAllowed s (allowedX (t.scalar.scale z))) (touches _ _ g wide ρ)) (shine _ _ _ _ _ t) ?_


 rw [Complex.norm_real,Real.norm_eq_abs]
 unfold wage
 apply le_trans _ fee
 apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
 refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_left ((move0 s _).le.trans l) _) (by norm_num)) icos_pos.le

