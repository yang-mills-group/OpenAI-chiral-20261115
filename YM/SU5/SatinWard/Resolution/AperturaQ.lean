import YM.SU5.Assay.Credits
import YM.SU5.SatinWard.Resolution.ImpulseT
import YM.SU5.SatinWard.Resolution.Sandstone
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
-- includes Core.Comparison.`
open OS.Semigroup.Marble
variable (u:Immutable S v)
def Steady (w:H):Prop:=∀ t:ℝ≥0,S.E t w=w
lemma Steady.opaque (x:H)(p:Steady S x) (t:ℝ) : ω t x=x:=p t.toNNReal
lemma hold_color (w:H)(g:Steady S w)(a:ℂ):Steady S (a • w):=by intro t; rw [map_smul,g t]
lemma steady_zero:Steady S 0:=fun t=>map_zero _
lemma Steady.seam (a b:V)(x y:ℝ)(p:Immutable S v) (q:Steady S (quietArm v b)): Marble.seam S v x a b=Marble.seam S v y a b:=by rw [Marble.still_pay S v _ p,Marble.still_pay S v _ p]; rw [Steady.opaque S _ q _, Steady.opaque S _ q _]
lemma steered (u:H)(a:ℝ) : Steady S u→ Steady S (ω a u):=fun q=>by rw [Steady.opaque S u q a]; exact q
lemma recessed (w:H)(x:ℝ)(p:0≤x)(q:Steady S (ω x w)):Steady S w:=by
 intro t; let y:ℝ:= t; have he:0≤y:= t.2; apply wax_alive S x p; rw [show S.E t=ω y from congrArg S.E Real.toNNReal_coe.symm]
 change (ω x * ω y) w=ω x w; rw [S.wax_sq p he, add_comm,← S.wax_sq he p]; exact Steady.opaque S _ q _ -- Bool
include u
lemma ember_launch {F:ℝ→ℝ→H.Op}(q:S.Credits 0 F)(l r s t:ℝ)(hl:0<l)(hr:0<r)(hs:0<s)(ht:0<t)(y:Steady S (quietArm v (F l r))): Steady S (quietArm v (F s t)):=by
 let A:=max l s; let B:=max r t; have he:= q hl hr (le_max_left l s) (le_max_left r t); have hf:= q hs ht (le_max_right l s) (le_max_right r t); have hw: Steady S (quietArm v (F A B)):=by unfold A B; rw [he,Marble.arm_sand S v u]; exact steered S _ _ y
 unfold A B at hw; rw [hf, Marble.arm_sand S v u] at hw; exact recessed S _ _ (sub_nonneg.mpr (le_max_right ..)) hw
end BasinWake
end YM.OS.Semigroup
