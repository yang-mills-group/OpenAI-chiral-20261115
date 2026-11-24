import Velour.Organza.Boning
import Velour.Organza.Takings
import Velour.Organza.Surges
/-!
# Detector existence. Includes precise test estimates.

See Larva for consequences, in particular word unpadding.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe
local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

local notation "E" => S.E
local notation "G" => S.heatL


abbrev Detector : Type := Test4 →ₗ[ℂ] Module.End ℂ S.muslin

/-- Operator-valued distribution, with controlled input weights costing
output powers plus a fixed loss. -/
def Touchable (T:S.Detector): Prop:=
 ∃k:ℕ, ∀ n, ∃ W:Test4 →L[ℂ] H.Op, ∀ f, S.Refines (T f) k n (W f)

/-- Registration of Minkowski local detector with the complete positive
slab prices. Also a sheet of boundary values. This condition is designed
to propagate to arbitrary finite words on the common domain. -/
structure Instates (Q : ℝ≥0→H.Op) (T:S.Detector): Prop where
 touch : S.Touchable T
 guard (f:Test4)(t:ℝ≥0)(u:0<t):
   S.labelled (Q t) f = G t * T f * G t

def hatch (X:H.Op)(m:ℕ):S.Detector where
  toFun f:= (B m) * (S.labelled X f) * (B m)
  map_add' f g:=by rw [map_add, mul_add,add_mul]
  map_smul' c f:=by rw [map_smul,mul_smul_comm,smul_mul_assoc]; rfl


lemma hatch_eq (X:H.Op)(m:ℕ)(f:Test4):
  S.hatch X m f = (B m)*(S.labelled X f)*(B m):= rfl

lemma hatch_refines (X:H.Op)(m n:ℕ)(f:Test4):
 S.Refines (S.hatch X m f) (m+m) n (S.rise X (m+n) f):= by
  rw [hatch_eq]
  have t: S.Refines (B m*S.labelled X f) m n (S.rise X (m+n) f):= by
    simpa using (S.weight_refines m n).mul (S.labelled_refines X f (m+n))
  simpa using t.mul (S.weight_refines m (m+n))

lemma hatch_touch (X:H.Op)(m:ℕ): S.Touchable (S.hatch X m):=
 ⟨m+m, fun n=>⟨_,S.hatch_refines X m n⟩⟩ -- placeholder for CLM?

lemma hatch_bill (X:H.Op)(m n:ℕ)(f:Test4)(v:D):
 ‖B n (S.hatch X m f v)‖ ≤ tender a (m+n) f * ‖X‖ * ‖B ((m+m)+n) v‖:=
 ((S.hatch_refines X m n f).bill _).trans (mul_le_mul_of_nonneg_right (S.rise_bill ..) (norm_nonneg _))

variable {X:H.Op}
lemma heat_weight (t:ℝ≥0)(m:ℕ)(v:D):
  B m (G t v)=G t (B m v):= by
    apply Subtype.ext; rw [S.heatL_coe]
    simpa only [zero_add] using S.heatL_refines t m v



lemma hatch_welcome {Q: ℝ≥0→H.Op}{m:ℕ}
 (h:S.Prepaid Q m X): S.Instates Q (S.hatch X m):= by
 refine ⟨S.hatch_touch ..,fun f d t=> ?_⟩
 have u: R^m * S.rasp (Q d) f * R^m =
    E d * S.rasp X f * E d := by
     have k(b):Commute (S.unit.translation b) (R^m):=(S.unit_weight b).pow_right m
     rw [← S.rasp_more_left _ _ k,← S.rasp_more_right _ _ k, h d t,
         S.rasp_more_right _ _ (fun b=>S.unit_heat b d),
         S.rasp_more_left _ _ (fun b=>S.unit_heat b d)]
 ext1 x
 rw [hatch_eq]
 apply Subtype.ext
 change (S.labelled _ f x).val=(G d (B m (S.labelled X f (B m (G d x))))).val
 rw [← S.heat_weight, S.heat_weight d m x]
 apply S.gauze_power_inj m
 rw [weight_cancel,heatL_coe,labelled_coe,labelled_coe,heatL_coe]
 have z:=congrArg (fun Y:H.Op=>Y (B m x).val) u
 rwa [mul_apply_eq_comp,weight_cancel,mul_apply_eq_comp,mul_apply_eq_comp, mul_apply_eq_comp] at z


theorem hatchery {Q:ℝ≥0→H.Op}(p:S.Cashable Q):
 ∃T, S.Instates Q T:= by
 obtain ⟨m,Z,q⟩:= S.cashed p
 exact ⟨_, S.hatch_welcome q⟩

noncomputable def seated {Q:ℝ≥0→H.Op}(p:S.Cashable Q): S.Detector:=
 Classical.choose (S.hatchery p)

lemma seated_in {Q:ℝ≥0→H.Op}(p:S.Cashable Q):S.Instates Q (S.seated p):=
 Classical.choose_spec (S.hatchery p)

#print YM.OS.Semigroup.Instates
#print axioms seated_in
#print axioms hatch_bill

