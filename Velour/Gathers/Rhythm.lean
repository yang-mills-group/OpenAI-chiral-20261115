import Velour.Gathers.Broderie
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Velour Boundary Probe
local notation "R"=> S.gauze
local notation "E"=> S.E
local notation "B"=> S.weight
local notation "G"=> S.heatL
local notation "D"=> S.muslin

abbrev wrapW (m:ℕ)(X:H.Op):= R^m * X * R^m

lemma hatch_given (m:ℕ)(X:H.Op)(f:Test4):
    S.hatch (S.wrapW m X) m f = S.labelled X f:=by
 rw [hatch_eq]
 ext1 v; apply Subtype.ext
 apply S.gauze_power_inj m
 change (R^m) (B m _).val = (R^m) ((S.labelled X f) v).val
 rw [weight_cancel,labelled_coe,labelled_coe]
 have s (b):Commute (S.unit.translation b) (R^m):=(S.unit_weight b).pow_right _
 unfold wrapW
 rw [S.rasp_more_right _ _ s,S.rasp_more_left _ _ s,mul_apply_eq_comp,
       weight_cancel,mul_apply_eq_comp]


lemma surges_hatch {q:ℕ→H.Op}{v:H.Op}(e:Gleams H q v){F:ℕ→Test4}
       {f:Test4}(h:Tendsto F atTop (𝓝 f))(m:ℕ):
    S.Surges atTop (fun i=>S.hatch (q i) m (F i)) (S.hatch v m f):=by
 let g:=S.surges_width e h
 have c: S.Surges atTop (fun _:ℕ=>B m) (B m):=
    Surges.idle fun n=>⟨m,_,S.weight_refines m n⟩
 exact (c.mul g).mul c

-- pad through G, need general surges_warm
lemma swinging_heat {p:ℕ→ℝ≥0}{d:ℝ≥0}(g:Tendsto p atTop (𝓝 d)):
    S.Surges atTop (fun i=>G (p i)) (G d):=by
 intro v w e n
 have h (t:ℝ≥0)(z:D): (B n (G t z)).val=E t (B n z).val:=
    by rw [S.heat_weight,S.heatL_coe]
 simp_rw [h]
 exact (Gleams.warm S g).both (e n)


variable {S} {m:ℕ}{X:H.Op}{Q:ℝ≥0→H.Op}{Y:ℕ→H.Op}{A:ℝ}
variable {T:S.Detector}

namespace Ribs

lemma refines (h:S.Ribs Y Q m A X)(i n:ℕ)(f:Test4):
    S.Refines (S.labelled (Y i) f) (m+m) n
       (S.rise (S.wrapW m (Y i)) (m+n) f) ∧
    ‖S.rise (S.wrapW m (Y i)) (m+n) f‖≤ tender a (m+n) f * A:= by
  rw [← S.hatch_given m]
  have g:=S.hatch_refines (S.wrapW m (Y i)) m n f
  refine ⟨g,(S.rise_bill ..).trans (mul_le_mul_of_nonneg_left (h.spent i) ?_)⟩
  exact tender_nonneg ..


lemma exacts (h:S.Ribs Y Q m A X)(t:S.Instates Q T):
    T=S.hatch X m:= t.common (S.hatch_welcome h.prepaid) (EventuallyEq.rfl)

lemma limit_refines (h:S.Ribs Y Q m A X)(t:S.Instates Q T)(n:ℕ)(f:Test4):
    S.Refines (T f) (m+m) n (S.rise X (m+n) f) ∧
    ‖S.rise X (m+n) f‖≤ tender a (m+n) f * A :=
  ⟨h.exacts t ▸ S.hatch_refines X m n f,
   (S.rise_bill ..).trans (mul_le_mul_of_nonneg_left h.limit (tender_nonneg ..))⟩

variable {j:ℕ→ℕ}{F:ℕ→Test4}{f:Test4}
lemma rushes (h:S.Ribs Y Q m A X)(t:S.Instates Q T)
   (k:Tendsto j atTop atTop)(e:Tendsto F atTop (𝓝 f)):
   S.Surges atTop (fun i=>S.labelled (Y (j i)) (F i)) (T f):=by
 rw [h.exacts t]
 refine (S.surges_hatch (h.rattle.glints k) e m).consent (Eventually.of_forall ?_)
 exact fun i=> S.hatch_given ..


lemma rushes_warm (h:S.Ribs Y Q m A X)(t:S.Instates Q T)
   (k:Tendsto j atTop atTop)(e:Tendsto F atTop (𝓝 f))
   {p q:ℕ→ℝ≥0}{l r:ℝ≥0}
   (a': Tendsto p atTop (𝓝 l))(b': Tendsto q atTop (𝓝 r)):
   S.Surges atTop (fun i=> S.labelled (E (p i) * Y (j i) * E (q i)) (F i))
      (G l * T f * G r):= by
 simp_rw [S.heat_right_label,S.heat_left_label]
 exact ((S.swinging_heat a').mul (h.rushes t k e)).mul (S.swinging_heat b')
end Ribs

variable (S) {L:Module.End ℂ S.muslin}
variable {t:H.Op}

-- heat add-on cost
lemma frosted_price {n k:ℕ}(p q:ℝ≥0)(u:S.Refines L k n t):
    S.Refines (G p * L * G q) k n (E p * t * E q) ∧
    ‖E p * t * E q‖≤‖t‖:=by
 have w:S.Refines (G p*L) k n (E p * t) := by
    rw [←zero_add n] at u
    simpa using (S.heatL_refines p n).mul u
 refine ⟨by simpa using w.mul (S.heatL_refines q (k+n)), ?_⟩


 refine ((norm_mul_le ..).trans
    (mul_le_of_le_one_right (norm_nonneg _) (S.shrinks _))).trans ?_
 exact (norm_mul_le ..).trans
    (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))
#print axioms Ribs.rushes_warm
