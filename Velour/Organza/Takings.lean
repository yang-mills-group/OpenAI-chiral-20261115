import Velour.Organza.Shuttling
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

local notation "R" => S.gauze
local notation "D" => S.muslin
local notation "B" => S.weight

open Boundary Probe

def rise (T:H.Op) : ℕ→ Test4 →L[ℂ] H.Op
 | 0=>S.rasp T
 | n+1=>
    let x:=rise T n
    x+((ContinuousLinearMap.mul ℂ H.Op).flip R).comp (x.comp (shuttle a))
termination_by structural u=>u

@[simp] lemma rise_zero (T:H.Op): S.rise T 0=S.rasp T:= rfl
lemma rise_step (T:H.Op)(f:Test4)(n:ℕ):
 S.rise T (n+1) f=S.rise T n f + S.rise T n (shuttle a f) * R:= rfl

lemma rises (T:H.Op)(f:Test4)(n:ℕ):
 S.rasp T f * R^n = R^n * S.rise T n f:=by
 induction n generalizing f with
 | zero=> simp
 | succ n h=>
    rw [pow_succ' R n, rise_step,←mul_assoc,S.shuttles,mul_assoc,mul_assoc,add_mul,h]
    rw [mul_assoc (S.rasp T (shuttle a f)),←pow_succ', pow_succ,← mul_assoc (S.rasp T _), h,mul_assoc,←mul_add]


lemma sealed_rasp (T:H.Op)(f:Test4):S.Sealed (S.rasp T f):= fun n=> ⟨_, S.rises T f n⟩

def labelled (T:H.Op): Test4 →ₗ[ℂ] Module.End ℂ D where
 toFun f:= S.label _ (S.sealed_rasp T f)
 map_add' f g:= by
   ext1 v; apply Subtype.ext; change S.rasp _ (f+g) v.val=_; rw [map_add]; rfl
 map_smul' c f:=by
   ext1 v; apply Subtype.ext; change S.rasp _ (c•f) v.val=_; rw [map_smul]; rfl
lemma labelled_coe (T:H.Op)(f:Test4)(v:D):
 (S.labelled T f v).val=S.rasp T f v.val:=rfl

lemma labelled_refines (T:H.Op)(f:Test4)(n:ℕ):
 S.Refines (S.labelled T f) 0 n (S.rise T n f):=
 S.label_refines _ (S.sealed_rasp T f) _ _ (S.rises ..)
lemma labelled_faces (T:H.Op)(f:Test4):
 S.Faces (S.labelled T f) (S.labelled (star T) (bar f)):= by
   intro x y; rw [labelled_coe,labelled_coe,←rasp_star]; symm
   exact ContinuousLinearMap.adjoint_inner_right ..


/-- Graph bound, cost continuous in test. -/
def tender (a:Axis): ℕ→Test4→ℝ
 | 0=> L₁
 | n+1=>fun f=>tender a n f + tender a n (shuttle a f)
lemma tender_nonneg (n:ℕ)(f:Test4): 0≤tender a n f:=by
 induction n generalizing f with
 | zero=> exact L₁_nonneg _
 | succ n h=>exact add_nonneg (h _) (h _)
lemma tender_cont (n:ℕ): Continuous (tender a n):=by
 induction n with
 | zero=> exact L₁_cont
 | succ n h=> exact h.add (h.comp (shuttle a).continuous)

lemma rise_bill (T:H.Op)(n:ℕ)(f:Test4):
 ‖S.rise T n f‖ ≤ tender a n f * ‖T‖:=by
 induction n generalizing f with
 | zero=>exact S.rasp_bill ..
 | succ n h=>
    rw [rise_step, tender,add_mul]
    exact (norm_add_le ..).trans (add_le_add (h _)
      (le_trans (norm_mul_le ..)
       ((mul_le_of_le_one_right (norm_nonneg _) S.gauze_norm).trans (h _))))
#print axioms labelled_refines

