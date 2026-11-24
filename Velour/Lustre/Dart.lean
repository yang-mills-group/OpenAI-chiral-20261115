import Velour.Quilt.Edging
import Velour.Organza.Larva
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

open Boundary Probe
open YM.Velour
local notation "R" => S.gauze
local notation "C" => S.rasp
local notation "E" => S.E
local notation "E'" t:max => deriv S.F ↑((t):ℝ)

lemma dart (u:ℝ≥0)(p:0<u): HasDerivAt (fun y:ℝ=> E y.toNNReal) (E' u) (u:ℝ):=by
    have k := (S.localHeat _ (dur.mpr p)).differentiableAt.hasDerivAt.scomp (u:ℝ) (hasDerivAt_id' (u:ℝ)).ofReal_comp
    rw [ofReal_one, one_smul] at k
    refine k.congr_of_eventuallyEq ?_
    exact (eventually_gt_nhds (show 0<(u:ℝ) from p)).mono fun y hy=> by
     change S.E _= S.F _
     rw [← S.roots_heat (Real.toNNReal_pos.mpr hy),duration,Real.coe_toNNReal _ hy.le]

lemma dart_gauze(t:ℝ≥0)(p:0<t): R * E' t=E t * R - E t:=by
 rw [← S.deriv_gauze _ p]
 let k:=S.dart _ p
 exact (k.const_mul R).unique ((k.mul_const R).congr_of_eventuallyEq (Eventually.of_forall fun y=> (S.gauze_heated _).eq.symm))


lemma gauze_cancel (T X:H.Op)(h:R * T * R=R * X * R): T=X:=by
 obtain ⟨Y,p⟩:=S.heat_weighted 1 zero_lt_one
 have j:E 1=R * star Y:=by rw [←S.gauze_star,←star_mul,←p];exact (S.sym _).symm
 refine S.equal_heat (d:=1) ?_
 conv => lhs; lhs; lhs; rw [p]
 conv => rhs; lhs; lhs; rw [p]
 rw [j]
 simpa only [mul_assoc] using congrArg (fun t:H.Op=>Y*t*star Y) h

def train (t:ℝ≥0) (X:H.Op): H.Op := E' t * X * E t - E t * X * E' t
lemma train_down (X:H.Op)(t:ℝ≥0)(p:0<t):
 R * S.train t X * R = R * (E t * X * E t) - (E t * X * E t) * R:=by
 unfold train
 rw [mul_sub, ←mul_assoc,←mul_assoc,S.dart_gauze _ p,sub_mul,sub_mul,sub_mul]
 have h:=S.deriv_gauze t p
 conv_lhs=>rhs; rw [mul_assoc,mul_assoc,mul_assoc,h]
 conv_lhs=>lhs; lhs;lhs;lhs;lhs;rw [(S.gauze_heated t).eq]
 simp only [sub_mul,mul_sub,mul_assoc]
 abel


lemma rasp_train (t:ℝ≥0)(p:0<t)(X:H.Op)(f:Test4):
 C (S.train t X) f=C (E t * X * E t) (-(shuttle a f)):=by
 have h(Y:H.Op)(g:Test4):C (R * Y * R) g=R * C Y g * R:=by rw [S.rasp_more_right _ _ S.unit_weight,S.rasp_more_left _ _ S.unit_weight]
 refine S.gauze_cancel _ _ ?_
 rw [←h,S.train_down _ _ p, S.rasp_cutoff,_root_.sub_apply,
   S.rasp_more_left _ _ S.unit_weight,S.rasp_more_right _ _ S.unit_weight]
 conv_lhs=>rhs;rw [S.shuttles]
 rw [map_neg,mul_neg,neg_mul,mul_add,mul_assoc]; abel


def bead (a:Axis)(n:ℕ)(f:Test4) : Test4:= (fun x=>-(shuttle a x))^[n] f
lemma hem_bead (n:ℕ)(f:Test4): tsupport (bead a n f) ⊆ tsupport f:=by
 induction n with
 | zero=> exact le_refl _
 | succ n ih=>
    refine subset_trans ?_ ih
    rw [bead, Function.iterate_succ_apply']
    let v:=bead a n f
    change tsupport (fun b=> -(I • tick a v b))⊆tsupport v
    exact (le_of_eq (tsupport_neg (fun b=> I • tick a v b))).trans
        ((tsupport_smul_subset_right (fun _=>I) _).trans
         (SchwartzMap.tsupport_lineDerivOp_subset (basis a) v))
open SatinJets
def fringed (a:Axis)(W:Prism) (c:ℂ)(f:Test4):Test4:=
 ∑ i∈W.support, (c * W i) • bead a (i+1) f


lemma fringed_hem (W:Prism)(c:ℂ)(f:Test4): tsupport (fringed a W c f) ⊆ tsupport f:=by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x h; by_contra q
  let L:Test4→ₗ[ℂ]ℂ:= {toFun:= fun g=>g x,map_add':=by intros;rfl,map_smul':=by intros;rfl}
  apply h
  change L _=0
  rw [fringed,map_sum]
  refine Finset.sum_eq_zero fun i _=>?_
  rw [map_smul]
  have y:L (bead a (i+1) f)=0:=image_eq_zero_of_notMem_tsupport (x:=x) (f:=bead a (i+1) f) (mt (@hem_bead a (i+1) f x) q)
  rw [y,smul_zero]

def raspOp (f:Test4): H.Op→ₗ[ℂ] H.Op where
 toFun x:= C x f
 map_smul' c x:= by rw [rasp_lever]; rfl
 map_add' x y:= by
    have q:=S.rasp_cutoff (x+y) y
    rw [add_sub_cancel_right] at q
    rw [q,_root_.sub_apply,sub_add_cancel]

#print axioms fringed_hem
end YM.OS.Semigroup
