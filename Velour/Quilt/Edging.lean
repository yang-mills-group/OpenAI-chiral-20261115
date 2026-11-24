import Velour.Tassel.Jewel
import Velour.Quilt.Shell
import YM.SU5.Same.TemperPrism
/-!
# Heating the sides of a mesh difference, *after* cancellation
-/
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.Velour
open Function Filter TopologicalSpace Metric Set Complex
open scoped NNReal Topology 
open OS.Semigroup SatinJets
variable {H : Hilbert}{j : Axis} (S : OS.Semigroup H j) {a d:ℝ≥0}

lemma mesh_form: mesh_diff S d * S.E a=(duration d)⁻¹ • (S.E (a+d) - S.E a):= by
 rw [add_comm, S.time]; unfold mesh_diff; rw [smul_mul_assoc,sub_mul,one_mul]; rfl
variable {L:Type*}{f:Filter L}{t:L→ℝ≥0}
private lemma diff_conv (p:Tendsto t f (𝓝 0))(q:∀ᶠ i in f, 0< t i)(A:0<a):
    Tendsto (fun i=> mesh_diff S (t i) * S.E a) f (𝓝 (deriv S.F (duration a))):=by
 have h: Tendsto (fun i=> duration (t i)) f (𝓝[≠] 0):= by
   apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
   · simpa using! (continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.comp p
   filter_upwards [q] with i e
   intro hv; exact lt_irrefl (0:ℝ) (show (0:ℂ)∈inside from (show duration (t i)=0 from hv) ▸ (dur.mpr e))
 refine ((S.localHeat _ (dur.mpr A)).differentiableAt.hasDerivAt.tendsto_slope_zero.comp h).congr' ?_
 filter_upwards [q] with i hi
 rw [mesh_form]; change (duration _)⁻¹ • (S.F _- S.F _) = _
 rw [show duration a+duration (t i)=duration (a+t i) by simp [duration],
     roots_heat _ A, roots_heat _ (add_pos A hi)]


variable (τ:ℕ→ℝ)(c:ℕ→ℝ≥0)
local notation "E" t:max => S.E (Real.toNNReal t)
-- for the limit write the extra slot as real
def repay (t:ℝ):H.Op:=deriv S.F (t/4:ℝ)
def shell (t:ℝ)(i:ℕ): H.Op:= mesh_diff S (c i) * E (t/4)
-- heat difference * constant (t/4)
def piping (X:ℝ→H.Op)(t:ℝ):H.Op:=
 let u:=X (t-t/4)
 repay S t * u * E (t/4) - E (t/4)*u * repay S t
def quilt (V:ℝ→ℕ→H.Op)(t:ℝ)(i:ℕ):H.Op:=
   shell S c t i * V t i * E (t/4) - E (t/4) * V t i * shell S c t i


lemma repay_le (t:ℝ)(p:0<t) :
    ‖repay S t‖<9/t:=by
 have h:0<t/4:=by positivity
 have e:1/(t/4/2)=8/t:=by ring
 exact ((CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.deriv_heat_cost
     S (t/4:ℝ) h).trans_eq e).trans_lt ((div_lt_div_iff_of_pos_right p).mpr (by norm_num))

variable (p:Tendsto c atTop (𝓝 0))(g:∀i,0<c i)
include p g
lemma edging (t:ℝ)(z:0<t) : Tendsto (shell S c t) atTop (𝓝 (repay S t)):=by
 have h:0<t/4:=by positivity
 have hp:= Real.toNNReal_pos.mpr h
 have e:=diff_conv S p (Eventually.of_forall g) hp
 have a:duration ((t/4).toNNReal)=(↑(t/4:ℝ):ℂ):=congrArg (Complex.ofReal) (Real.coe_toNNReal (t/4) h.le)
 rw [a] at e; exact e
lemma edgingPays {L:ℝ}(y:∀k,0<τ k)(r:1≤L)(f:∀k,L^k*τ k=τ 0):
   Pays H τ (shell S c) (repay S):=by
 refine ⟨fun d x=> Gleams.tightly (edging S c p g d x),
      max (9/τ 0) 1,L,le_max_right ..,r,
      Eventually.of_forall fun k=> (((edging S c p g (τ k) (y k)).norm.eventually_le_const
         (repay_le S (τ k) (y k)))).mono fun i u=>u.trans ?_⟩

 have e:0<L^k:=pow_pos (zero_lt_one.trans_le r) _
 suffices 9/τ k=9/τ 0 * L^k from this.le.trans (mul_le_mul_of_nonneg_right (le_max_left ..) e.le)
 have ht:=y k; rw [←f k]; field_simp

lemma pipingPays {L:ℝ}(y:∀k,0<τ k)(r:1≤L)(f:∀k,L^k*τ k=τ 0)
    {V:ℝ→ℕ→H.Op}{X:ℝ→H.Op}(e:Pays H τ V (fun t=> X (t-t/4))):
    Pays H τ (quilt S c V) (piping S X):=by
 have h:=edgingPays S τ c p g y r f
 have w:= Pays.one (τ:=τ) (fun t=>E (t/4)) (fun _=>S.shrinks _)
 exact ((h.mul e).mul w).sub ((w.mul e).mul h)


omit p g
lemma quilt_turned
    (V:ℝ→ℕ→H.Op)(t:ℝ)(i:ℕ)(h:0<t):
   quilt S c V t i=(duration (c i))⁻¹ •
      (S.pad (t/4 + c i) (t/4) (V t i)-S.pad (t/4) (t/4 + c i) (V t i)):=by
 have h':0<t/4:=by positivity
 unfold quilt shell
 rw [pad_val,pad_val,Real.toNNReal_add h'.le (c i).coe_nonneg,Real.toNNReal_coe,
     mesh_form, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,
     ←smul_sub,sub_mul,sub_mul,mul_sub]
 abel

-- algebra for whole tuba stencil
def trims (W:Prism) (X:ℝ→H.Op)(t:ℝ): H.Op:=
   ∑ i∈W.support,W i • ((piping S)^[i+1] X) t
lemma piping_agree {X Y:ℝ→H.Op} (e:∀t:ℝ,0<t→X t=Y t)(n:ℕ):
   ∀t:ℝ,0<t→((piping S)^[n] X) t=((piping S)^[n] Y) t:=by
 induction n with
 | zero=> exact e
 | succ n ih=>
   intro t w
   simp only [Function.iterate_succ_apply',piping,ih (t-t/4) (by linarith)]
lemma trims_agree {X Y:ℝ→H.Op}(e:∀t:ℝ,0<t→X t=Y t)(W:Prism):
    ∀t:ℝ,0<t→ trims S W X t=trims S W Y t:=by
 intro t h

 unfold trims; refine Finset.sum_congr rfl fun i _=>?_
 rw [piping_agree S e (i+1) t h]

end YM.Velour
