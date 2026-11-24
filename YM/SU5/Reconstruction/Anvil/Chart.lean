import YM.SU5.Reconstruction.Anvil.Rays
/-! # Anvil's cost for the reconstructed field positions (variants of CP3
 seam with two spatial arms or possibly three). Interpolates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Filter Metric InnerProductSpace OS Semigroup
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators Classical
variable {H H':Hilbert} (a:Axis)
local notation "χ" => onlyTime a
-- next δ constants; use real values including when moving away from marks
structure Price where
  margin : ℝ
  first : ℝ
  firstWidth : ℝ
  second : ℝ
  secondWidth : ℝ
variable {ι:Type*}
namespace Price
variable (Q : Price)(y:Bool)
def entry : Wage→Wage := if y then fun _=> χ ((Q.first+Q.margin:ℝ):ℂ) else fun z=> z+χ ((Q.second+Q.margin:ℝ):ℂ)
def compare : Wage→Wage:= if y then fun z=> z+χ ((Q.second-(Q.first+Q.firstWidth):ℝ):ℂ) else fun z=> χ ((Q.first-(Q.second+ Q.secondWidth):ℝ):ℂ)-z
def leaves : Wage→Wage:= if y then fun z=> χ ((Q.margin-(Q.second+Q.secondWidth):ℝ):ℂ)-z else fun _=> χ ((Q.margin-(Q.first+Q.firstWidth):ℝ):ℂ)
def permeates (z:Wage):Prop:= Q.entry a y z∈ Tunnel a ∧ Q.compare a y z∈ Tunnel a ∧ Q.leaves a y z∈ Tunnel a
-- physical gap real pricing during motion
lemma commuter (x:Wage): Q.compare a y x∈ Tunnel a ↔ ‖rimPay a (Deeper x)‖ < if y then (x a).re +(Q.second-(Q.first+Q.firstWidth)) else Q.first-(Q.second+Q.secondWidth)-(x a).re:= by cases y<;>simp [compare,Tunnel,only_agree,onlyTime,deeper_add]
-- helpers continuity & hol
@[fun_prop] lemma entryCont : Continuous (Q.entry a y):= by cases y<;>simp only [entry, reduceCtorEq, if_true,if_false]<;>fun_prop
@[fun_prop] lemma compareCont : Continuous (Q.compare a y):= by cases y<;>simp only [compare, reduceCtorEq, if_true,if_false]<;>fun_prop
@[fun_prop] lemma leavesCont : Continuous (Q.leaves a y):= by cases y<;>simp only [leaves, reduceCtorEq, if_true,if_false]<;>fun_prop
lemma permeates_open : IsOpen {z| Q.permeates a y z}:= ( (tunnel_open a).preimage (Q.entryCont a y)).inter (((tunnel_open a).preimage (Q.compareCont a y)).inter ((tunnel_open a).preimage (Q.leavesCont a y)))
lemma entryD (D:Set ℂ)(z:ℂ→Wage)(e:∀ i,DifferentiableOn ℂ (fun t=> z t i) D)(i:Axis) : DifferentiableOn ℂ (fun t=> Q.entry a y (z t) i) D:=by cases y<;>simp only [entry, reduceCtorEq, if_true,if_false,Pi.add_apply]<;> fun_prop
lemma compareD (D:Set ℂ)(z:ℂ→Wage)(e:∀ i,DifferentiableOn ℂ (fun t=> z t i) D)(i:Axis) : DifferentiableOn ℂ (fun t=> Q.compare a y (z t) i) D:=by cases y<;>simp only [compare,reduceCtorEq, if_true,if_false,Pi.add_apply,Pi.sub_apply]<;> fun_prop
lemma leavesD (D:Set ℂ)(z:ℂ→Wage)(e:∀ i,DifferentiableOn ℂ (fun t=> z t i) D)(i:Axis) : DifferentiableOn ℂ (fun t=> Q.leaves a y (z t) i) D:=by cases y<;>simp only [leaves, reduceCtorEq, if_true,if_false,Pi.sub_apply]<;> fun_prop
-- operator prices. perm
variable {a} (S:OS.Semigroup H a) (A B:H.Op)(L R:H)
abbrev takeAB (x:Bool)(a b:ι) := if x then a else b
def sale (z:Wage):ℂ:= inner ℂ L (PaysOn S (Q.entry a y z) (takeAB y A B (PaysOn S (Q.compare a y z) (takeAB y B A (PaysOn S (Q.leaves a y z) R)))))
variable {x:Wage}(t:Q.permeates a y x)
-- local notation "F"=> sale Q y S A B L R -- order check
include t
lemma saleCont : ContinuousAt (Q.sale y S A B L R) x:= by
 let e:= (Q.permeates_open a y).mem_nhds t; exact ((tendsto_const_nhds (x:=L)).inner (keepRight S (𝓝 x) t.1.le (Q.entry a y) ((show ∀ᶠ i in 𝓝 x,Q.permeates a y i from e).mono (fun _ v=> v.1.le)) (Q.entryCont a y|>.continuousAt) _ _ ((takeAB y A B).continuous.continuousAt.tendsto.comp (keepRight S (𝓝 x) t.2.1.le (Q.compare a y) ((show ∀ᶠ i in 𝓝 x,Q.permeates a y i from e).mono (fun _ v=> v.2.1.le)) (Q.compareCont a y|>.continuousAt) _ _ ((takeAB y B A).continuous.continuousAt.tendsto.comp (keepRight S (𝓝 x) t.2.2.le (Q.leaves a y) ((show ∀ᶠ i in 𝓝 x,Q.permeates a y i from e).mono (fun _ v=> v.2.2.le)) (Q.leavesCont a y|>.continuousAt) (fun _=>R) R tendsto_const_nhds))))))
lemma tariff {c d:ℝ}(p:‖A‖ ≤ c)(e:‖B‖≤d): ‖Q.sale y S A B L R x‖ ≤ ‖L‖*c*d*‖R‖:= by
 let X:=takeAB y A B; let Y:= takeAB y B A; unfold sale
 have h₀(F:H.Op)(p:‖F‖ ≤1)(z:H): ‖F z‖ ≤‖z‖:= (F.le_opNorm _).trans ((mul_le_mul_of_nonneg_right p (norm_nonneg _)).trans_eq (one_mul _))
 have g(T:H.Op)(W:H.Op)(k:H) (Z:H.Op)(q:‖Z‖≤1) (U:H.Op)(w:‖U‖ ≤1): ‖T (Z (W (U k)))‖ ≤ ‖T‖*(‖W‖*‖k‖):= by
    refine (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((h₀ _ q _).trans ((W.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h₀ _ w _) (norm_nonneg _)))) (norm_nonneg _))
 refine (norm_inner_le_norm ..).trans (le_trans (mul_le_mul_of_nonneg_left ((h₀ _ (francs S _ t.1.le) _).trans (g X Y R _ (francs S _ t.2.1.le) _ (francs S _ t.2.2.le))) (norm_nonneg _)) ?_)
 rw [← mul_assoc ‖X‖, ← mul_assoc, ← mul_assoc]
 have u0:= (norm_nonneg A).trans p; have e0:= (norm_nonneg B).trans e; cases y; swap; · change ‖L‖*‖A‖*‖B‖*‖R‖ ≤ _; gcongr -- tune
 change ‖L‖ * ‖B‖*‖A‖ *‖R‖ ≤ _; rw [mul_right_comm ‖L‖]; gcongr
omit t
lemma saleHol (D:Set ℂ)(z:ℂ→Wage)(e:∀ i,DifferentiableOn ℂ (fun t=> z t i) D)(h:IsOpen D)(v:∀ t∈D, Q.permeates a y (z t)): AnalyticOnNhd ℂ (fun t:ℂ=> Q.sale y S A B L R (z t)) D := by
 apply DifferentiableOn.analyticOnNhd ?_ h; unfold sale; intro t w
 have A₁:= marchHol S h (fun x u=>(v x u).1.le) (Q.entryD a y D z e); have A₂:= marchHol S h (fun x u=> (v x u).2.1.le) (Q.compareD a y D z e); have A₃:= marchHol S h (fun x u=> (v x u).2.2.le) (Q.leavesD a y D z e)
 -- linear maps
 apply DifferentiableAt.differentiableWithinAt; let f:ℂ→H:=fun r=> PaysOn S (Q.leaves a y (z r)) R
 exact ( (innerSL ℂ L).differentiableAt).comp _ ((A₁.differentiableAt (h.mem_nhds w)).clm_apply ((takeAB y A B).differentiableAt.comp _ ((A₂.differentiableAt (h.mem_nhds w)).clm_apply ((takeAB y B A).differentiableAt.comp _ ((A₃.differentiableAt (h.mem_nhds w)).clm_apply (differentiableAt_const R))))))
end Price
end YM.Anvil
