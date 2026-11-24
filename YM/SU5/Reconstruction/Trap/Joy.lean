import YM.SU5.Reconstruction.Trap.Clasp
/-!
# The Trap crossing for light ray. Mellin yields covariance in this non-Lorentz-yet phase.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp
variable {K H D:Hilbert} {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
namespace Clasp
variable (C:Clasp K H D) (L:X→ℝ)(h:Measurable L)(p:∀ x,0≤L x) (M:Y→ℝ)(b:Measurable M)(q:∀ y,0≤ M y)
   (e:ℝ)(t:e=1∨e=-1) (P : PVM H X)(Q : PVM D Y)
local notation "A"=> sail e
local notation "B"=> sail (-e)
local notation "F" z=> order P (slopeRay (sail e) L z)
local notation "N" z=> order Q (slopeRay (sail (-e)) M z)
variable (c:∀ x:ℝ,0<x→ Pass C (order P (slopeRay (sail e) L x)) (order Q (slopeRay (sail (-e)) M x)))
include b q h p c
-- arbit unit along eig rays; unequal incomes as costs cross i
lemma passJoy (u i): C.Pass (introT P L (sail e) u i) (introT Q M (sail (-e)) u i) := by
 refine C.passIntegral (tunable P L h p A (by simp) u i) (tunable Q M b q B (by simp) u i) ?_
 filter_upwards [ae_restrict_mem measurableSet_Icc] with u' y
 have d : 0<u':= pagePos i y; have v:∀ᶠ a:ℝ in 𝓝[>] u',0<a:= mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds d)
 exact (C.derivPass _ _ ((bill P L h p A _ (realRay A (by simp) _ d)).differentiableAt) ((bill Q M b q B _ (realRay B (by simp) _ d)).differentiableAt) (v.mono fun i w=> c _ w)).scale _
local notation "R" u=> starry P L u
local notation "S" u=> starry Q M u
include t
lemma North (u:ℝ): Pass C (starry P L u) ((wages e u:ℂ) • starry Q M u):= by
 have hu:= C.passLimit atTop (a:= reward u A • starry P L u) (b:= reward u B • starry Q M u) (sot P L h p A (by simp) u) (sot Q M b q B (by simp) u) (Eventually.of_forall (passJoy C L h p M b q e P Q c u))
 have hz:=hu.scale (reward u A)⁻¹
 rw [smul_smul,inv_mul_cancel₀ (reward_ne u A),one_smul, sails u _ t,smul_smul,mul_left_comm,inv_mul_cancel₀ (reward_ne u A),mul_one] at hz; exact hz
lemma Noon : C.Pass (P.region (onboard L)) (Q.region (onboard M)):= by simpa only [wages,mul_zero,zero_div,Real.exp_zero,Complex.ofReal_one,one_smul,star_zero P L h, star_zero Q M b] using North C L h p M b q e t P Q c 0
end Clasp
end YM.CrossedFrame
