import YM.SU5.Reconstruction.AllGrades.Passage
import YM.SU5.Reconstruction.UVPrice.Temper
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice.Session
open Function Set Filter MeasureTheory Spectral Analysis InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket Roy
variable {W : Hilbert} {a: Axis}(K:OS.Semigroup W a)(h:Forward K)
lemma skyPulse(t:ℝ≥0): cue K * K.E t = cue K:= by
 apply Registers.single (((toe_pays K).times (costT K t)).agrees (toe_pays K).price ?_) (toe_pays K); intro x; filter_upwards with i
 by_cases p:i∈ toe a
 · change _*_= (toe a).indicator (1:E4→ℂ) i; rw [indicator_of_mem p]; simp [Pi.mul_apply,favor, (show i a=0 from p),indicator_of_mem p] -- tune
 simp [p]
include h
lemma frostedSpace (s: Cross a) : K.U s * cue K= cue K:=by
 apply Registers.single (((costU K s).times (toe_pays K)).agrees (toe_pays K).price ?_) (toe_pays K)
 intro x; filter_upwards [forward_ae K x h] with i y; by_cases p: i∈ toe a; swap;· simp [p]
 have ht: i=0:=by
    let k:= SEP a i; have he:(SEP a i).val=i:= by change i-i a • basis a=i; rw [show i a=0 from p,zero_smul,sub_zero]
    have hr: ‖SEP a i‖ ≤ 0 := (show ‖_‖≤ i a from y).trans (show i a=0 from p).le; rw [← he, show SEP a i=0 from norm_le_zero_iff.mp hr]; rfl
 -- turn all $x\in Ground$ . operator norm.
 rw [Pi.mul_apply,indicator_of_mem p,ht]; simp [plane]
lemma clock_frost (s:ℕ→ℝ≥0)(t:ℕ→Cross a)(x:W)(p:Tendsto s atTop atTop) : Tendsto (fun i=> K.E (s i) (K.U (t i) x)) atTop (𝓝 (cue K x)):=by
 rw [tendsto_iff_norm_sub_tendsto_zero]; have h₁(i:ℕ): ‖K.E (s i) (K.U (t i) x) -cue K x‖ = ‖K.E (s i) x-cue K x‖:= by
    rw [show K.E (s i) (K.U (t i) x)=K.U (t i) (K.E (s i) x) from DFunLike.congr_fun (K.independent _ _) x]; nth_rw 1 [← show K.U (t i) (cue K x)=cue K x from DFunLike.congr_fun (frostedSpace K h _) x]
    rw [←map_sub,K.unitary]
 simp_rw [h₁]; exact tendsto_iff_norm_sub_tendsto_zero.mp ((truth K x).comp p)
end YM.ConePrice.Session
#print axioms YM.ConePrice.Session.skyPulse
#print axioms YM.ConePrice.Session.clock_frost
