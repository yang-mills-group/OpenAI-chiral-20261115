import YM.SU5.Reconstruction.PilotLight.Composition
/-! strong composable ports! In fact PAYMENT in OPERATOR norm with padding kept fixed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(C:Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "Ω₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "Θ"=> doorstep Y H V G.history G.clipped j false C χ
local notation "F"=> osValue Y H V G j C χ
local notation "Os"=> OSvector Y H V G j C χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false C χ
local notation "Ps"=> Follows Y H V G j C χ
local notation "Uₚ" => charted Y H V G j C χ
local notation "Sp" => splice Y H V G j C χ
variable (s t w: marks (timeMesh Λ))(A B:(indoor Y H V G.history G.clipped j false C χ).Op)
-- `(s,t)=(core, lamp)`; d−(s+t)>0 includes all gaps and all trailing. full Θ.
local notation "E₀" a:max=> ((L).E (Real.toNNReal (a:ℝ)))
lemma recombine (p:placement Λ)(h:(s:ℝ)≤(p j:ℝ))(q:0≤(t:ℝ))(e:(p j:ℝ)+(t:ℝ)≤(w:ℝ)): Sp p w s t A ((L).E (Real.toNNReal (t:ℝ)))= A * (L).E (Real.toNNReal ((w:ℝ)-(s:ℝ))) := by
 let W:=w-(p j+t: Gt); let u:=((p j)-s:Gt); let v:= (eject j w-(p+eject j t)); unfold splice
 rw [ensemble, ensemble, Pi.sub_apply p, eject_at]
 have hv(i:Trans j): v i.val=(-p) i.val:= by unfold v; simp [i.property]
 have hA(i:Trans j): (p-eject j s) i.val=p i.val:= by simp [i.property]
 change A *((E₀ u) * Uₚ _)*(E₀ t)*((L).E ((v j:ℝ).toNNReal) * Uₚ v)=_
 rw [show v j=W from by unfold v W; simp, chart_away Y H V G j C χ v _ hv, chart_away Y H V G j C χ (p-eject j s) _ hA]
 have ht:(E₀ u)*(E₀ t)*(E₀ W)=E₀ ((w:ℝ)-(s:ℝ)):=by
    let a:ℝ≥0:=Real.toNNReal (u:ℝ); let b:ℝ≥0:=Real.toNNReal (t:ℝ); let k:ℝ≥0:= Real.toNNReal (W:ℝ)
    have ha:0≤(u:ℝ):= sub_nonneg.mpr h; have hk:0≤(W:ℝ):= sub_nonneg.mpr e
    have Ht: ((a+b)+k)=Real.toNNReal ((w:ℝ)-(s:ℝ)):=by
       unfold a b k; rw [← Real.toNNReal_add ha q,←Real.toNNReal_add (add_nonneg ha q) hk]; apply congrArg
       change ((p j:ℝ)-(s:ℝ)+(t:ℝ))+ ((w:ℝ)-((p j:ℝ)+(t:ℝ)))=(w:ℝ)-(s:ℝ); abel
    rw [show (E₀ u)*(E₀ t) = (L).E (a+b) from ((L).time ..).symm, ←Ht]; exact ((L).time ..).symm
 calc
    A * (_ * Uₚ p) * (E₀ t) * _ = A * (E₀ u)* (Uₚ p*(E₀ t)*(E₀ W))*Uₚ (-p):= by rw [mul_assoc]; simp only [mul_assoc] -- possible composition defeq
    _= _:= by rw [ (concert_heat Y H V G j C χ _ p).eq,mul_assoc (E₀ t),(concert_heat Y H V G j C χ _ p).eq,←ht]; simp only [mul_assoc,concert_one,mul_one]
lemma earnInterest (p:placement Λ)(h:(s:ℝ)≤(p j:ℝ))(q:0≤(t:ℝ))(e:(p j:ℝ)+(t:ℝ)≤(w:ℝ)) (r:ℝ) (u:‖B+E₀ t‖ ≤ r) : ‖Sp p w s t A B + A*(L).E (Real.toNNReal ((w:ℝ)-(s:ℝ)))‖ ≤ ‖A‖ *r:= by
 rw [← recombine Y H V G j C χ s t w A p h q e, show (Sp p w s t A B)+_=Sp p w s t A (B+(E₀ t)) from (by unfold splice; rw [mul_add,add_mul])]; exact le_trans (splicing ..) (mul_le_mul_of_nonneg_left u (norm_nonneg _))
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.earnInterest
