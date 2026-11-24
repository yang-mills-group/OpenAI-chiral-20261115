import GaugeFieldConstruction.DawnMatrixN
import GaugeFieldConstruction.InvictVUV
/-!
 # Six energy carriers = true Hilbert positive combos not vacuum artifact.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice.curvΝ
open YM.Boundary
open MeasureTheory Set Filter Function Mink Spectral Complex Finset
open scoped Topology BigOperators InnerProductSpace Matrix
abbrev SΝΨ:= ClanZN→ℂ
lemma normShipsVU (x:SΝΨ)(p:x≠0): let r:ℂ:= (↑‖x‖:ℂ)⁻¹; ‖r • x‖=1:=by
 have h:‖x‖≠0:=norm_ne_zero_iff.mpr p; intro r; rw[norm_smul]; simp[r,h]
lemma HankMeasureVU {Y: SettingZN}(q:SΝΨ)(p:ℂ):Formsν Y (p • q)= (starRingEnd ℂ p * p) * Formsν Y q:=by
 unfold Formsν; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _; simp_rw [Pi.smul_apply,smul_eq_mul,map_mul]; ring
variable {H:Hilbert}
lemma FormsΛVU {X T:ClanZN→H}(w:SΝΨ):let x:= ∑ i:ClanZN,w i • X i; let y:=∑ i:ClanZN, w i • T i; Formsν (fun i j=> inner ℂ (X i) (T j)) w=inner ℂ x y:=by
 dsimp only; rw[sum_inner]; simp_rw [inner_sum]; unfold Formsν; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i _; rw[inner_smul_left,inner_smul_right,mul_assoc]
lemma ArchiteXΛVU {X T:ClanZN→H}{p:ℝ}(h:0<p)(v:(fun i j=>inner ℂ (X i) (T j))∈ PrecisionYN p)(c:SΝΨ)(u:c≠0): Formsν (fun i j=>inner ℂ (X i) (T j)) c≠0 :=by
 let r:ℂ:= (↑‖c‖:ℂ)⁻¹; intro hp
 have ht:p<(Formsν _ (r • c)).re:= v _ (normShipsVU c u); rw[HankMeasureVU c r,hp,mul_zero,zero_re] at ht; linarith -- tune
lemma ArchiteΛVU {X T:ClanZN→H}{p:ℝ}(h:0<p)(v:(fun i j=>inner ℂ (X i) (T j))∈ PrecisionYN p) : LinearIndependent ℂ X ∧ LinearIndependent ℂ T:=by
 constructor; rotate_left
 all_goals
   apply Fintype.linearIndependent_iff.mpr; intro w pw i; by_contra e
   have he:w≠0:=fun u=> e (congrFun u i)
   have ht:= ArchiteXΛVU h v w he; rw[FormsΛVU,pw] at ht; simp at ht
#print axioms ArchiteΛVU
end YM.GaugeFieldConstruction.Invoice.curvΝ
end
