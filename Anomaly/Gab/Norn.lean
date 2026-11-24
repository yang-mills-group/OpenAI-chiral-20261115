import Anomaly.Gab.Pithy
-- Election receipts click. supports demanding more L, heights after.Any.L
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open Lattice Wilson RG Lat Tune QuadClock Cube Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] {B:Basis I ℂ E} {m:ℕ}(pκ:SketchA B m) {L:Side}{X Y:BudgetPoint}{H w Q A K C v0 v1 v2 ε T:ℝ}{z:ℂ}
namespace SketchA
variable {P:ArmorK}{u p f:ℝ}
local notation "ι"=> Sum I Unit
-- certificate separated ArtStem.BOTH dims.Rail.Tool.Reg.Haus.Trace
structure ScaleKit (K C v0 v1 v2 A T u f ε:ℝ)(L:Side): Prop where
   earn: pκ.Gain₀ v0 v1 v2 A u T L
   bite : pκ.Bleak L v0 v1 v2 A
   grants: κGain (B:=B) ε T f (|C| * u)
   minkPay :0 < ε
   pays: paceY*|K| * (far_C A * (L.val:ℝ)⁻¹) ≤ ε
   buys : |C| * (far_C A * (L.val:ℝ)⁻¹) ≤ ε
   grip : far_C A * (L.val:ℝ)⁻¹ ≤ u
   tunes : far_C A * |C| * (L.val:ℝ)⁻¹≤ 1/2
   rites :0<u
   rule :0<f
abbrev Next_L (P:Side→Prop):Prop := ∀ᶠ n:ℕ in atTop,∀ L:Side,n≤L.val→ P L
lemma perL (u f:ℝ)(p:0 < f) : Next_L (fun L=> u*(L.val:ℝ)⁻¹≤ f):=by
 obtain ⟨i,w⟩:= exists_nat_gt (u/f); filter_upwards [eventually_ge_atTop i] with n hx L kL
 have h:i≤L.val:=le_trans hx kL; rw [←div_eq_mul_inv,div_le_iff₀ (by positivity)]; exact ((div_le_iff₀ p).mp (le_trans w.le (by exact_mod_cast h))).trans_eq (mul_comm ..)
lemma readyScales (h:0<u)(p:0<f)(t:0<ε)(U: κGain (B:=B) ε T f (|C| * u)) (x:Next_L fun L=> Gain₀ pκ v0 v1 v2 A u T L)(X0:∀ L,Bleak pκ L v0 v1 v2 A) : Next_L (fun L=>ScaleKit pκ K C v0 v1 v2 A T u f ε L):=by
 filter_upwards [perL (paceY*|K| * far_C A) ε t,perL (|C| * far_C A) (min ε (1/2)) (lt_min t (by norm_num)),perL (far_C A) u h,x] with n p' g z V L wL; refine ⟨V _ wL,X0 _,U,t,?_,?_,z _ wL,?_,h,p⟩
 · rw [←mul_assoc]; exact p' _ wL
 · rw [←mul_assoc]; exact (g L wL).trans (min_le_left ..)
 rw [mul_comm (far_C _)]; exact (g L wL).trans (min_le_right ..)
-- Choose constants BEFORE L. For both can require these for any A purchased pre L AFTER. uniform receipts.
abbrev μ₃ := MF+2
abbrev μ₄ := 3*MF+1
lemma mE₀ : 0 ≤ MF:=mul_nonneg (Real.exp_pos _).le hPπ
lemma hitch (v0 v1 v2 C K:ℝ) : ∃ ε T q:ℝ, 0 < ε∧0<T∧0<q ∧∀ A:ℝ,0≤A→ Next_L (fun L=> ScaleKit ιBuild3 K C v0 v1 v2 A T μ₃ q ε L):=by
 obtain ⟨δ,T,η,y,u⟩:= turns_T; have hx:0< μ₃:=add_pos_of_nonneg_of_pos mE₀ (by norm_num)
 obtain ⟨ε,X,U,p,t⟩:= κGold (B:=Bθ) y (mul_nonneg (abs_nonneg C) hx.le)
 refine ⟨ε,T,X,U,y,p,fun A _=> readyScales ιBuild3 hx p U t ?_ ?_⟩
 · filter_upwards [perL (|v1| * far_C A) δ η,perL (far_C A) 1 zero_lt_one] with n V g L x; exact litThree _ u (by rw [←mul_assoc]; exact V _ x) (g _ x)
 exact fun L X Y z H Q w K C u Z F t x p U=> Markup.three_zero u p U
lemma process (P:ArmorK)(C K:ℝ) : ∃ ε T q:ℝ, 0 < ε∧0<T∧0<q ∧∀ A:ℝ,0≤A→ Next_L (fun L=> ScaleKit ιBuild4 K C P.g0 P.g1 P.g2 A T μ₄ q ε L):=by
 have ht:=glints P; obtain ⟨T,δ,u⟩:= ht; let y:= u.pay; have hx:0< μ₄:= add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) mE₀) zero_lt_one
 obtain ⟨ε,X,U,p,t⟩:= κGold (B:=Gior) y (mul_nonneg (abs_nonneg C) hx.le)
 refine ⟨ε,T,X,U,y,p,fun A h=> readyScales ιBuild4 hx p U t ?_ ?_⟩
 · filter_upwards [ht_H P A T δ h u] with n V L x; exact litFour u (V _ x).1 (V _ x).2 -- 
 exact fun L X Y z H Q w K C u Z F t x p U=> Markup.four_zero u p U
end SketchA
end YM.CF.Py
