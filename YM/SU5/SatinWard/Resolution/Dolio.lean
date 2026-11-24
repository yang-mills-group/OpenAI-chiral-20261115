import YM.SU5.SatinWard.Resolution.Dormosa
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Py.Rate.LocalLimit.Preparation QuadClock ShapeLab SoulField Mezzo Treaty
-- Gather norm. For any linear real charge $L. Consumable unit estimate.Technique via trace dominance & perturbation. Income scalars on all runtime hats, not independent heights. 
lemma view_trace (r:ℕ)(p:0<r) : ∃ C:ℝ,0 < C∧ ∀ (L:Soul→L[ℝ]ℝ),(∀z∈ depth,L z=0)→‖L‖ ≤ C*(|L (coreTrace true r)|+|L (coreTrace false r)|):=by
 let u:=shortTime r; let f(A:Bool): Soul→L[ℝ]ℝ:= ((1/(3*u)) • generation A : Soul→ₗ[ℝ]ℝ).toContinuousLinearMap; let C:=1+‖f true‖+‖f false‖; have hu:0<u:=short_live p; have hp:=norm_nonneg (f true); have hj:=norm_nonneg (f false); refine ⟨C,(by unfold C; positivity),fun L h=>?_⟩
 let s (b:Bool):= L (coreTrace b r); have he:L= s true • (f true)+ s false • (f false):=by
    ext x; let z:=blendRem x; have g: L x= L (reconstructH x):=by let k:= h (x-reconstructH x) z; rw [map_sub] at k; exact sub_eq_zero.mp k
    rw [g,reconstructH,map_add,map_smul,map_smul]; have hx(b:Bool): s b=u*L (genCore b):= L.map_smul u _; simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,hx]; change _/3*L _+_/3*L _= u*L _ *((1/(3*u))* generation true x) + u*L _*((1/(3*u))*generation false x); field_simp <;>ring
 calc
    _ =‖s true • f true+s false • f false‖:=congr_arg norm he
    _ ≤ ‖s true • f true‖+‖s false • f false‖:= norm_add_le ..
    _ ≤ C * (|s true|+|s false|):=by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]; unfold C; nlinarith only [mul_nonneg hp (abs_nonneg (s false)), mul_nonneg hj (abs_nonneg (s true)),abs_nonneg (s true),abs_nonneg (s false)]
-- applies after bounding individually. Use observable error ledger.
theorem accrual (Y:Soul→L[ℝ]ℝ)(T:Bool→Soul)(C E E' K:ℝ) (c:0≤C)(e:0≤E)(v:0≤E')
 (U:Bool→ℂ)(h:0<K)(u:4*C*E ≤ K) (W:Bool→Soul)(u₁:∀ b, ‖W b-T b‖ ≤ E/K) (u₂:∀ b, ‖(↑(Y (W b)):ℂ)-U b‖ ≤ E') (w:‖Y‖ ≤ C *(|Y (T true)|+|Y (T false)|)):
 ‖Y‖ ≤ 2*C*(2*E'+‖U true‖+‖U false‖) ∧∀ b:Bool, ‖(↑(Y (T b)):ℂ)-U b‖ ≤ E'+(2*C*(2*E'+‖U true‖+‖U false‖))*(E/K):=by
 let F(b:Bool):ℂ:= Y (T b); let G:= (2*C*(2*E'+‖U true‖+‖U false‖)); have hp(b:Bool): ‖F b-U b‖ ≤ E'+‖Y‖*(E/K):=by let H:ℂ:= Y (W b); rw [add_comm]; refine (norm_sub_le_norm_sub_add_norm_sub _ H _).trans (add_le_add ?_ (u₂ b)); unfold H F; rw [←Complex.ofReal_sub,Complex.norm_real,←map_sub]; exact (Y.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((norm_sub_rev ..).trans_le (u₁ b)) (norm_nonneg _))
 have hz(b:Bool): |Y (T b)|≤ E'+‖Y‖*(E/K)+‖U b‖:=by
    have h':= (norm_le_norm_sub_add (F b) (U b)).trans (add_le_add_left (hp b) _); unfold F at h'; rw [Complex.norm_real] at h'; exact h'
 have hx: ‖Y‖≤G:=by
    have hx:= w.trans (mul_le_mul_of_nonneg_left (add_le_add (hz true) (hz false)) c); unfold G; have he: C*(E/K)≤ 1/4:=by rw [←mul_div_assoc]; apply (div_le_iff₀ h).mpr; linarith only [u]
    linarith only [hx,mul_le_mul_of_nonneg_left he (norm_nonneg Y)] -- indent tune
 exact ⟨hx,fun a=>(hp a).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hx (div_nonneg e h.le)))⟩
#print axioms accrual
end AuroraX
end YM.CF.LitCurrent
