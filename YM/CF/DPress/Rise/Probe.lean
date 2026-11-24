import YM.CF.DPress.Rise.Flame
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open LinQ Cad Mercer Room Push.AbsoluteSums Larch Ione Trees Py Wray Kay DPress.Fees DPress.Analytic Moral
open scoped YM.CF.Mew
namespace Flight
variable {t w ε a b L:ℝ}(u:1<L)
def keep(L:ℝ)(z:ℂ):ℂ:= if z∈ ank L then z else 0
lemma keeping {z:ℂ}(p:z∈ank L):keep L z=z:=if_pos p
include u
lemma goes(z:ℂ):keep L z ∈ank L:=by unfold keep; split; assumption; exact planeZero u -- tune namespace
lemma one:keep L 1=1:=keeping (planeOne u)
lemma zero:keep L 0=0:=keeping (planeZero u)
omit u
lemma keep_s : Holo (ank L) (keep L):= DifferentiableOn.congr (f:=id) differentiableOn_id fun _ p=>keeping p
lemma keep_n (z:ℂ)(u:1<L): ‖keep L z‖<L:=by have hp:=goes u z; simpa only [DPress.Analytic.ank,mem_ball, dist_zero_right] using hp
variable (V U:Θq t)
abbrev hΔ:ℝ:= ‖V.val-U.val‖/t -- note first arg V = NEW
abbrev θ₁(q:ℂ):Θ:= U.val+q.re • (V.val-U.val)
abbrev θ₂(q:ℂ):Θ:= q.im • (V.val-U.val)
abbrev debt(V U:Θq t)(ε:ℝ):= ε+hΔ V U
abbrev wideS(V U:Θq t)(ε:ℝ):= 1+ (debt V U ε)⁻¹ -- $R. via keep
variable (ht:0<t) (w0:0≤ ε) (φ:0 < debt V U ε)
include ht
lemma balance : hΔ V U*t=‖V.val-U.val‖:= div_mul_cancel₀ _ ht.ne'
lemma nn : 0≤ hΔ V U:= div_nonneg (norm_nonneg _) ht.le
lemma duty : hΔ V U≤2:= ((div_le_iff₀ ht).mpr (((norm_sub_le ..).trans (add_le_add V.property U.property)).trans_eq (by ring)))
omit ht in
include φ in
lemma starV : 1 < wideS V U ε:= lt_add_of_pos_right _ (inv_pos.mpr φ)
include w0 φ
lemma expense (q:ℂ)(p:‖q‖ ≤ wideS V U ε): ‖q‖ * hΔ V U ≤ 3:=by
 let h:=hΔ V U; let v:= debt V U ε; have he: ‖q‖ *h≤h+v⁻¹*h:= (mul_le_mul_of_nonneg_right p (nn V U ht)).trans_eq (by unfold wideS v; ring); apply he.trans; have hp:v⁻¹*h≤1:= (inv_mul_le_iff₀ φ).mpr (by unfold debt; rw [mul_one]; linarith); linarith only [hp,duty V U ht]
lemma forkR (q:ℂ)(p:‖q‖ ≤ wideS V U ε): ‖θ₁ V U q‖ ≤5*t∧ ‖θ₂ V U q‖ ≤ 5*t:=by
 let d:= ‖V.val-U.val‖; have hp: ‖q‖*d ≤ 3*t:= by unfold d; rw [← balance V U ht,←mul_assoc]; exact mul_le_mul_of_nonneg_right (expense V U ht w0 φ q p) ht.le
 have hz:‖q.re • (V.val-U.val)‖≤ 3*t:=by rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm q) (norm_nonneg _)).trans hp
 have he:‖q.im • (V.val-U.val)‖≤3*t:=by rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm q) (norm_nonneg _)).trans hp
 have hr:‖θ₁ V U q‖≤t+3*t:= (norm_add_le ..).trans (add_le_add U.property hz); exact ⟨hr.trans (by linarith), he.trans (by linarith)⟩
omit w0 φ ht
abbrev se(Q:Θ)(p:‖Q‖ ≤5*t):Θq t:= ⟨(5:ℝ)⁻¹ • Q,by rw [norm_smul,Real.norm_of_nonneg (by norm_num), inv_mul_le_iff₀ (by norm_num :0<(5:ℝ))]; exact p⟩
-- combination generic over ℝ vectors with ℂ extension
variable {D:Type*}[AddCommGroup D][Module ℂ D][Module ℝ D][IsScalarTower ℝ ℂ D](F:Θ →ₗ[ℝ] D)(z:ℂ)
abbrev vista (V B:D)(z:ℂ):=B+z • (V-B) -- implicit Module
lemma flameV (v:‖θ₁ V U z‖ ≤5*t)(u:‖θ₂ V U z‖ ≤5*t) : vista (F V.val) (F U.val) z=(5:ℂ) • F (se _ v).val+ (5*Complex.I) • F (se _ u).val:=by
 unfold vista; change _=(5:ℂ) • F ((5:ℝ)⁻¹ • θ₁ V U z)+ (5*Complex.I) • F ((5:ℝ)⁻¹ • θ₂ V U z); simp only [map_smul,θ₁,θ₂,map_add,map_sub]; simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ), RCLike.ofReal_inv, RCLike.ofReal_ofNat]; rw [smul_smul (5:ℂ),smul_smul (5*Complex.I),mul_inv_cancel₀ (by norm_num : (5:ℂ)≠0),show 5*Complex.I* (5:ℂ)⁻¹=Complex.I from by field_simp,one_smul, smul_smul,add_assoc,←add_smul]; change _= F U.val+ ((z.re:ℂ)+Complex.I*z.im) • _; rw [show (z.re:ℂ)+Complex.I*z.im=z from by rw [mul_comm,Complex.re_add_im]] -- name ofReal_ofNat
end Flight
end YM.CF.Sour.Heath
