import Merino.JadeEye.Tithe

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

open Dial Brooch
open TreasuryFog Paige Vault
attribute [local instance] loreM loreN
open Roots

open Pressure Py BPress

lemma coinback (L:Side){a:ℝ}(u:0<a):
 ∀ᶠ x:ℝ in atTop, Real.exp (-a*((radiusB x/10:ℕ):ℝ))≤temp x ^2:=by
 let g:=tailω L a 10 u (by decide)
 filter_upwards [(g.vanish 0).eventually (ge_mem_nhds zero_lt_one), draft_π L] with x h z
 have q:0<pinpr L x:=pow_pos z.2.1 _
 have t:0<temp x:=by rw [BPress.temp_eq]; exact mul_pos (BPress.g_pos z.1) (drift_pos x)
 have p:1≤ stemS x:=Real.one_le_rpow (drift_one x) (by norm_num)
 have h := (show hueW L x * Real.exp (-a*((radiusB x/10:ℕ):ℝ)) / pinpr L x ≤1 by simpa using h)
 unfold hueW at h
 rw [div_le_iff₀ q, one_mul,mul_assoc,div_mul_eq_mul_div,div_le_iff₀ (pow_pos t 2)] at h
 have h:=le_of_mul_le_mul_left h q
 exact le_trans (le_mul_of_one_le_left (Real.exp_pos _).le p) h

def cis (S:ℝ)(x:ℝ):= S*(4*(1+ (radiusB x :ℝ)))

lemma costs (S:ℝ):PL (cis S):=
 (PL.const _).mul ((PL.const _).mul ((PL.const _).add PL_radiusX))

def vat (C S b:ℝ)(x:ℝ):=7 * (b + (quota^2*b*C) * (cis S x ^2))*icost
lemma wet (C S b:ℝ) : PL (vat C S b):=
 ((PL.const _).mul ((PL.const _).add ((PL.const _).mul ((costs S).pow 2)))).mul (PL.const _)

lemma levee (S:ℝ): Tendsto (fun x=> temp x * cis S x) atTop (𝓝 0):=
 by simpa using (npl_temp.mul (costs S)).vanish 0


lemma branchX (P:BudgetPoint)(x:ℝ)(C S b:ℝ)(k:P.B=radiusB x)
 (t:P.threshold=temp x)(L:Side)(w:0<pinpr L x)(u:ℝ):
 |u * (pinpr L x/temp x^2)| * outlay P C S (temp x ^2*b) b ≤
    |u * vat C S b x| *pinpr L x:=by
 have y:0<temp x:=t ▸ P.threshold_pos
 have z:outlay P C S (temp x^2*b) b = vat C S b x * (temp x)^2:=by
    unfold outlay lime vat cis
    rw [k,t];ring
 rw [z, abs_mul,abs_mul,abs_of_pos (show 0< pinpr L x / _ by positivity)]
 refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)) w.le)
 field_simp

 exact le_refl _
