import SatinThinRegister
import YM.CF.Roots.Cane
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/- Side^4 bookkeeping throughout. Gap speed pays an additional LARGE CONSTANT per step.
   This variant doesn't use L^(9/2). -/
def zoomC (L:Side):ℝ:=64*(L.val:ℝ)^4
def zoomM (L:Side):ℝ:=512*(L.val:ℝ)^4
lemma zoomM_p (L:Side): 0<zoomM L:=by unfold zoomM; positivity
lemma zoomC_p (L:Side): 1 ≤ zoomC L:=by
 have h:1≤ (L.val:ℝ):=by exact_mod_cast L.property
 unfold zoomC; linarith only [one_le_pow₀ h (n:=4)]

structure ChoiceCost (W VZ A:ℝ)(L:Side): Prop where
 root: 1≤ A
 arch:100000* |W| ≤ A
 limb: (A+4)≤ (L.val:ℝ)
 mean: 1024 * |VZ| * (A+4)≤ (L.val:ℝ)
lemma choose_cost (W VZ A:ℝ)(t:1 ≤ A)(r:100000*|W| ≤ A): ∀ᶠ n:ℕ in atTop, ∀ L:Side,n≤L.val→ChoiceCost W VZ A L:=by
 filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (A+4),tendsto_natCast_atTop_atTop.eventually_ge_atTop (1024*|VZ| *(A+4))] with n a b L h using ⟨t,r,le_trans a (Nat.cast_le.mpr h),le_trans b (Nat.cast_le.mpr h)⟩
variable {P Y:BudgetPoint}{L: Side}{T x b h t q W VZ VX VY A:ℝ}
local notation "qC"=> Tune.qCorset P.threshold Y.threshold (L.val:ℝ)
variable (hp:ChoiceCost W VZ A L)(hq:0<q)(w:Real.exp (-1)≤ |t|) (v:|t| ≤ Real.exp 1)
lemma peg_ub (v: |t| ≤ Real.exp 1): |t|≤ 3:= v.trans Real.exp_one_lt_three.le
lemma peg_lb (v:Real.exp (-1) ≤ |t|): 1/3 ≤ |t|:= by
 refine le_trans ?_ v; rw [Real.exp_neg]; rw [one_div]; exact inv_anti₀ (Real.exp_pos _) Real.exp_one_lt_three.le
lemma choice_slot (a:ℝ): ‖(PointSk a).1‖=|a|:=by simp [PointSk, norm_smul, slotNorm, Real.norm_eq_abs]
lemma choice_mint : κprobe mintR L h (A*q) T (t:ℂ) (PointSk x) = ((L.val:ℝ)⁻¹)^4*(|t| *|x|) + ((L.val:ℝ)⁻¹)^5*(A*q)+T:=by simp [κprobe,mintR,norm_smul,Real.norm_eq_abs,PointSk,slotNorm, Complex.norm_real]
lemma choice_nax : κprobe naxR L h (A*q) T (t:ℂ) (PointSk x) = ((L.val:ℝ)⁻¹)^5*(|t| *|x|+A*q)+T:=by simp [κprobe,naxR,Real.norm_eq_abs,PointSk,norm_smul,slotNorm,Complex.norm_real]
private lemma choice_next {T c:ℝ}(_g:0 ≤ c)(p: T≤ (L.val:ℝ)*c): ((L.val:ℝ)⁻¹)^5 * T ≤ ((L.val:ℝ)⁻¹)^4 *c:= (mul_le_mul_of_nonneg_left p (by positivity)).trans_eq (by field_simp) -- ring tune
variable (f:|T|≤ ((L.val:ℝ)⁻¹)^5*q) (u: |x|≤ q)
include hp v f hq u
lemma mint_cost : W*κprobe mintR L h (A*q) T (t:ℂ) (PointSk x) ≤ 4*|W| *((L.val:ℝ)⁻¹)^4*q:=by
 have hx: |t| *|x| ≤ 3*q:=mul_le_mul (peg_ub v) u (abs_nonneg x) (by norm_num)
 let a:= (L.val:ℝ)⁻¹; have ha:0≤a:=by unfold a; positivity
 have hA:0 ≤ A:=zero_le_one.trans hp.root; rw [choice_mint]; refine (le_abs_self _).trans ?_; rw [abs_mul]; change |W| *|a^4*(|t| *|x|)+a^5*(A*q)+T|≤ _; calc
    _ ≤ |W| *(4*a^4*q):=by
       refine mul_le_mul_of_nonneg_left ((abs_add_le ..).trans ?_) (abs_nonneg _); rw [abs_of_nonneg (by positivity:a^4*(|t| *|x|)+a^5*(A*q)≥0)]
       have hk:=mul_le_mul_of_nonneg_left hx (pow_nonneg ha 4)
       have ht:a^5*((A+1)*q) ≤ a^4*q:= choice_next hq.le ((by exact mul_le_mul_of_nonneg_right ((by linarith only [hp.limb])) hq.le))
       change |T|≤a^5*q at f; linarith only [hk,f,ht]
    _ = _:=by dsimp only [a]; ring
lemma nax_cost : VZ*κprobe naxR L h (A*q) T (t:ℂ) (PointSk x)≤((L.val:ℝ)⁻¹)^4*q/1024:=by
 let a:= (L.val:ℝ)⁻¹; have ha:0≤a:=by unfold a; positivity
 have hx: |t| *|x| ≤ 3*q:=mul_le_mul (peg_ub v) u (abs_nonneg x) (by norm_num)
 have hA:0 ≤ A:=zero_le_one.trans hp.root; rw [choice_nax]; refine (le_abs_self _).trans ?_; rw [abs_mul]; change |VZ| *|a^5*_+T|≤ _; calc
    _ ≤ |VZ| *(a^5*((A+4)*q)):=by
       refine mul_le_mul_of_nonneg_left ((abs_add_le ..).trans ?_) (abs_nonneg _); rw [abs_of_nonneg (by positivity:a^5*(|t| *|x|+A*q)≥0)]; change |T| ≤ a^5*q at f
       linarith only [f,mul_le_mul_of_nonneg_left hx (pow_nonneg ha 5)]
    _ ≤ _:=by
       have ht:a^5*(1024*|VZ| *(A+4)*q) ≤ a^4*q:=choice_next hq.le (mul_le_mul_of_nonneg_right hp.mean hq.le); change _≤a^4*q/1024; linarith only [ht]
lemma nail (p:αPrice L h (A*q) T VZ VX VY (PointSk x) (PointSk b) P Y (t:ℂ)) : |b-qC*t*x| ≤ ((L.val:ℝ)⁻¹)^4*q/1024:=by
 have hz: ζtap L P Y (t:ℂ) (PointSk x)=(qC*t*x) • mainSlot:=by unfold ζtap PointSk; rw [Complex.coe_smul,Complex.coe_smul,smul_smul]; exact (mul_smul (qC * t) x _).symm
 have hv:= p.red.trans (nax_cost hp hq v f u); rw [hz] at hv; change ‖b • _ - _‖ ≤ _ at hv; rwa [←sub_smul,norm_smul,slotNorm, mul_one,Real.norm_eq_abs] at hv

omit u
include w
variable (b' q':ℝ)
structure KeyRadius (L:Side) (s b:ℝ):Prop where
 up:|b|≤64*((L.val:ℝ)⁻¹)^4*s
 dn:((L.val:ℝ)⁻¹)^4*s/64≤ |b|
lemma fixed_cost (p:αPrice L h (A*q) T VZ VX VY (PointSk q) (PointSk b) P Y (t:ℂ))
 (S q':ℝ) (sp:S=qC)(a: S ≤ 4*((L.val:ℝ)⁻¹)^4) (r: ((L.val:ℝ)⁻¹)^4/4 ≤ S)(b1:q≤q')(b2:q'≤2*q):KeyRadius L q' b:=by
 let c:= ((L.val:ℝ)⁻¹)^4; have hc:0≤ c:=by unfold c; positivity
 have hv:0≤S:=(div_nonneg hc (by norm_num)).trans r
 change c/4≤S at r; change S≤ 4*c at a
 let k:= c*q; have he:|b-S*t*q|≤c*q/1024:=sp.symm ▸ nail hp hq v f (abs_le.mpr ⟨by linarith only [hq],le_rfl⟩) p
 have hm: |S*t*q|-|b|≤ |b-S*t*q|:= (abs_sub_abs_le_abs_sub ..).trans_eq (abs_sub_comm ..)
 have hm':|b|-|S*t*q|≤ |b-S*t*q|:=abs_sub_abs_le_abs_sub ..
 have e': |S*t*q|=S*|t| *q:=by rw [abs_mul,abs_mul,abs_of_nonneg hv,abs_of_nonneg hq.le]
 have h1:=mul_le_mul_of_nonneg_right (mul_le_mul r (peg_lb w) (by norm_num) hv) hq.le
 have h2:=mul_le_mul_of_nonneg_right (mul_le_mul a (peg_ub v) (abs_nonneg _) (by positivity)) hq.le
 constructor
 · change |b| ≤64*c*q'; linarith only [he,hm',e',h2,mul_le_mul_of_nonneg_left b1 hc,mul_nonneg hc hq.le]
 change c*q'/64 ≤ _; linarith only [he,hm,e',h1,mul_le_mul_of_nonneg_left b2 hc,mul_nonneg hc hq.le]
omit w
lemma gap_cost (p:αPrice L h (A*q) T VZ VX VY (PointSk 0) (PointSk b') P Y (t:ℂ)) (b1:q≤q') (hb: KeyRadius L q' b): |b'|≤|b|/8:=by
 have he:= nail hp hq v f (by simpa using hq.le) p; rw [mul_zero,sub_zero] at he
 let c:= ((L.val:ℝ)⁻¹)^4; have hc:0≤ c:=by unfold c; positivity
 have hx:= hb.dn; change c*q'/64≤ _ at hx; change |b'|≤ c*q/1024 at he; linarith only [he,hx,mul_le_mul_of_nonneg_left b1 hc,mul_nonneg hc hq.le]
end YM.CF.QuadClock
