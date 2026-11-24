import Bay.D.Cation
import YM.SU5.Thin.Glacier.Hilltop
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group

variable {n:Side}{q:Clip}{Z:PathData T4}{H:Bed}{η C S δ w:ℝ}

variable {o d:Site n} {B:Z.Bounds q η C S}{P:Attached H Z}
 {p:BudgetPoint} {β v M N E L:ℝ}
 {F:Yn n ℝ}{W:Chalk n ℝ}
variable {I:Type}[Fintype I]
def gusts(gs:I→Kite n)(F:Yn n ℝ)(x:Config T4 n):ℝ:=
 ∑i,F ((gs i).swirl x)
def picks(gs:I→Kite n)(W:Chalk n ℝ)(x:Dock n):ℝ:=∑i,W (gs i) x
def flavor (B:Z.Bounds q η C S)(P:Attached H Z)(W:Chalk n ℝ):ℝ:=
 clouds B P (W 1)

lemma packed_shift {gs:I→Kite n}(u:Packed gs o d)(h:Kite n):
 Packed (fun i=>h*gs i) o d:=by
 unfold Packed;simp_rw[Kite.r_mul]
 exact ⟨h.r_inj.comp u.1,h.r_inj.comp u.2⟩

lemma gusts_shift (gs:I→Kite n)(h:Kite n)(F:Yn n ℝ)(x:Config T4 n):
 gusts gs F (h.swirl x)=gusts (fun i=>h*gs i) F x:=
 sum_congr rfl fun i _=>congrArg F (Kite.union h (gs i) x)

namespace Ion
variable (u:Ion B P p β v o d F W M N E L)
 (gs:I→Kite n)
include u

lemma gust_env:RG.Envelope (gusts gs F):= RG.Envelope.sum univ _ fun i=>
    ⟨(u.shift (gs i)).sane,M,(u.shift (gs i)).limit⟩
lemma gust_scale: GaugeInvariant (gusts gs F):= fun y a=>sum_congr rfl fun i _=>
    (u.shift (gs i)).gauge y a
lemma gust_fine: ContDiff ℝ 1 (picks gs W):=ContDiff.sum fun i _=> u.gloss (gs i)
lemma gust_arc (x:Dock n): |picks gs W x|≤ Fintype.card I*N:=by
 rw[←Real.norm_eq_abs]
 exact (norm_sum_le ..).trans ((sum_le_sum fun i _=>u.high (gs i) x).trans_eq
    (by rw[sum_const,card_univ,nsmul_eq_mul]))
lemma gust_lip (p:Packed gs o d)(x:Dock n):‖fderiv ℝ (picks gs W) x‖≤L*Real.sqrt (Fintype.card I):=by
 let R:NNReal:=⟨_,mul_nonneg u.perks.2.2.2 (Real.sqrt_nonneg (Fintype.card I))⟩
 apply norm_fderiv_le_of_lipschitz ℝ (C:=R) (LipschitzWith.of_dist_le_mul ?_) -- x implicit?
 intro x y;rw[dist_eq_norm,dist_eq_norm]
 unfold picks
 rw[←sum_sub_distrib]
 exact (norm_sum_le ..).trans (u.alloy _ _ p ..)
lemma gust_habi (g:Kite n):Integrable (fun x:stamen B P n=>W g x.val)
    (stdGaussian (stamen B P n)):=by
 apply Regis.bree (a:=N) _ _
 · exact ((u.gloss g).continuous.comp continuous_subtype_val).measurable
 intro i;rw [←Real.norm_eq_abs]; exact u.high g i

lemma flavor_fee: |flavor B P W|≤N:=by
 unfold flavor clouds
 rw [← Real.norm_eq_abs]
 refine le_trans (norm_integral_le_of_norm_le (integrable_const N)
    (Eventually.of_forall fun i=>u.high 1 i.val)) ?_
 simp

variable (t:Floor H q n δ w)(x:Bid.Sworn H n T4)
include t x
lemma flavor_scent(g:Kite n):
   clouds B P (W g)=flavor B P W:=
 (cover_calms g.turn g.gust B P t x _ _
    (u.gloss 1).continuous (fun i=>by
      exact (u.spins g 1 i).trans (congrFun (congrArg W (mul_one g)) _))).symm

lemma gust_fee (a:ℝ):
 plumeCost B P (picks gs W) a=Fintype.card I*(a*flavor B P W):=by
 rw [plumeCost,cloud_turn B P _ (u.gust_fine gs).continuous]
 have hX(i:I): ∫x:stamen B P n, W (gs i) x.val ∂stdGaussian (stamen B P n)=flavor B P W:= u.flavor_scent t x _
 unfold clouds picks
 rw [integral_finsetSum]
 · simp_rw[hX,sum_const,card_univ,nsmul_eq_mul]
   ring
 exact fun i _=>u.gust_habi (gs i)

end Ion

variable (u:Ion B P p β v o d F W M N E L)
 {a:ℝ}{c:Side}(r:Ratio c n){gs:I→Kite n}

open scoped Classical in
include u in
lemma Ion.gust_foot
  (t:|a| * (M+N) ≤1)(g:Packed gs o d)
  (h:Odd r.count.val)(l:hallBill p.B ≤ r.count.val/2)
  (A:Support c)(D:Finset (Cell n))(τ:ℝ):
 RimScene B P p r p.B β v
   (Fintype.card I*(|a| * E)+fritTrap r p.B A D) τ A D a (gusts gs F) (picks gs W):=by
 intro U V Y _ f k w
 let y:=iceCost B P r A p.B D Y β V
 let Df(x:Site n):Finset I:=univ.filter fun i=> ¬Deep r A D (hallBill p.B) ((gs i).rise x)
 let Z:=Df o∪Df d
 let ndf:=surfaceBill r (hallBill p.B) A D
 have hf(x:Site n)(j:Injective (fun i=>(gs i).rise x)): (Df x).card≤ndf:=by
   let f:=fun i=>(gs i).rise x
   rw [←card_image_of_injective (Df x) j]
   apply le_trans (card_le_card _) (field_wall h l)
   intro i hi; obtain ⟨u,h,rfl⟩:=mem_image.mp hi
   exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩

 have hz:Z.card≤2*ndf:= (card_union_le ..).trans ((Nat.add_le_add (hf _ g.1) (hf _ g.2)).trans_eq (two_mul ..).symm)
 have h₀:0≤ |a| * E:=mul_nonneg (abs_nonneg _) u.perks.2.2.1
 have he(i:I):a*F ((gs i).swirl U) -a*W (gs i) y ≤ (|a| * E+if i∈Z then (1:ℝ) else 0):=by
   rw [←mul_sub]
   apply le_trans (le_abs_self _);rw [abs_mul,←Real.norm_eq_abs (_-_)]
   split
   · apply le_trans _ (le_add_of_nonneg_left h₀)
     apply le_trans _ t
     exact mul_le_mul_of_nonneg_left
        ((norm_sub_le ..).trans (add_le_add (u.limit _) (u.high _ _))) (abs_nonneg _)
   rw [add_zero]
   rename_i h
   have hx : Deep r A D (hallBill p.B) ((gs i).rise o)∧
           Deep r A D (hallBill p.B) ((gs i).rise d):=by
      simpa [Z,Df] using h
   exact mul_le_mul_of_nonneg_left (u.day U V Y (gs i) w k f.symm hx.1 hx.2) (abs_nonneg _)
 refine (sub_le_iff_le_add'.mp ?_)
 rw [gusts,picks,mul_sum,mul_sum,←sum_sub_distrib]
 apply (sum_le_sum (fun i _=>he i)).trans
 rw [sum_add_distrib,←sum_filter]
 simp only [sum_const,nsmul_eq_mul,card_univ,filter_mem_eq_inter,univ_inter,mul_one]
 apply add_le_add le_rfl

 rw [show fritTrap r p.B A D=4*(ndf:ℝ) from ?_]
 · apply (Nat.cast_le.mpr hz : (↑Z.card:ℝ)≤↑(2*ndf:ℕ)).trans
   push_cast; exact mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
 unfold ndf surfaceBill fritTrap; push_cast;rfl

section Lint
abbrev tithe (E L θ:ℝ):= θ*E+Regis.trend*L^2*θ^2
include u in
lemma tithe_le (θ:ℝ)(j:|a|≤θ):|a| *E+
 Regis.trend *L^2*a^2≤tithe E L θ:=by
 have :=u.perks.2.2.1 -- omitted? include u
 have ht:0≤Regis.trend:=by unfold Regis.trend; positivity
 rw[←sq_abs a]
 unfold tithe
 exact add_le_add (mul_le_mul_of_nonneg_right j ‹0≤E›) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg a) j _) (by positivity))

end Lint
end YM.CF.Bay.D
