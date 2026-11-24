import Risa.Array
import Risa.Testify
import Risa.Leaves
import Risa.Clamp
import Risa.Aurora
import YM.SU5.Regis.Hospitality
import Taffeta.Stigma
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Luster
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ v' ν θ ω':ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable {X Y:fieldDir G n 1}{D:Finset (Cell n)}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)(D':LocalRatio J)
namespace Risa
open Regis ProbabilityTheory
open _root_.YM.Regis.Head AnalyticBridge.VerifiedReset StressFlux Lattice.PlaqAxes Virgo _root_.YM.CF.Scree
local notation "D1" => CF.Compass.decor
variable (Xh:Hike) (y:ℝ)
local notation "χ"=> Xh.cost
local notation "Γ"=> (ridges:ℝ)
local notation "𝕥"=>p.threshold
local notation "τh"=>tempRate p Xh y
local notation "Υ₀"=>posess G Xh
section
universe wP
variable {I:Type wP}[Fintype I](o:I→Bool→ Site n)(p0:∀i:Bool,Injective (fun j:I=>o j i))(t:I→Bool→ Signed)(a:I→ℝ)(n₀:Bool)
variable (j:Odd r.count.val)(wH:hallBill m≤ r.count.val/2)
def snagS{I:Type wP}[Fintype I](r:Ratio c n)(F:Support c)(D:Finset (Cell n))(m:ℕ)(o:I→Site n):=univ.filter fun i=>¬stint r m F D (o i)
-- marker count all defects.
include wH j
lemma snag_cover (D':I→ Site n)(T: Injective D')(A:Support c)(D:Finset (Cell n)): 4*((snagS r A D m D').card:ℝ) ≤ snags r m A D:=by
 let Z:=snagS r A D m D'; let H:=univ.filter (fun i=>¬Safe r A (hallBill m) i); let F:=Lattice.halo (hallBill m) (D.image Prod.fst)
 have he: Z.image D'⊆ H∪ F:=by
    intro i t; obtain ⟨k,p,rfl⟩:=mem_image.mp t; have h:= (mem_filter.mp (show k∈snagS r A D m D' from p)).2; unfold stint vigilant at h
    by_cases v:Safe r A (hallBill m) (D' k); swap; · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,v⟩)
    push Not at h; obtain ⟨b,g,u⟩:=h v; exact mem_union_right _ (halo_spec.mpr ⟨_,mem_image_of_mem _ g,u⟩)
 have hx: Z.card ≤ (Fintype.card (Site c)* largerBill r.count.val (hallBill m) + A.card*r.count.val^4)+D.card*lusterBill (hallBill m):=by
    rw [←card_image_of_injective Z T]; refine (card_le_card he).trans ((card_union_le ..).trans (add_le_add (cool_home j wH) ((Corona.halo_size _ _).trans (Nat.mul_le_mul_right _ card_image_le))))
 have h':=Nat.cast_le (α:=ℝ).mpr hx; unfold snags lusterBill; push_cast; push_cast at h'; linarith only [h']
variable {k f:ℝ}(e:∀i:I,|a i| ≤ k)(K:0 ≤ k)(hX:4*k *(tempRate p Xh y)^2≤1)
local notation "λc"=> coupling β
include B P p0 j wH e K hX
lemma pricer (R:Rules G)(g:0 ≤ v) (hw:v ≤ R.c) (hv:(Υ₀).payroll ≤ m)(h₀:20 ≤ m)(h:0<β)(fee:sunFee Xh R y p (v:=v) ≤ 1)(A:Support c)(D:Finset (Cell n)) : GradeLease B P p r m β v ((Fintype.card I:ℝ)*k*((2*(gradM p y+1))* sunFee Xh R y p (v:=v)) +1*snags r m A D) v' A D (tables G p y o t a n₀) (tableZ G q Xh (y*coupling β) o t a n₀):=by
 intro U V Y ha hd db l
 let X₀:=starFee B P r A D m Y β V; let N(i:Bool)(j:I):= solicit G p y (t j i) (o j i) U; let C:(Bool→I→ℝ):= fun i j=> (Υ₀).chalk q (y*λc) (t j i) (o j i) X₀
 let ψ:=tempRate p Xh y; let S:= sunFee Xh R y p (v:=v)
 let M(i:Bool): Finset I:=snagS r A D m (fun k:I=>o k i)
 have hg(i:Bool): 4*((M i).card:ℝ) ≤ snags r m A D:=snag_cover j wH _ (p0 _) .. 
 let Δ(i:Bool)(k:I):= |N i k-C i k|
 obtain ⟨hψ,hQ,hH⟩:=rate_at (G:=G) Xh y p
 change 1≤ ψ at hψ; change (Υ₀).arc ≤ψ at hQ; change gradM p y ≤ψ at hH
 have hN(i:Bool)(j:I): |N i j| ≤ ψ:= (launchQ G p y _ _ U).trans hH
 have hC(i:Bool)(j:I): |C i j| ≤ ψ:= ((Υ₀).chalk_bound ..).trans hQ
 have hL(i:Bool)(j:I)(p':j ∉ M i): Δ i j ≤ S:= same_act B P Xh p (t j i) R y hv (by simpa only [M,snagS,mem_filter,mem_univ,true_and,not_not] using p') l g hw h hd h₀
 unfold tables tableZ; apply (sub_le_iff_le_add').1; rw [←sum_sub_distrib]
 let c₀:=gradM p y+1
 let sα(i:Bool)(j:I):ℝ:=if j∈M i then 2*ψ^2 else 0
 have hsα(i:Bool)(j:I):0≤ sα i j:=by unfold sα; split; positivity; exact le_rfl
 have hs:0≤ S:=sun_safe B P Xh p R y (v:=v)
 have hv: 1 ≤ c₀:=le_add_of_nonneg_left (by unfold gradM ridges; positivity)
 have he(i:I): a i * raiseX G p y n₀ U (t i) (o i)-a i*raiseZ G q Xh (y*λc) n₀ X₀ (t i) (o i) ≤ k*(2*c₀*S+∑ b:Bool,sα b i):=by
    apply le_trans (le_abs_self _)
    rw [← mul_sub_left_distrib,abs_mul]; refine mul_le_mul (e _) ?_ (abs_nonneg _) K
    by_cases h:∀ b:Bool,i ∉M b
    · have ah(j:Bool): |N j i| ≤ gradM p y:= launchQ ..
      refine (grainL hv (fun j=> (ah j).trans (le_add_of_nonneg_right zero_le_one)) (fun j=>?_:∀ j:Bool,|C j i| ≤ c₀)).trans ((mul_le_mul_of_nonneg_left (sum_le_sum (fun j _=>hL j i (h j))) (zero_le_one.trans hv)).trans ?_)
      · calc
         |C j i|=|(C j i -N j i)+N j i|:=congrArg abs (by ring)
         _ ≤ |C j i-N j i|+|N j i|:=abs_add_le _ _
         _≤ c₀:=by rw [abs_sub_comm]; unfold c₀; exact (add_le_add ((hL j i (h j)).trans fee) (ah j)).trans_eq (add_comm ..)
      have hx: 0≤∑ j:Bool,sα j i:=sum_nonneg fun j _=>hsα _ _
      rw [Fintype.sum_bool (fun _=>S)]; linarith only [hx]
    push Not at h; obtain ⟨j,h⟩:=h
    refine (abs_sub _ _).trans ((add_le_add (grainD hψ (fun j=>hN j i)) (grainD hψ (fun j=>hC j i))).trans (le_trans (le_of_eq ?_) ((show 2*ψ^2≤ ∑ b:Bool,sα b i from ?_).trans (le_add_of_nonneg_left (show 0≤2*c₀*S by nlinarith only [hv,hs,mul_nonneg (zero_le_one.trans hv) hs])))))
    ring
    exact (show _≤ sα j i from le_of_eq (if_pos h).symm).trans (single_le_sum (fun j _=>hsα j i) (mem_univ j))
 refine (sum_le_sum (fun i _=>he i)).trans ?_; simp_rw [mul_add k (2*c₀*S)]; rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum,sum_comm]
 have hl(b:Bool): (∑ i:I, sα b i) = ((M b).card:ℝ)*(2*ψ^2):=by unfold sα; rw [←sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
 simp_rw [hl]; rw [Fintype.sum_bool]; change _ ≤(Fintype.card I:ℝ)*k*(2*c₀*S)+_
 have hz:= hg true; have zh:=hg false; have hX1:4*k*ψ^2≤1:=hX
 nlinarith only [hz,zh,mul_le_mul_of_nonneg_right hX1 (show 0≤((M false).card:ℝ)+((M true).card:ℝ) by positivity)]
#check @sun_safe
#check @snag_cover
#print axioms pricer
end
end Risa
end YM.Gleam.Luster
