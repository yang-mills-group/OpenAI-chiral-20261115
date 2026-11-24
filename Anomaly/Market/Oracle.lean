import Anomaly.Market.Vendor
import Anomaly.Market.Scar
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Regis.Head.GeometryP
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Gleam Matrix ProbabilityTheory
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {c n : Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ ε Λ α ρ D:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f l m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)
open CF.Swell.Sonar Garland Etch Next.Free Push.Local
variable {I J:Type*} [Fintype I][Fintype J] {T:ℝ} (L:Tour I n)(O:I→ Site n)
variable (F: I→ Config G n→ℂ)(W:I→tableQ G n ℂ)(fp:ℂ→L[ℝ] ℝ)(ov:‖fp‖≤1)(EΩ:J→Tour I n)
def bistro (x:Config G n):=∑ j, booth (EΩ j) F fp x
-- budget.Secure **closed convention**.
structure Secure (F: I→ Config G n→ℂ)(W:I→tableQ G n ℂ)(P:BudgetPoint)(o:I→Site n) (k:ℕ)(α T B S A:ℝ): Prop where
 shu(i:I): Envelope (F i)
 passing(i:I)(V:Config G n)(g:Site n→G.El): F i (gauge g V)=F i V
 hoop(i:I)(x:Config G n): ‖F i x‖≤ B
 bunker(i:I): costs (W i)≤T
 inSpan(i:I): Regional (o i) k (W i)
 value(i:I)(V:Config G n)(p:Healthy P.threshold (halo P.B {o i}) V)(X:Dir G n)(q:Agrees (halo k {o i}) V (represent X))(t:‖collect G X‖<α): ‖F i V - S^2 • tariff (W i) (receipt X)‖ ≤ A*‖collect G X‖^3
variable {F W O fp}{Γ:ℝ}(U':Secure F W p O l α T ξ ρ Γ)
local notation "Δ"=> halo l
include U'

lemma kettle (y:Config G n)(g:Site n→G.El): bistro F fp EΩ (gauge g y)=bistro F fp EΩ y:=by refine sum_congr rfl fun i _=> congrArg fp (prod_congr rfl (fun j _=>?_ )); exact invariant_pull (f:=F j) (fun k x=>U'.passing j x k) _ _ g y -- defined real valued
include ov
lemma vigil (y:Config G n)(h:0≤ξ): |booth L F fp y| ≤ ξ^Fintype.card I := by refine (contracts fp ov _).trans (?_); rw [norm_prod]; exact (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=> U'.hoop i _)).trans_eq (by simp)
lemma shutterE (h:0≤ξ): Envelope (booth L F fp) :=by
 refine ⟨fp.continuous.measurable.comp (Finset.measurable_fun_prod _ (fun i _=> (U'.shu i).meas.comp (prior_pull (L.orient i) (L.loc i)).measurable)),ξ^Fintype.card I,fun j=> by rw [Real.norm_eq_abs]; exact vigil L ov U' j h⟩
lemma concert (h:0≤ξ): Envelope (bistro F fp EΩ):= Envelope.sum univ _ (fun i=> shutterE _ ov U' h)

lemma dash (s:Signed)(b:Site n)(x:Config G n): bistro F fp EΩ (pull s b x)= bistro F fp (fun i=>(EΩ i).moves s b) x:= sum_congr rfl fun i _=>booth_pulled ..
-- besides. even keep ψ angular powers if needed. near support balls.
variable (hv:0≤v)(ht:v≤R.c)(hX:Γ≥0)(hY:2*v<α)(bR:p.B+2≤hallBill m)(h:l + 2 + Sequest m ≤ hallBill m)(e:0<β)(g:0<D)(hr: 0≤ξ)(hp:0 ≤ T) (hx: |ρ| *(p.threshold+faceCutError R v)≤ D)
-- P conflict p Point
include hv ht hY bR h e g hr hp hx hX
abbrev feesx (i:ℕ) (D T ξ Γ v:ℝ):ℝ:= (1+ ξ+(2*D)^2*T)^i * (i:ℝ) * (Γ * (2*v)^3)
abbrev feesB (i:ℕ) (D T ξ:ℝ):ℝ:= ξ^i+ ((2*D)^2*T)^i
lemma servesHere (X Y:Dir G n)(V: Config G n) (f:ProbeBox (X+Y) (2*v))(t:TrustLogs (X+Y) V r A v)(p':∀ i,withinCore r A (face_anchors (misdemean p.threshold V)) (hallBill m) (seats L O i)):
     let z:= starFeed B P r A (face_anchors (misdemean p.threshold V)) m Y β X
     |booth L F fp V- imagined L fp W q D (ρ*coupling β) z|≤ feesx (Fintype.card I) D T ξ Γ v:=by -- tune named
 intro z; let a(i:I):=L.orient i; let b(i:I):=L.loc i; let j(i:I):= bank (a i) (b i) (X+Y)
 let Ψ(i:I):=F i (pull (a i) (b i) V); let Λ(i:I):=coverT (W i) (a i) (b i) q (ρ*coupling β) D z
 have hx(i:I): ‖Ψ i-Λ i‖≤Γ*(2*v)^3:=by 
    unfold Λ; rw [lump B P (W i) (a i) (b i) ρ X Y (p' i) h e t ht hv (U'.inSpan i) g hx]; let c':= collect_boundS (a i) (b i) _ f (by positivity)
    exact (U'.value i _ (maskSafe _ _ _ (p' i) bR) (j i) (forest_yaw (a i) _ _ (p' i) t ht (by unfold hallBill Sequest at h ⊢; omega)) (c'.trans_lt hY)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) c' _) hX)
 let U:= (2*D)^2*T; have hu:0≤U:=by unfold U; positivity
 let T:= 1+ξ+U
 have hp':1 ≤ T:=by unfold T; linarith only [hu,hr]
 unfold booth imagined; rw [←map_sub]; refine (contracts fp ov _).trans ((boundsProd (X:=Ψ) (Y:=Λ) (fun i=> (U'.hoop i _).trans (?_)) (fun i=> ((potQ (W i) _ _ _ _ _ g _).trans (mul_le_mul_of_nonneg_left (U'.bunker i) (sq_nonneg _))).trans (?_)) hp' univ).trans (?_))
 · unfold T; linarith only [hu]
 · change U ≤ T; unfold T; linarith only [hr]
 · unfold feesx; rw [card_univ]; apply (mul_le_mul_of_nonneg_left ((sum_le_sum (fun i _=> hx i)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])) (pow_nonneg (zero_le_one.trans hp') _)).trans_eq; unfold T U; ring

lemma staffSeat (U:Finset (Cell n))(y:0 ≤ w)(l: Odd r.count.val)(hw:hallBill m ≤ r.count.val/2)(b0:scopes EΩ O)(hw': |t| *feesB (Fintype.card I) D T ξ* Fintype.card I ≤4*w) : ShelfScene B P p r m β v ε (feesx (Fintype.card I) D T ξ Γ v * |t| *Fintype.card J + w*(trap r m A+trap_s m U)) A U t (bistro F fp EΩ) (columnV fp W q D (ρ*coupling β) EΩ):=by
 intro X V Y _ h' pZ h1; let B':= starFeed B P r A (face_anchors U) m Y β V; let a(j:J):= booth (EΩ j) F fp X-imagined (EΩ j) fp W q D (ρ*coupling β) B'; let E:=univ.filter fun i:J=> ¬∀ j:I, withinCore r A (face_anchors U) (hallBill m) (seats (EΩ i) O j); let u:= feesB (Fintype.card I) D T ξ; let q':= feesx (Fintype.card I) D T ξ Γ v; have hp':0 ≤ q':=by unfold q' feesx; positivity
 have he(i:J):|a i| ≤ q'+if i∈E then u else 0 :=by
    split; next=> exact (abs_sub ..).trans ((add_le_add (vigil _ ov U' X hr) (observes (EΩ i) fp ov W q D _ g U'.bunker B')).trans (le_add_of_nonneg_left hp'))
    next h=> have p:∀ j:I, withinCore r A (face_anchors U) (hallBill m) (seats (EΩ i) O j):=of_not_not (fun q=>h (mem_filter.mpr ⟨mem_univ _,q⟩)); rw [add_zero]; subst U; exact servesHere B P _ ov U' hv ht hX hY bR ‹_› e g hr hp hx V Y X pZ h1 p
 have hK:E.card ≤ Fintype.card I * (Fintype.card (Site c)* largerBill r.count.val (hallBill m)+A.card*r.count.val^4+U.card*coldBill (hallBill m)):=by
    let N(j:I):= univ.filter fun i:J=> ¬ withinCore r A (face_anchors U) (hallBill m) (seats (EΩ i) O j)
    refine ((card_le_card (show E⊆univ.biUnion N from ?_)).trans (card_biUnion_le ..)).trans (?_)
    · intro i p; obtain ⟨j,y⟩:= not_forall.mp (mem_filter.mp p).2; exact mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨mem_univ _,y⟩⟩
    have he(j:I): (N j).card≤ _:= (Eq.ge (card_image_of_injective (N j) (b0 j))).trans ((card_le_card (show (N j).image (fun i=> seats (EΩ i) O j) ⊆ univ.filter (fun i=> ¬ withinCore r A (face_anchors U) (hallBill m) i) from ?_)).trans (land_fee A U l hw))
    · simpa using sum_le_sum (fun (j:I) (_: j∈univ)=>he j)
    intro i z; obtain ⟨k,p,rfl⟩:= mem_image.mp z; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2⟩
 apply (sub_le_iff_le_add').1; unfold bistro columnV; rw [←mul_sub,←sum_sub_distrib]; apply (le_abs_self _).trans; rw [abs_mul]; refine (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum (fun i _=> he i))) (abs_nonneg _)).trans ?_; rw [sum_add_distrib,←sum_filter]; simp only [sum_const,card_univ,nsmul_eq_mul,filter_mem_eq_inter,univ_inter]
 let μ:ℝ:= Fintype.card (Site c)* (largerBill r.count.val (hallBill m):ℕ)+A.card*(r.count.val:ℝ)^4+U.card*(coldBill (hallBill m):ℕ)
 have hu:(E.card:ℝ) ≤ Fintype.card I * μ:= by refine (Nat.cast_le (α:=ℝ).2 hK).trans_eq ?_; unfold μ; push_cast; ring
 rw [show trap r m A+trap_s m U=4*μ from by unfold trap trap_s μ; ring]; change |t| * ((Fintype.card J:ℝ)*q'+(E.card:ℝ)*u) ≤ q'* |t| *Fintype.card J+w*(4*μ) -- adjust
 nlinarith only [mul_le_mul_of_nonneg_left hu (show 0≤ |t| * u from mul_nonneg (abs_nonneg t) (by unfold u feesB; positivity)), mul_le_mul_of_nonneg_left hw' (show 0 ≤ μ from by unfold μ; positivity)]
end YM.Regis.Head.GeometryP
