import YM.SU5.Exchange.Reg.Incidence
import YM.SU5.Exchange.Pilot.Contour
import YM.SU5.WakeFields.GateShelf

/-!
# Location receipts. Distance decay of allocations arriving from planted core

We keep the scale 1/B **even here**, stronger may cost too much for a Ward-vial pilot. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 390000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson RG Scroll Fock Cadre Stax Mew Roots
open Push.AbsoluteSums Trees Ione MeasureTheory Finset
open Cube Lat Vow Tulip Skye Scree Hake Jet Sault
open scoped Topology ContDiff BigOperators Classical
variable {n:Side} (P:BudgetPoint) {a b h:ℝ}
-- a little bandwidth
abbrev discount (B : ℕ) : ℝ:= (↑B : ℝ)⁻¹
abbrev dutyGlide (B:ℕ)(x y:Seat n) := Real.exp (-(((4*B:ℕ):ℝ)^2)⁻¹/2 * separation x y)
abbrev coastU (B:ℕ)(c:ℕ) : ℝ:= ((c:ℝ)*taxIns (4*B))* Real.exp 1
lemma coastSafe (B:ℕ)(c:ℕ) : 0≤ coastU B c := by unfold coastU taxIns fernL; positivity
lemma glide_cost (x y:Seat n)(X:Aura n)(p:x∈X.val)(q:y∈X.val)(w:ℝ) :
    tact w P.B X ≤ dutyGlide P.B x y * (Real.exp 1 * tact (w+discount P.B) P.B X) := by
 let b:ℝ:= P.B; let d:ℝ:= separation x y; let k:ℝ:= coverNumber P.B X.val
 unfold tact dutyGlide; rw [←Real.exp_add,←Real.exp_add,add_mul,neg_div,neg_mul]; apply Real.exp_monotone
 have hz: separation x y ≤ (coverNumber P.B X.val)*(4*P.B+2)+2*P.B:= Corona.extent _ P.B p q; have hf:d≤ k*(4*b+2)+2*b:=by unfold d k b; exact_mod_cast hz
 have hP : 0<b:= Nat.cast_pos.mpr P.B_pos; have hx:b≥1:=Nat.one_le_cast.mpr P.B_pos; have hk:0 ≤ k:=Nat.cast_nonneg _
 push_cast; change w*k ≤ -((((4*b)^2)⁻¹ / 2)*d)+(1+(w*k+b⁻¹*k))
 have ht : (((4*b)^2)⁻¹ / 2)*d ≤ 1+b⁻¹*k:=by
    rw [show (((4*b)^2)⁻¹/2)=(32*b^2)⁻¹ from (by field_simp; ring),mul_comm ((_)⁻¹ :ℝ),←div_eq_mul_inv]
    rw [div_le_iff₀ (by positivity : (0:ℝ)< _)]; change d ≤ _; apply hf.trans
    rw [show (1+b⁻¹*k)*(32*b^2)=32*b^2+32*k*b from (by field_simp)]
    nlinarith only [hx,hk,hf]
 linarith only [ht]
lemma seats_count {I:Type}[LinearOrder I][Fintype I](σ:I→Seat n)(t:ℕ)(p:Force_M P.B σ t)(x:Seat n) : (univ.filter (fun i:I=>σ i=x)).card ≤ t:= by
 refine le_trans (card_le_card ?_) (p.2 x); intro i u; refine mem_filter.mpr ⟨mem_univ _,?_⟩; rw [(mem_filter.mp u).2,separation_self]; exact Nat.zero_le _
lemma coastTreasury {I:Type}[LinearOrder I][Fintype I](σ:I→Seat n)(t:ℕ)(p:Force_M P.B σ t)(x: Seat n) :
    ∑ i:I,dutyGlide P.B x (σ i) ≤ t*taxIns (4*P.B):=by
 let G(y:Seat n):= dutyGlide P.B x y
 rw [←sum_fiberwise_of_maps_to (s:=univ) (g:=σ) (t:=univ) (fun i _=>mem_univ _)]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (placeExpense (4*P.B) (by have he:= P.B_pos; omega) x) (Nat.cast_nonneg t))
 rw [mul_sum]; refine sum_le_sum fun i _=> ?_
 let S:=univ.filter fun j=> σ j=i
 have hv: (S.card:ℝ)≤ t:= Nat.cast_le.mpr (seats_count P σ t p i)
 rw [sum_congr rfl (g:=fun _=> G i) (fun j h=>by rw [(mem_filter.mp h).2]),sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right hv (Real.exp_pos _).le
-- require anchors even when planner certificate sparse by figure. no topology on V
lemma coastTransit {I:Type}[LinearOrder I][Fintype I](σ:I→Seat n)(t:ℕ)(p:Force_M P.B σ t)
    (V:I→ Aura n→ℝ)(u:0≤V)(Z : ∀ i X,V i X≠0 → σ i∈X.val) (e:∀ i,voyageB (V i) P.B (a+discount P.B)≤ b) (g:0≤b) (x: Seat n) :
    Cadre.nook ((∑ i,V i)*tact a P.B) x ≤ coastU P.B t*b := by
 let K(x:Aura n):= tact a P.B x; let L:=tact (n:=n) (a+discount P.B) P.B; let S:= Cadre.spark x; let E:=Real.exp 1; let D(i:I):= dutyGlide P.B x (σ i)
 have ht(i:I): (∑ j∈S, V i j*K j) ≤ D i*(E*b):=by
    have hh: (∑ j∈S,V i j*L j) ≤ b:= (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>mul_nonneg (u i j) (Real.exp_pos _).le)).trans (e i)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le) (Real.exp_pos _).le)
    simp_rw [mul_sum]; refine sum_le_sum fun j v=> ?_
    by_cases t: V i j=0
    · rw [t]; simp
    refine le_trans (mul_le_mul_of_nonneg_left (glide_cost P x (σ i) j (mem_filter.mp v).2 (Z i j t) a) (u i j)) (le_of_eq ?_)
    unfold D E L; ring
 unfold nook; simp_rw [Pi.mul_apply,Finset.sum_apply,sum_mul]; rw [sum_comm]
 apply le_trans (sum_le_sum (fun i (_:i∈univ)=> ht i)); rw [←sum_mul]; exact (mul_le_mul_of_nonneg_right (coastTreasury P σ t p x) (mul_nonneg (Real.exp_pos _).le g)).trans_eq (by unfold coastU; rw [←mul_assoc]) -- potential absurd.T.
end YM.CF.Sour
#print axioms YM.CF.Sour.coastTransit
