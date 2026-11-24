import YM.SU5.Exchange.Reg.RateMargin
import YM.SU5.Exchange.Reg.Union
import YM.CF.Milo.Cent
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
-- root pension distribute. supports preserving regular total memory.
open Tenant
private lemma stillRetreat (i : Hz) (F : InkD n) (t : PressB (raiseRate P) i F h a) :
 PressB P i F h a := by
 obtain ⟨b,f,q,r⟩:=t.worth
 exact ⟨t.term,t.fitted,t.measureV,t.gaugeV,b,f,fun V h i=>let q:=q V h i; ⟨q.grade,q.paid,q.token⟩,r⟩

-- raise (124) portion once more, taking the min later with light occupancy.Still pays with NO repapping.
lemma warm_snap (X:Scree.Hub n)(Y:Seat n)(p:Y∈ X.val.2): massPlus P (16/(P.B:ℝ)) X.val.2 1 ≤ Real.exp (-( (P.B:ℝ)^2)⁻¹/2* separation Y X.val.1) * Real.exp 1 * massPlus P (26/(P.B:ℝ)) X.val.2 1:=by
 unfold massPlus; rw [mul_one,mul_one, ←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; have hv:=inSeat P Y X p; rw [show 16/(P.B:ℝ)=10/(P.B:ℝ)+6/(P.B:ℝ) from by ring, show 26/(P.B:ℝ)=20/(P.B:ℝ)+6/(P.B:ℝ) from by ring]; linarith only [hv]
abbrev heatMark (B:ℕ)(x:ℝ):ℝ:= taxIns B*(Real.exp 1*(Real.exp 16*x+x))
lemma stayPay(x:ℝ) (F:RegBudget n)(u:1≤ h)(p:∃ v:Scree.Hub n →ℝ,(∀ X, PressB P X (F X) h (v X)) ∧
     ∀ x':Seat n,(∑ X:Scree.Hub n, if x'∈X.val.2 then Ione.massPlus P (10/(P.B:ℝ)) X.val.2 (v X) else 0) ≤ x) (q:IncX (fun _=>False) F (raiseRate P) h 1)(v:52≤P.B)(hx:Real.exp (-(P.B:ℝ)/2)≤x) : ∃ K:Hz→ℝ,(∀ i,PressB P i (F i) h (K i))∧∀ y:Seat n,(∑ i:Hz,if y∈i.val.2 then massPlus P (16/(P.B:ℝ)) i.val.2 (K i) else 0) ≤ heatMark P.B x:=by
 obtain ⟨U,Q,Hx⟩:=p; obtain ⟨V,Z,Vw⟩:=q.weight
 let ζ:= Real.exp 16*x+x
 let X(i:Hz):= coverNumber P.B i.val.2; let zB:= (P.B:ℝ); let Λ(i:Hz):=if X i ≤ P.B then U i else V i
 have hU(i:Hz):= (Taxi.eraF _ _ (Q i) (zero_le_one.trans u) 1 (ping_f _ _)).grade
 have hV(i:Hz):= (Taxi.eraF _ _ (Z i) (zero_le_one.trans u) 1 (ping_f _ _)).grade
 have hB:zB≥52:=by unfold zB; exact_mod_cast v
 have ht:0<zB:=by linarith only [hB]
 have htXY(x:Seat n): ∀ i:Hz,x=i.val.1→x∈i.val.2:=fun i h=> h.symm ▸ i.property
 have hr(i):PressB P i (F i) h (Λ i):=by unfold Λ; split; exact Q i; exact stillRetreat P i _ (Z i)
 let R0:= P.supportExponent
 have hu(Y:Seat n):(∑ i:Hz,if Y=i.val.1 then massPlus P (26/(P.B:ℝ)) i.val.2 (Λ i) else 0) ≤ ζ:=by
    let G:=add_le_add (mul_le_mul_of_nonneg_left (Hx Y) (Real.exp_pos 16).le) ((mul_le_mul_of_nonneg_left (Vw Y) (Real.exp_pos (-(P.B:ℝ)/2)).le).trans ((mul_one _).le.trans hx)); refine le_trans ?_ G; rw [mul_sum,mul_sum,← sum_add_distrib]; apply sum_le_sum; intro i p; by_cases w:Y=i.val.1; swap
    · rw [if_neg w,if_neg w, mul_zero,add_zero]; refine mul_nonneg (Real.exp_pos _).le ?_; split; exact mul_nonneg (Real.exp_pos _).le (hU i); exact le_rfl
    rw [if_pos w,if_pos w,if_pos (htXY Y i w)]; let k:= X i; unfold Λ; split; next h=>
        apply le_add_of_le_of_nonneg _ (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hV i))); unfold massPlus; rw [←mul_assoc, ←Real.exp_add]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (hU i); have hQ: (16/zB)*(k:ℝ)≤16:=(mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) (show (0:ℝ)≤16/zB by positivity)).trans_eq (div_mul_cancel₀ _ ht.ne') -- tune
        change (R0+26/zB)*(k:ℝ)≤16+(R0+10/zB)*(k:ℝ); rw [show 26/zB=10/zB+16/zB from by ring,←add_assoc,add_mul]; linarith only [hQ]
    next h=>
       apply le_add_of_nonneg_of_le (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hU i))); unfold massPlus BudgetPoint.mass; rw [←mul_assoc,←Real.exp_add]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (hV i)
       have hk:zB≤ (k:ℝ):=Nat.cast_le.mpr (not_le.mp h |>.le); change (R0+26/zB)*(k:ℝ)≤ -zB/2+(R0+1)*(k:ℝ); have hq:=mul_le_mul_of_nonneg_right (show 26/zB ≤ 1/2 from (div_le_iff₀ ht).mpr (by linarith only [hB])) (Nat.cast_nonneg k : (0:ℝ)≤(k:ℝ)); linarith
 refine ⟨Λ,hr,fun x=>?_⟩; let X':=univ.filter (fun i:Hz=> x∈i.val.2); let Jw (i:Hz): Seat n:= i.val.1
 let μ(Z:Seat n):= Real.exp (-((P.B:ℝ)^2)⁻¹/2 * separation x Z); let C:= Real.exp 1
 have he:0≤ ζ:= add_nonneg (mul_nonneg (Real.exp_pos _).le ((Real.exp_pos _).le.trans hx)) ((Real.exp_pos _).le.trans hx)
 rw [←sum_filter, ←sum_fiberwise_of_maps_to (s:=X') (t:=univ) (g:=Jw) (fun _ _=> mem_univ _)]
 calc
    _ ≤ ∑ y:Seat n, μ y * (C*ζ):=sum_le_sum fun y _=>by
       let V(i:Hz):= massPlus P (26/(P.B:ℝ)) i.val.2 (Λ i)
       let W(i:Hz):= massPlus P (16/(P.B:ℝ)) i.val.2 (Λ i)
       let Y:= X'.filter (fun i=> Jw i=y)
       have hx(i:Hz):= (Taxi.eraF _ i (hr i) (zero_le_one.trans u) 1 (ping_f P i.val.2)).grade
       have hp(i:Hz)(p:i∈ Y):W i ≤ μ y * (C*V i):=by
          have hv:= warm_snap P i x (mem_filter.mp (mem_filter.mp p).1).2
          unfold massPlus at hv; rw [mul_one,mul_one] at hv
          rw [← (mem_filter.mp p).2]; unfold W V μ C Jw massPlus; rw [←mul_assoc (Real.exp 1),←mul_assoc]; refine (mul_le_mul_of_nonneg_right hv (hx i)).trans_eq ?_; ring
       apply (sum_le_sum hp).trans; rw [← mul_sum,←mul_sum]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
       apply le_trans _ (hu y); rw [←sum_filter]; exact sum_le_sum_of_subset_of_nonneg (fun i p=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2.symm⟩) (fun i _ _=>mul_nonneg (Real.exp_pos _).le (hx i))
    _ ≤ _:=by
       rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (placeExpense P.B P.B_pos x) (by unfold C; positivity)
end YM.CF.Ione
