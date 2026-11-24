import GaugeFieldConstruction.Hoon
import YM.CF.Chaff.Echo
import YM.CF.Yaw.Viv
import GaugeFieldConstruction.Plaid
import GaugeFieldConstruction.Corbie
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
variable {P:BudgetPoint}{K J B I:Type}[LinearOrder I][Fintype I] {h:ℝ}
variable (σ:I→ Seat n)(e:Vulcan I n)(x:Scree.Hub n)
variable (L:ℕ)(P:BudgetPoint)(h a b d r c:ℝ)
-- fz ℓ picks raw cost irrespective of legs table.Core reach & shape adjust.
def buyV(P:BudgetPoint)(d c:ℝ):Prop:=∀ i:ℕ,bSalt P i≤ c*Real.exp (d*(i:ℝ))
lemma adaptFees (d:ℝ)(v:0<d):∃ c:ℝ,0≤ c∧∀ (p:BudgetPoint),p.power=3→p.order=6→ buyV p d c:=by
 obtain ⟨V,o,h⟩:= Chaff.polyF (a:=d) (3+3*6) v; refine ⟨_,o,fun p u w i=>?_⟩; unfold bSalt preFoot; rw [u,w,←pow_mul,←pow_add]; exact h i
abbrev Zell (L:ℕ)(r:ℝ):ℝ:= Real.exp (r*Yaw.χ (ThermalH L))
lemma bounty (U:Linca P σ e)(w:buyV P d c): waiveP e P h ≤ Lite h e.val*e.won*(c* Branch.rent d e.seat):= by unfold waiveP base_E; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_left (w _) (mul_nonneg (costsE ..) U.stamp.micro.1)
variable (ha:2*d ≤ a)(hd:0≤d)(hr:0≤r)(gP:buyV P d c)(sP:r*2*Yaw.χ (ThermalH L) ≤ (P.B:ℝ)*d)(wZ:2*(ThermalH L*P.B)< (More n).val)
include ha hd hr gP sP wZ
lemma ωHeld (U:Linca P σ e)(v:0≤ c)(t: Finset I)(Y:x∈ marksY σ e L P t)(hb:0≤ b):b^t.card*(currency P.B r x.val.2)*(waiveP e P h) ≤ c*Zell L r*wageL a b h e:=by
 let z:= Zell L r; let A:= rent d e.seat; have hk:currency P.B r x.val.2 ≤ z*A:=by rw [(mem_filter.mp Y).2.2.2.1]; exact planet_Z _ _ _ hr hd U L wZ sP
 have hp:= bounty σ e P h d c U gP
 have hq: 0≤Lite h e.val*e.won:=mul_nonneg (costsE ..) U.stamp.micro.1
 have he: A*A≤ rent a e.seat:=by unfold A Branch.rent; rw [←Real.exp_add]; apply Real.exp_monotone; exact (by nlinarith [mul_le_mul_of_nonneg_right ha (show 0≤ (e.seat.card:ℝ) from by positivity)])
 have hu:= (mem_filter.mp Y).2; have hh:t.card=e.keys.length:= by rw [hu.1, List.toFinset_card_of_nodup (List.Nodup.of_map _ hu.2.1)] -- tune
 rw [hh]; let T:=b^e.keys.length; let R:= Lite h e.val*e.won
 have hz:0≤z:=(Real.exp_pos _).le; change T*_*_≤ _; have hT:0≤T:=pow_nonneg hb _
 calc
    _ ≤ T*(z*A)*(R*(c*A)):=mul_le_mul (mul_le_mul_of_nonneg_left hk hT) hp (base0_E σ e P h U _) (mul_nonneg hT (mul_nonneg hz (Real.exp_pos _).le))
    _ = T*z*R*c*(A*A):=by ring
    _ ≤ T*z*R*c* (rent a e.seat):=mul_le_mul_of_nonneg_left he (by change 0≤T*_*(Lite _ _*_) * _; positivity)
    _ = _:=by unfold wageL weightV Branch.rent; unfold T R z; ring
omit ha hd hr gP sP wZ
private lemma plateU (X:Finset (Scree.Hub n))(P:ℝ)(v:0≤P): ∑ i∈ X, exp_Plate X*P ≤ P:=by
 simp only [sum_const,nsmul_eq_mul,←mul_assoc,exp_Plate]; by_cases h:X=∅; simp [h,v]; have hs:(X.card:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)))
 rw [mul_inv_cancel₀ hs,one_mul]
abbrev Γcast (y:Seat n):= ∑ i:TiltI,c* Zell L r * costL a b h e (coy_Y L y P i)
lemma Γcasts (U:Linca P σ e)(v:0≤c)(hb:0≤b)(y:Seat n):0≤Γcast e L P h a b r c y:= sum_nonneg fun i _=>mul_nonneg (mul_nonneg v (Real.exp_pos _).le) (costsZ a b h _ hb U.stamp.micro.1 _)
-- accounting:
lemma Γy (U:Linca P σ e)(v:0≤c)(hb:0≤b)(y:Seat n)(w:y∈ SpacePad L P σ e): c*Zell L r*wageL a b h e ≤ c*Zell L r*costL a b h e y+Γcast e L P h a b r c y:=by
 let T:=Γcast e L P h a b r c y; let V:=c*Zell L r; have hv:0≤V:=mul_nonneg v (Real.exp_pos _).le; have ht(z:Seat n): 0≤ V*costL a b h e z:=mul_nonneg hv (costsZ _ _ _ _ hb U.stamp.micro.1 _)
 unfold SpacePad at w
 cases mem_union.mp w with
 | inl w=> rw [show wageL a b h e = costL a b h e y from (by unfold wageL costL bil; rw [if_pos w])]; exact le_add_of_nonneg_right (Γcasts _ _ _ _ h a b r c U v hb _)
 | inr w=>
    split at w; contradiction -- tune empt w
    generalize hg:e.keys=l at w; split at w
    next k=>
       obtain ⟨j,t,g⟩:= Finset.mem_image.mp w; have he: coy_Y L y P j=σ k:= by unfold coy_Y; rw [←g,Atlas_Y]; rw [sub_add_cancel]
       refine le_trans ?_ (le_add_of_nonneg_left (ht _)); have hx: V * costL a b h e (coy_Y L y P j) ≤ T:= single_le_sum (f:=fun i=> V * costL a b h e (coy_Y L y P i)) (fun _ _=> ht _) (mem_univ j); refine le_trans (Eq.le ?_) hx; rw [he, costL,bil,if_pos (U.stamp.port k (by simp [hg]))]; rfl
    simp at w
local notation "Tκ" T:max=> marksY σ e L P T
local notation "Vℓ"=> c*Zell L r
abbrev pinH0 (x:Scree.Hub n)(d:ℝ)(k:ℕ):=currency k d x.val.2
include ha hd hr gP sP wZ
lemma whimP (U:Linca P σ e)(v:0≤c)(T:Finset I)(y:Seat n)(hb:0≤b): 
 b^T.card * (∑ x∈ univ.filter (fun x:Scree.Hub n=>y∈ x.val.2),pinH0 x r P.B * Lex_B σ e x L P T h) ≤ c*Zell L r *costL a b h e y+Γcast e L P h a b r c y:=by
 let S:=Tκ T; let Y:=univ.filter (fun x:Scree.Hub n=>y∈ x.val.2); let W:=Vℓ*costL a b h e y+Γcast e L P h a b r c y; have hx:0≤W:= add_nonneg (mul_nonneg (mul_nonneg v (Real.exp_pos _).le) (costsZ a b h e hb U.stamp.micro.1 _)) (Γcasts _ _ _ _ _ _ _ _ _ U v hb y)
 unfold Lex_B; rw [mul_sum]; simp_rw [mul_ite,mul_zero]; rw [←sum_filter]
 let X:=Y.filter (fun u=> u∈ S); have hy(x)(t:x∈ X): b^T.card * (pinH0 x r P.B*(exp_Plate S* waiveP e P h)) ≤exp_Plate S*W:=by
    obtain ⟨s,Y⟩:=mem_filter.mp t; let H:=ωHeld _ _ x L P h a b d r c ha hd hr gP sP wZ U v T Y hb; have hH:= H.trans (Γy _ _ _ _ _ _ _ _ _ U v hb y (((mem_filter.mp Y).2.2.2.1) ▸ (mem_filter.mp s).2))
    refine le_trans (Eq.le ?_) (mul_le_mul_of_nonneg_left hH (show 0≤exp_Plate S by unfold exp_Plate; positivity)); unfold pinH0; ring
 refine (sum_le_sum hy).trans ((sum_le_sum_of_subset_of_nonneg (show X⊆ S from fun i q=> (mem_filter.mp q).2) (fun i _ _=>mul_nonneg (by unfold exp_Plate; positivity) hx)).trans (plateU _ _ hx))
local notation "ξ" T:max x:max=> Lex_B σ e x L P T h
lemma spool (U:Linca P σ e)(v:0≤c)(y:Seat n)(hb:0≤b): 
 (∑ T∈realm_C σ,b^T.card * (∑ x∈ univ.filter (fun x:Scree.Hub n=>y∈ x.val.2),pinH0 x r P.B * ξ T x))≤ Vℓ*costL a b h e y+Γcast e L P h a b r c y:=by
 let A:=realm_C σ; let X:=e.keys.toFinset
 let Y:=univ.filter (fun x:Scree.Hub n=> y∈x.val.2); let TY(t:Finset I):= b^t.card * (∑ x∈ Y,pinH0 x r P.B*ξ t x)
 have hz(t:Finset I)(p:t≠X): TY t=0:=by unfold TY; rw [sum_eq_zero ?_,mul_zero]; intro i v; rw [Lex_B,if_neg (fun w=>p ((mem_filter.mp w).2.1)),mul_zero]
 change ∑ i∈A,TY i≤_
 by_cases ht:X∈ A; · rw [sum_eq_single X (fun i t v=> hz i v) (fun p=> (p ht).elim)]; exact whimP _ _ _ _ _ _ _ _ _ _ ha hd hr gP sP wZ U v X y hb
 rw [sum_eq_zero fun i t=>hz i (ne_of_mem_of_not_mem t ht)]
 exact add_nonneg (mul_nonneg (mul_nonneg v (Real.exp_pos _).le) (costsZ _ _ _ e hb U.stamp.micro.1 _)) (Γcasts _ _ _ _ _ _ _ _ _ U v hb y)
variable (Q:Boke n I)
def Tours_Q (y:Seat n)(F:Finset I→ Scree.Hub n→ℝ):ℝ:=∑ T∈realm_C σ,b^T.card* (∑ x∈univ.filter (fun x:Scree.Hub n=>y∈ x.val.2),pinH0 x r P.B * F T x)
def BigE (L:ℕ)(c r M:ℝ):= c*Zell L r * M+(Fintype.card TiltI:ℝ)*(c*Zell L r * M)
lemma Tours_e (U:CostP σ P Q)(v:0≤ c)(hb:0≤b)(M:ℝ)(y:Seat n)(hx: MajorZ a b h Q M): Tours_Q σ P b r y (entryW σ L P Q h) ≤ BigE L c r M:=by
 let Y:=univ.filter (fun x:Scree.Hub n=>y∈x.val.2); let G(e:Vulcan I n)(T:Finset I):=b^T.card*(∑ x∈Y,pinH0 x r P.B*Lex_B σ e x L P T h)
 have he (Q:Boke n I): Tours_Q σ P b r y (entryW σ L P Q h)=Lee Q fun e=> ∑ T∈realm_C σ, G e T:=by
    induction Q with
    | nil=> simp [Tours_Q,entryW,Lee]
    | cons i Q w=> unfold Tours_Q entryW; unfold Tours_Q entryW at w; simp only [consA,mul_add,sum_add_distrib]; rw [w]
 rw [he]; refine le_trans (lea_p _ _ (fun e=> Vℓ*costL a b h e y+Γcast e L P h a b r c y) (fun i g=> spool σ i L P h a b d r c ha hd hr gP sP wZ (U _ g) v y hb)) ?_
 rw [lea_pair]; have ht(t): Lee Q (fun e=> Vℓ*costL a b h e t) ≤ Vℓ*M:=(lea_scale ..).le.trans (mul_le_mul_of_nonneg_left (hx t) (mul_nonneg v (Real.exp_pos _).le))
 refine add_le_add (ht _) ?_
 unfold Γcast; rw [←lea_sum]; exact (sum_le_sum (fun i _=>ht (coy_Y L y P i))).trans_eq (by simp) -- tune
#print axioms Tours_e
end MastTin
end YM.CF.XGarden
end
