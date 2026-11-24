import GaugeFieldConstruction.Tango
/-!
# Near Loom relative local bounds. Use no bigger Paw cash.
-/
set_option autoImplicit false
set_option maxHeartbeats 40000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f c:Side}{σ B U C:ℝ} {G:Ratio c f}{M:Male}{b:Bool}{o:Skye.Seat f}{Q:Op (Single f)}{h:ℝ}{k r:ℕ}
variable (p:Honed G.count M b U σ)(u:0<U)(t:0<σ) (e:Odd G.count.val)(A:Site f)
-- charter YeT from proof booklet
local notation "Cc"=> BudgetX G σ U
local notation "ρ"=> αN G.count
include p u t e
lemma story (i: Kt)(n r:ℕ)(g:n ≤ 3)(v:r≤3) (x d:Cover)(c:ℝ)(hC:Ladder x ≤ c)(hc:ρ*c≤1) : chime (wagN n) (errorY M G A b i (x+d) r) (12*BudgetX G σ U n *ρ^r*c^r *Ladder d ^ 3):=by
 apply SBwork (fun i=>mul_nonneg (zero_le_one.trans (wagE ..)) (norm_nonneg _)); intro J
 let K:= Ytab M G A b i; let t':= Ytax (wagN n) J; let Z:=Y_Goose p u t e J A i n g; let P:=DignityY (wagN n) (fun _=>zero_le_one.trans (wagE ..)) J; let Y:=x+d; let Q:ℝ:= lateral Y; have hQ:0 ≤Q:=Nat.cast_nonneg _; let f:=Ladder d; have hp:1 ≤ f:= ladE _; have hv:0<BudgetX G σ U n:=Bux_pos G U σ u t _; have hs:0 < c:=(zero_lt_one.trans_le (ladE _)).trans_le hC
 have hr:0<ρ:=α_pos _; change t' ((K-wheelK K r) Y) ≤ _
 have hx: Q ≤ c*f:= (le_add_of_nonneg_left zero_le_one).trans ((wl_up x d).trans (mul_le_mul_of_nonneg_right hC (zero_le_one.trans hp)))
 let Y':=ρ*c; have hy:0 ≤ Y':=(mul_pos hr hs).le
 by_cases h:ρ*Q≤1
 · have hg: Q^r ≤ c^r* f^3:= (pow_le_pow_left₀ hQ hx r).trans (by rw [mul_pow]; gcongr) -- tune
   apply (Goa_cost P K _ _ r v Y (Z.lower v) h).trans;
   change 8*_ *ρ^r*Q^r ≤12*_ *ρ^r*c^r*f^3; rw [mul_assoc (12*_*_) (c^r)]; gcongr <;> norm_num
 have hg: 1 ≤ ρ*Q:=(not_le.mp h).le; let Lr:=ρ*Q; let D:=Cc n
 have ht: t' (K Y)≤ 8*D*Lr^3:= (Goose.leap P Z Y).trans (by
    calc _ ≤ D*(2*Lr)^3:=by change _*(1+Lr)^_≤ _; have hz:Lr≥1:=hg; gcongr; linarith
         _ = _:=by ring)
 apply (P.sub (K Y) _).trans; apply (add_le_add ht (Goa_far P K _ _ r v Y (Z.lower v) hg)).trans;
 have hf:Lr^3 ≤ (ρ*c)^r*f^3:=by
    calc _ ≤ (ρ * (c*f))^3:=by unfold Lr; change _≤_; gcongr -- tune
         _ = Y'^3*f^3:=by unfold Y'; ring
         _ ≤ _:= by exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hy hc v) (by positivity)
 change 8*D*Lr^3+3*D*Lr^3 ≤ 12*D*ρ^r*c^r*f^3; rw [show 12*D*ρ^r*c^r*f^3=12*D*((ρ*c)^r*f^3) from (by rw [mul_pow]; ring)]; have hm:0≤D*Lr^3:= mul_nonneg hv.le (pow_nonneg (zero_le_one.trans hg) _); linarith only [mul_le_mul_of_nonneg_left hf hv.le,hm]
local notation "Uf"=> M
lemma score (x:Cover) (i:Kt)(c:ℝ)(hC:Ladder x ≤c)(hc:ρ*c ≤1)(n r:ℕ)(g:n ≤ 3)(v:r ≤3): chime (wagN n) (Lobe M G A b r x i) (12 * EraM b n G U σ 3 *ρ^r * c^r) := by
 let Y:= Fume M G A b r
 have he: 0 ≤ Cc n:= (Bux_pos G U σ u t n).le; have hz:0 ≤ρ:= (α_pos _).le; have hr:1≤ c:= (ladE x).trans hC; let B:= Cc n
 apply TicketX M b Y x i n; apply SBmono (geo_coin M b Y _ i n 3 (12* B *ρ^r*c^r) (by unfold B; positivity) (fun j d=> story p u t e A j n r g v x d c hC hc)) (le_of_eq _); unfold EraM Grove B; ring
lemma RankingB (i:Kt)(x:Cover)(c:ℝ)(hC:Ladder x ≤ c)(p0:∀ j ≤3,∀ k ≤3,EraM b j G U σ k ≤ B): Upk (fun j=> Stove M G A b j x i) (Sister M G b A x i) B c ρ:=by
 let Q:= Sister M G b A x i; have he:0<B:=(EP_V b 0 G U σ 0 u t).trans_le (p0 _ (by decide) _ (by decide)); have ht:0<ρ:=α_pos _; have hp:(lateral x:ℝ) ≤ c:=(le_add_of_nonneg_left zero_le_one).trans hC
 constructor
 · apply SBmono (SB_paws p u t A x i 0); simpa using p0 0 (by decide) 0 (by decide)
 · apply SBmono (SB_paws p u t A x i 3); unfold usingF; gcongr; exact p0 3 le_rfl 3 le_rfl -- tune
 · intro r h n k; apply SBmono (ticketY p u t e A x i n r k (by omega)); have hr:= zero_le_one.trans (ladE x); gcongr; exact p0 n k r (by omega)
 intro c' r h n k; rw [show Q- _ =Lobe M G A b r x i from (by unfold Q; rw [ReadyF p u t e A x i r h,add_sub_cancel_right])]; apply SBmono (score p u t e A x i c hC c' n r k h); have hz:0≤ c:= (zero_le_one.trans (ladE ..)).trans hC; gcongr; exact p0 n k 3 le_rfl
end Boom
end YM.CF.TableF
end
