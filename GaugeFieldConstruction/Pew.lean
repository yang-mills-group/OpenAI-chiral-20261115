import GaugeFieldConstruction.Elastic
/-!
# Taylor response on χ legs, incl single-parameter remainder	
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
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
variable {c f:Side}{G:Ratio c f}{M:Male}{b:Bool}{U σ:ℝ}
-- Witness maps
abbrev Toy (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(r:ℕ) : Dove :=fun i=> ChipY M G A b i r
abbrev Fume (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(r:ℕ) : Dove:=fun i x=>errorY M G A b i x r
abbrev Stove (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(r:ℕ):=streamsW M b (Toy M G A b r)
abbrev Lobe (M:Male)(G:Ratio c f)(A:Site f)(b:Bool)(r:ℕ):=streamsW M b (Fume M G A b r)
variable (p:Honed G.count M b U σ)(h:0<U)(u:0<σ)(e:Odd G.count.val) (A:Site f)
include p h u e
local notation "ℳ"=> BudgetX G σ U
local notation "ρ"=> αN G.count
lemma TicketW (x:Cover)(i:Kt)(n r:ℕ)(v:n≤3)(k:r<3): SumBudget (fun v:Lane × Mill=> wagN n v.2*‖journey M b (Toy M G A b r) x i v.1 v.2‖) (EraM b n G U σ r *ρ^r* Ladder x^r) := by
 let D:=BudgetX G σ U n*ρ^r*Ladder x^r; have he:= Bux_pos G U σ h u n; have hp:= ladE x; have hw:=α_pos G.count; have hD:0≤D:=by unfold D; positivity
 have hx (i y):=GoaChip p h u e A i n r v k (x+y)
 apply SBmono (geo_coin M b _ x i n r D hD _); · exact le_of_eq (by unfold EraM Grove D; ring)
 intro j y; apply SBmono (hx j y); unfold D; rw [mul_assoc (ℳ n *_)]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [←mul_pow]; exact pow_le_pow_left₀ (zero_le_one.trans (ladE _)) (wl_up ..) _
lemma EW (x:Cover)(i:Kt)(n r:ℕ)(v:n≤3)(k:r≤3): SumBudget (fun v: Lane × Mill=> wagN n v.2*‖journey M b (Fume M G A b r) x i v.1 v.2‖) (12*EraM b n G U σ 3*ρ^r* Ladder x^3):= by -- same
 let D:=12*BudgetX G σ U n*ρ^r*Ladder x^3; have he:= Bux_pos G U σ h u n; have hp:= ladE x; have hw:=α_pos G.count; have hD:0≤D:=by unfold D; positivity
 have hx (i y):=GoaErr p h u e A i n r v k (x+y)
 apply SBmono (geo_coin M b _ x i n 3 D hD _); · exact le_of_eq (by unfold EraM Grove D; ring)
 intro j y; apply SBmono (hx j y); unfold D; rw [mul_assoc (12*ℳ n * _) (Ladder x^3)]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [←mul_pow]; exact pow_le_pow_left₀ (zero_le_one.trans (ladE _)) (wl_up ..) _
lemma ticketY (x:Cover)(i:Kt)(n r:ℕ)(v:n≤3)(k:r<3): chime (wagN n) (Stove M G A b r x i) (EraM b n G U σ r *ρ^r* Ladder x^r) :=TicketX M b _ _ _ _ (TicketW p h u e A x i n r v k) -- tune
lemma chimeE (x:Cover)(i:Kt)(n r:ℕ)(v:n≤3)(k:r≤3): chime (wagN n) (Lobe M G A b r x i) (12*EraM b n G U σ 3*ρ^r* Ladder x^3):= TicketX M b _ _ _ _ (EW p h u e A x i n r v k) -- tune
lemma hiker (x:Cover)(i:Kt)(r:ℕ)(v:r<3): Lobe M G A b r x i= Stove M G A b r x i+Lobe M G A b (r+1) x i:=by
 funext j; let Y:= Toy M G A b r; let L:=Fume M G A b (r+1); let D:= Fume M G A b r
 have hx: D=Y+L :=by
    funext a t j; change _; let F:=polynomialY M G A b a (r+1); change _=Y a t j+(Ytab _ G _ _ _ t j - F t j); rw [show F= ChipY M G A b a r+polynomialY _ G _ _ _ r from chip_more a r v]; change _ = Y a t j + (_-(Y a t j+polynomialY M G A b a r t j)); change Ytab M G _ _ _ _ _ - _= _; abel -- likely fails due unfolding
 have hp:= (sum_coin M b Y x i 3 (TicketW p h u e _ _ _ _ _ le_rfl v)).prod_symm.prod_factor j |>.of_norm -- tune
 have he:= (sum_coin M b L x i 3 (EW p h u e _ x i 3 (r+1) le_rfl v)).prod_symm.prod_factor j |>.of_norm
 have ha(y:Lane): journey M b D x i y j= journey M b Y x i y j+ journey M b L x i y j:=by rw [hx]; unfold journey; simp only [Pi.add_apply,mul_add]
 change ∑' k,journey M b D x i k j=(∑' k,journey M b Y x i k j)+ (∑' k,journey M b L x i k j); simp_rw [ha]; exact hp.tsum_add he
lemma ReadyF (x:Cover)(i:Kt)(m:ℕ)(u':m ≤3): Sister M G b A x i=Lobe M G A b m x i + ∑ k∈ range m, Stove M G A b k x i:=by
 induction m with
 | zero=> rw [range_zero,sum_empty,add_zero]; unfold Lobe Fume; have he : (fun (i:Kt) x=> errorY M G A b i x 0)=sill M G b A:=funext₂ (fun i x=>by change Ytab M G A b i x-0= _; exact sub_zero _); rw [he]; -- tune
 | succ m ih=> rw [ih (by omega),hiker p h u e A x i m u',sum_range_succ]; abel
-- tidy universal wages independent both Rs: any finite convert constants.
omit p h u e
lemma βE : ∀ (b:Bool)(n k:ℕ)(G:Ratio c f)(u t:ℝ), EraM b n G u t k = (Fintype.card Kt:ℝ)*(Fintype.card Kt:ℝ)*PawnCharge b k* widthCost t n * 9^n*u*wool G.count []:=by intro i n k G u t; unfold EraM Grove BudgetX budT; ring
lemma legWay (k:ℕ) (b:Bool): ∃ B U σ:ℝ, 1≤B ∧0<U∧0<σ∧∀{c f:Side}(G:Ratio c f)(e:Odd G.count.val), (∀ M:Male,Honed G.count M b U σ) ∧ ∀ j r:ℕ,j≤ k → r ≤k → EraM b j G U σ r ≤ B*wool G.count []:=by
 obtain ⟨σ,C,hp,hC,H⟩:= wool_mode b 4 3 (by decide)
 let F(i j:ℕ) := (Fintype.card Kt:ℝ)*(Fintype.card Kt:ℝ)*PawnCharge b j * widthCost σ i * 9^i * C; let K:= range (k+1); let B:=∑ i∈K,∑ j∈K,F i j; have hh(i j):0 ≤ F i j:=by unfold F; have hx:= PC_pos (n:=j) b; have hv:=widthCost_ge hp i; positivity
 refine ⟨B+1,C,σ,(le_add_of_nonneg_left (sum_nonneg fun i _=>sum_nonneg fun j _=> hh i j)),hC,hp,fun G p=>⟨fun M r a j D u=> H G.count M.val p M.property r a j D u,fun i j v u=>?_⟩⟩
 have he(i:ℕ)(v:i≤k):i∈K:=mem_range.mpr (Nat.lt_add_one_iff.mpr v)
 rw [βE]; apply mul_le_mul_of_nonneg_right _ (wool_pos ..); change F i j ≤ B+1; exact (single_le_sum (f:=F i) (fun j _=> hh i j) (he j u)).trans ((single_le_sum (f:=fun i=> ∑ j∈K,F i j) (fun i _=> sum_nonneg fun j _=>hh i j) (he i v)).trans (le_add_of_nonneg_right zero_le_one))
end Boom
end YM.CF.TableF
end
