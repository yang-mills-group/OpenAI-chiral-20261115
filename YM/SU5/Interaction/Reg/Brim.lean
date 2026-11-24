import YM.SU5.Interaction.Reg.Lift
/-! Convert to per-seat COVER-incidence cost. Use period independent decay/profile from Thirst/Scatter with scale B². -/
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
open Beau Next.Rank.Thirst -- Thirst namespace adjust
local notation "Hz"=> Scree.Hub n
local notation "α"=> P.supportExponent


-- receipt in strict the construction notes reception (through order six of p). Does not ask for p^*=3 power tariff.
structure LocalHead (b:ℝ)(E:RegBudget n)(h v:ℝ) : Prop where
  weight:∃ z: Scree.Hub n → ℝ,(∀ i,PressB P i (head_L E i) h (z i)) ∧ ∀ x:Seat n,(∑ i:Hz,if x∈i.val.2 then Real.exp (b*coverNumber P.B i.val.2)*z i else 0) ≤ v

lemma incidenceAt (E:RegBudget n)(w:0≤h)(u:IncX (fun _=>False) (head_L E) (midRate P 20 (by norm_num)) h a) : LocalHead P (α+10/(P.B:ℝ)) E h (wilt (P.B^2)*a):=by
 obtain ⟨v,z,t⟩:=u.weight; have hz(i: Scree.Hub n):0 ≤ v i:= grit_p _ (z i) w
 let v₀:= fun (i: Scree.Hub n)=>(head_L E i)
 let M:=midRate P 20 (by norm_num)
 let S:= fun (i:Hz)=> M.mass i.val.2 (v i)
 let q:=P.B^2
 have he:0<q:= pow_pos P.B_pos _
 have hB:0<(P.B:ℝ):=by exact_mod_cast P.B_pos
 refine ⟨⟨v,fun i=>?_,fun i=>?_ ⟩⟩
 · have t:= editPress (z i) _ P.exponent_pos; exact t
 let f(x:Seat n):=(separation x i/(8*q):ℕ)
 let F(x:Seat n):=Real.exp (-((f x:ℕ):ℝ))
 have hF(x:Seat n)(j: Hz):0≤S j:=mul_nonneg (Real.exp_pos _).le (hz _)
 have hh:a ≥0:=le_trans (Finset.sum_nonneg (f:=fun j:Hz=> if i=j.val.1 then S j else 0) (fun j _=>by split; exact hF i j; exact le_rfl)) (t i)
 calc
    _ ≤ ∑ j:Hz,∑ k:Skye.Seat n, F k*(if k=j.val.1 then S j else 0):=by
       refine Finset.sum_le_sum fun j _=>?_ ; apply le_trans _ (single_le_sum (fun k _=>mul_nonneg (show 0 ≤ F k from (Real.exp_pos _).le) (show 0 ≤ (if k=j.val.1 then S j else (0:ℝ)) from (by split; exact hF k j; exact le_rfl))) (mem_univ j.val.1)); split; next p=>
            rw [if_pos rfl]; let v':=coverNumber P.B j.val.2
            have hv:(P.B * (f j.val.1)) ≤ v':=by
               have h:= book_site P.B P.B_pos _ j.property p; have h':f j.val.1 ≤ v'/P.B:=by unfold f q; rw [pow_two,←mul_assoc,←Nat.div_div_eq_div_mul]; exact Nat.div_le_div_right h
               rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le P.B_pos).mp h'
            unfold F S BudgetPoint.mass; rw [←mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (hz _); apply Real.exp_monotone
            change (α+10 / (P.B:ℝ))*(v':ℝ) ≤ -((f j.val.1:ℕ):ℝ)+(α+20/(P.B:ℝ))*(v':ℝ)
            have y:(f j.val.1:ℝ)≤ (v':ℝ)/(P.B:ℝ):= by apply (le_div_iff₀ hB).2; rw [mul_comm]; exact_mod_cast hv
            have vZ:0 ≤ (v':ℝ)/(P.B:ℝ):=by positivity
            rw [add_mul,add_mul, div_mul_eq_mul_div,div_mul_eq_mul_div]; simp_rw [mul_div_assoc]; linarith only [y,vZ] -- normalize x*v'/B
       next => rw [if_pos rfl]; exact mul_nonneg (Real.exp_pos _).le (hF i _)
    _ ≤ ∑ k:Skye.Seat n,F k*a:=by
       rw [sum_comm]; apply sum_le_sum; intro k _; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (t k) (Real.exp_pos _).le
    _ ≤ _:=by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (range_wilt i q he) hh

lemma LocalHead.raise {E:RegBudget n} (p:LocalHead P b E h a)(u:a≤c): LocalHead P b E h c:=by obtain ⟨z,t,v⟩:=p.weight; exact ⟨⟨z,t,fun i=>(v i).trans u⟩⟩
end YM.CF.Ione
