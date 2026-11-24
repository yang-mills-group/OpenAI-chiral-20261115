import YM.SU5.Exchange.Reg.Lift

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
variable (τ:Ids n) {v:Aura n→ℝ}(qE:Sym_a E)(p:Turf E)(s_:0≤h) (t:∀ i:Aura n, Vow.Medal P i.val ∅ (E i) h (v i))


/-- If a portion of an already certified Reg array agrees with another,
 better-budgeted Reg array on the large Hubs, while arbitrary small hubs are present,
 pay the higher rate on the actual array. -/
lemma keep_large_hubs (N : ℕ)(U : Sweep n → Prop)(E F : RegBudget n)
 (u : IncX U E P h a) (w : IncX Utrue F (raiseRate P) h b) (p : 1 ≤ h)
 (g : ∀ i:Scree.Hub n,N < coverNumber P.B i.val.2 → E i=F i) :
   IncX U E (raiseRate P) h (Real.exp N * a + b) := by
 obtain ⟨f,hf,f'⟩:= u.weight; obtain ⟨G,hG,G'⟩:= w.weight
 have h0 : 0 ≤ h:= zero_le_one.trans p
 let S(i:Scree.Hub n):= if N < coverNumber P.B i.val.2 then G i else f i
 refine ⟨⟨S, fun i => ?_, fun q=> ?_⟩, u.face⟩
 · unfold S
   split
   next l=> rw [g i l]; exact hG i
   exact raisePress P (hf _)
 apply le_trans _ (add_le_add (mul_le_mul_of_nonneg_left (f' q) (Real.exp_pos _).le) (G' q))
 rw [mul_sum,←sum_add_distrib]
 refine sum_le_sum fun i _=>?_
 have hx:= (Taxi.eraF _ i (hf i) h0 1 (ping_f P i.val.2)).grade
 let P':=raiseRate P
 have hy:= (Taxi.eraF _ i (hG i) h0 1 (ping_f P' i.val.2)).grade
 by_cases c:q=i.val.1
 · simp only [c, ↓reduceIte]
   unfold S
   split
   · exact le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hx))
   next l=>
     apply le_add_of_le_of_nonneg _ (mul_nonneg (Real.exp_pos _).le hy)
     let X:ℝ:= coverNumber P.B i.val.2
     change Real.exp ((P.supportExponent+1)*X)*f i ≤ Real.exp (↑N)*(Real.exp (P.supportExponent*X)*f i)
     rw [←mul_assoc,←Real.exp_add]; gcongr
     have hx' : X ≤ N:=Nat.cast_le.mpr (le_of_not_gt l)
     linarith
 simp only [if_neg c]; simp
end YM.CF.Ione
