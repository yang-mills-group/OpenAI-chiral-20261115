import YM.CF.Lor.Count
import YM.CF.Lor.Cred
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' D D' κ τ τ' :ℝ}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
variable{S :StepData c f}{T:Tube G₅ S}{U:E→ Monk SU.group S}{x β:ℝ}(A O:Stores S)(s:Signed)
variable {w K':BudgetPoint}{τ σ τ' B C K C' B' K' Q θ α y H z:ℝ}{P P':BudgetPoint}{x':E}
local notation "Θ₀"=> (turnStore s A).costs
local notation "Γ₀"=> traceZ (turnStore s A).flags
local notation "W" =>fun i:E=> (U i).sent x T q θ l β
local notation "V"=>fun i:E=> (U i).V
local notation "t"=>P.threshold
local notation "v"=> P'.threshold
local notation "J"=> pull s 0 ∘ W
local notation "I"=> pull s 0 ∘ V
local notation "R" => Stores.till x

local notation "L"=> ((K*t^3*C+K*t^4*C) +(K'*v^3*C'+K'*v^4*C'))
local notation "Z"=> (H*z +(K*t^2*B + K'*v^2*B'))
lemma fist (p:CardX t τ J x' Θ₀ n q K 0)(h:CardX v τ' I x' Γ₀ n q K' 0) (hp: T.up.Bounds T.high τ C B)(hx:T.down.Bounds T.low τ' C' B')(u:∀ i∉Γ₀, Pressure.toll (I x') i ≤ v)(hV:∀ i,(U i).key=A) (i:Site f ⊕ Site c): Allows n (fun y=>folkK T x (U y) s q θ l β P P' i) x' L:=by
 have P1 : 0 ≤ K'*v^3*C'+K'*v^4*C':=(payNeg (((lampM h (barn hx.three R) hx.width P'.threshold_pos P'.threshold_le (by decide) (0:Site c)).2 u).add ((lampM h (barn hx.four R) hx.width P'.threshold_pos P'.threshold_le (by decide) (0:Site c)).2 u))).nonneg
 cases i with
 | inl i=> unfold folkK; simp only [Sum.elim_inl,hV]; exact (((lampM p (barn hp.three R) hp.width P.threshold_pos P.threshold_le (by decide) i).1).add (lampM p (barn hp.four R) hp.width P.threshold_pos P.threshold_le (by decide) i).1).mono (le_add_of_nonneg_right P1)
 | inr i=> have hf:0 ≤K*t^3*C+K*t^4*C:=add_nonneg (lampM p (barn hp.three R) hp.width P.threshold_pos P.threshold_le (by decide) (0:Site f)).1.nonneg (lampM p (barn hp.four R) hp.width P.threshold_pos P.threshold_le (by decide) (0:Site f)).1.nonneg
           unfold folkK; simp only [Sum.elim_inr,hV]; exact (payNeg (((lampM h (barn hx.three (R/S.patch.L.val)) hx.width P'.threshold_pos P'.threshold_le (by decide) i).2 u).add ((lampM h (barn hx.four (R/S.patch.L.val)) hx.width P'.threshold_pos P'.threshold_le (by decide) i).2 u))).mono (le_add_of_nonneg_left hf)
local notation "E₀"=> fun i' x''=> Esti.king Γ₀ T.down T.low R S.patch.L.val v ((pull s 0 ∘ V) x'') i'
lemma palmC (p:CardX t τ J x' Θ₀ n q K 0)(h:CardX v τ' I x' Γ₀ n q K' 0) (hp: T.up.Bounds T.high τ C B)(hx:T.down.Bounds T.low τ' C' B')(u:∀ i∉Γ₀, Pressure.toll (I x') i ≤ v) (j:Along S)(v':0≤z)(he:|α|≤H)(hy:∀i: Cell c,Allows n (E₀ i) x' z): Allows n (fun y=>heatR T (W y) (V y) s A q P P' x α j) x' Z:=by
 let hL(i:Site f):=(lampM p (barn hp.two R) hp.width P.threshold_pos P.threshold_le (by decide) i).1; let hC(i:Site c):=(lampM h (barn hx.two (R/S.patch.L.val)) hx.width P'.threshold_pos P'.threshold_le (by decide) i).2 u; have hl:0 ≤ K*t^2*B:=(hL 0).nonneg; have hh:0 ≤ K'*v^2*B':=(hC 0).nonneg; have ht:0 ≤ H*z:=mul_nonneg ((abs_nonneg _).trans he) v'; have hZ:0 ≤Z:=by positivity
 rcases j with (i|i|i|i)|(i|i)
 · exact allows_const _ (norm_zero.le.trans hZ)
 · exact allows_const _ (norm_zero.le.trans hZ)
 · refine ((hy i).smul (-α)).mono ?_; rw [abs_neg]; exact (mul_le_mul_of_nonneg_right he v').trans (le_add_of_nonneg_right (add_nonneg hl hh))
 · exact allows_const _ (norm_zero.le.trans hZ)
 · exact (hL i).mono ((le_add_of_nonneg_right hh).trans (le_add_of_nonneg_left ht))
 exact (payNeg (hC i)).mono ((le_add_of_nonneg_left hl).trans (le_add_of_nonneg_left ht))
section grade
variable (j:ℕ)
local notation "g"=> ((about S.patch.L 0*Esti.latticeFieldEstimates O j x:ℕ):ℝ)
lemma scope_p (p:CardX t τ J x' Θ₀ n q K 0)(h:CardX v τ' I x' Γ₀ n q K' 0) (hp: T.up.Bounds T.high τ C B)(hx:T.down.Bounds T.low τ' C' B')(u:∀ i∉Γ₀, Pressure.toll (I x') i ≤ v)(hV:∀ i,(U i).key=A) : Allows n (fun y=> ∑ i∈lyn x s O j,folkK T x (U y) s q θ l β P P' i) x' (g* L):=by
 refine (summed _ _ fun i _=> fist A s p h hp hx u hV i).mono (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (blade ..)) (fist A s p h hp hx u hV (.inr (0:Site c))).nonneg)
lemma sauce (p:CardX t τ J x' Θ₀ n q K 0)(h:CardX v τ' I x' Γ₀ n q K' 0) (hp: T.up.Bounds T.high τ C B)(hx:T.down.Bounds T.low τ' C' B')(u:∀ i∉Γ₀, Pressure.toll (I x') i ≤ v) (v':0≤z)(he:|α|≤H)(hZ:∀ i:Cell c,Allows n (E₀ i) x' z): Allows n (fun y=>∑ i∈strum x s O j,heatR T (W y) (V y) s A q P P' x α i) x' (g*Z):= (summed _ _ fun i _=> palmC A s p h hp hx u i v' he hZ).mono (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (branchZ ..)) (palmC A s p h hp hx u (.inr (.inr (0: Site c))) v' he hZ).nonneg)
end grade
end YM.CF.Lor
