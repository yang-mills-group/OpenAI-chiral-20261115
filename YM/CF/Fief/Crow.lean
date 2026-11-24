import YM.CF.Fief.Poe
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
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
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{k n j d:ℕ}
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable{G S x e T}
variable(A:Muster G S x e T)
open Vol YM.Push.AbsoluteSums
open ConnectedActivityE6.Raw
variable (U: Monk SU.group S)
variable{s:ℝ}{l v:ℕ}
-- wheel theta debt.R
variable {a b c p:ℝ}{r:ℕ}
local notation "L₁"=> Domain N B
local notation "μ_"=> Domain P B
variable (v v' w w' Q Q':ℝ)(k':ℕ)
def pot_c (L: Bit (Site (Domain N B))) := ∑ s:Signed,((∑ i,ringF A s k' Q v w L i) + ∑ i,ringC A s k' Q Q' v' w' L i)
section
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{x₀:E}(Y:E→ Monk SU.group S)
local notation "P_" s=> fun x':E=> pull s 0 ((Y x').sent x T A.trot A.room A.post A.beta)
local notation "X_" s=> fun x':E=> pull s 0 ((Y x').V)
local notation "t"=> A.phaseUp.threshold
local notation "s'"=> A.phaseLow.threshold
local notation "A_" s=> (turnStore s U.key).costs
local notation "S_" s=> traceZ (turnStore s U.key).flags
local notation "Δ"=> A.ang+A.fee
variable {a a' b b' C' t₀:ℝ}
lemma motor(hp:∀ i,(Y i).key=U.key)(p:∀ s:Signed, CardX t (w/4) (P_ s) x₀ (A_ s) n A.trot v 0)(h:∀ s:Signed,CardX s' (w'/4) (X_ s) x₀ (S_ s) n A.trot v' 0)(ht:∀ s:Signed,∀ i∉ S_ s,Pressure.toll ((X_ s) x₀) i ≤ s')(hu:T.up.Bounds T.high w a b)(hW:T.down.Bounds T.low w' a' b')(hc: |A.beta|≤Q)(hK:|Δ|≤Q')(hv:|A.beta+(Δ)|≤Q): Pale (fun i x=> shardy A (Y x) k' i) (pot_c A v v' (w/4) (w'/4) Q Q' k') n x₀:=by
 let u:=(Fintype.card Signed:ℝ)⁻¹
 let W(s:Signed)(X:Bit (Site (Domain N B)))(y:E):=(∑ i,Lich.Muster.river A (Y y) s k' X i)-∑ i,Lich.Muster.flows A (Y y) s k' X i; let M(s:Signed)(X):=(∑ i,ringF A s k' Q v (w/4) X i)+(∑ i,ringC A s k' Q Q' v' (w'/4) X i); have hg(s:Signed):Pale (W s) (M s) n x₀:= (Pale.sums (fun j i y=>Lich.Muster.river A (Y y) s k' i j) _ (fun i=>frost A U s k' x₀ hp (p s) i hu hc)).difference (Pale.sums _ _ (fun i=> frost_c A U s k' x₀ hp (h s) i hW hv hK (ht s))) -- tune
 have hm: |-u| ≤1:=by unfold u; rw [abs_neg,abs_inv,abs_of_nonneg (Nat.cast_nonneg _)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α:=Signed)) -- uses integer
 convert (Pale.sums W M hg).sca (-u) hm using 1
 · ext1 i; ext1 j; unfold shardy averaged; rw [neg_mul]
 ext; simp only [one_mul]; rfl
end
section
local notation "K_"=>radiusB x
local notation "G_"=>atOne (Domain N B)
variable {C C' D D' σ σ':ℝ}
lemma ton (h0:0 < radiusB x)(o: Site (Domain N B))(hu:0 ≤ Q)(hv:0≤Q')(hk:0≤v)(hK:0≤v')(hF:T.up.Bounds T.high w C D)(hG:T.down.Bounds T.low w' C' D')(hp:Footprint.reserve (w/4) a (Paths.legFee S.ratio k' K_) σ)(hl:Footprint.reserve (w'/4) a (Paths.legFee G_ k' K_) σ'):
 (∑ i,tallyL o i a K_ * pot_c A v v' (w/4) (w'/4) Q Q' (k'*radiusB x) i) ≤ Fintype.card Signed*(worthK S.ratio k' K_ (Stores.till x) Q a C v w σ D A.phaseUp.threshold+(worthK G_ k' K_ (Stores.till x / S.patch.L.val) Q a C' v' w' σ' D' A.phaseLow.threshold +worthH G_ k' K_ Q' a C' v' w' σ' D' A.phaseLow.threshold)):=by
 unfold pot_c; simp_rw [mul_sum]; rw [sum_comm, ←card_univ, ←nsmul_eq_mul, ←sum_const]; apply sum_le_sum; intro i hi; have he:= budget_f k' A Q C w a v D σ o i h0 hF hp hu hk; have ht:=budget_c k' A Q Q' C' w' a v' D' σ' o i h0 hG hl hu hv hK; refine le_trans (le_of_eq ?_) (add_le_add he ht); simp_rw [mul_add,mul_sum, ←sum_add_distrib]
end
end YM.CF.Fief
