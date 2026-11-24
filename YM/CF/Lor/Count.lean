import YM.CF.Fief.Dell
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
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Fief
variable {S :StepData c f}{T: Tube G₅ S}(A:Stores S)(s:Signed)(j:ℕ)(x:ℝ)
lemma load_p (L:Finset (Along S))(p:∀ i∈L,herald S s i∈A.dome (j*radiusB x)): L.card≤ about S.patch.L 0*Esti.latticeFieldEstimates A j x:=by
 let E:=A.dome (j*radiusB x); have hv:E.card ≤ Esti.latticeFieldEstimates A j x:=by
    apply (dome_count A j _).trans ((refer j (j+125) (Nat.le_add_right ..)).trans ?_); unfold Esti.latticeFieldEstimates; apply Nat.le_trans (le_mul_of_one_le_right (by positivity) (show 1≤ epoch S.patch.L from by unfold epoch; omega)) (le_mul_of_one_le_left (by positivity) (by norm_num))
 refine (card_le_card (show L ⊆ E.biUnion fun i=> Cay.peakM S s i 0 from fun i v=> mem_biUnion.mpr ⟨_,p i v,mem_filter.mpr ⟨mem_univ _, (separation_self _).le⟩ ⟩)).trans (Finset.card_biUnion_le.trans ?_); exact (sum_le_sum (fun i _=> num_peak s i)).trans (by rw [sum_const]; simpa only [smul_eq_mul,mul_comm (E.card)] using Nat.mul_le_mul_left (about S.patch.L 0) hv)
lemma blade: (lyn x s A j).card ≤ about S.patch.L 0 * Esti.latticeFieldEstimates A j x:=by
 let L:= lyn x s A j; let u : Site f ⊕ Site c→ Along S:= Sum.inr; have hp:= load_p A s j x (L.image u) fun i p=>by obtain ⟨z,t,rfl⟩:= mem_image.mp p; exact (mem_filter.mp t).2
 rwa [card_image_of_injective (f:=u) _ Sum.inr_injective] at hp
lemma branchZ: (strum x s A j).card ≤ about S.patch.L 0* Esti.latticeFieldEstimates A j x:= load_p A s j x _ fun i p=> (mem_filter.mp p).2
-- shelves.Flex.a
section card
variable {a b σ u C w:ℝ}{K:E→ Config G₅ f}{x:E}{r:ℕ}{F : Finset (Cell f)}{W:ℕ→ Atom G₅ r}
lemma lampM(p:CardX a σ K x F n q C u)(h:SumBudget (fun i=>(W i).budget σ) w)(l:0<σ)(t:0<a)(v:a≤1)(k:r≤4)(i:Site f):
 Allows n (fun y=>∑' j,lush_k q (W j) F a i (K y)) x (C*a^r*w)∧ ((∀ l∉F,Pressure.toll (K x) l≤ a)→ Allows n (fun y=>∑' j,peer_k (W j) F a i (K y)) x (C*a^r*w)):=by
 let d:=C*a^r; have he:0≤d:=mul_nonneg p.wt (pow_nonneg t.le _); obtain ⟨D,hD,H⟩:=loopK p.photo p.wind t v l r q
 have hv(Z:ℕ→ E→ ℝ)(g:∀ᶠ y in 𝓝 x,∀ j:ℕ,Allows n (Z j) y (D*(W j).budget σ))(u:∀ j, Allows n (Z j) x (d*(W j).budget σ)): Allows n (fun y=>∑' j,Z j y) x (d*w):=by apply (late_sum g (h.2.1.mul_left D) (h.2.1.mul_left d) u).mono; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 he
 exact ⟨hv _ (H.mono fun i' l z=> (l _ _).1) (fun _=>(p.clan.pot k _ i).1),fun y=> hv _ (H.mono fun i' l z=> (l _ _).2.1) (fun v=>(p.clan.pot k _ i).2.1 y)⟩ -- metavars inference
lemma allowedAv(V:Signed→ E→ℝ)(d:ℝ)(p:∀ i,Allows n (V i) x d): Allows n (fun y=> averaged fun i=> V i y) x d:=by
 let H:ℝ:=Fintype.card Signed; have he:0<H:=by unfold H; positivity
 refine ((summed Finset.univ V (fun i _=> p i)).smul H⁻¹).mono (le_of_eq ?_); rw [Finset.card_univ,abs_of_nonneg (inv_nonneg.mpr he.le)]; change H⁻¹*(H*d)=_; rw [←mul_assoc,inv_mul_cancel₀ he.ne',one_mul]
lemma payNeg {F:E→ℝ} (p:Allows n F x b):Allows n (fun y=> -F y) x b:=by convert p.smul (-1:ℝ) using 1; ext y; simp; simp
end card
end YM.CF.Lor
