import YM.CF.Lich.Bloss
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
open Vol
variable (s:Signed)
local notation "X₀"=>(turnStore s U.key).costs
local notation "K₁"=> traceZ (turnStore s U.key).flags
local notation "U₀"=> pull s 0 F
local notation "V₀"=> pull s 0 U.V
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
local notation "V'"=> A.phaseLow.threshold
local notation "U'"=> A.phaseUp.threshold
local notation "b₀"=> Stores.till x
local notation "b'"=> b₀/S.patch.L.val
local notation "Δ"=> (α+γ)
variable(k:ℕ){W': Monk SU.group S}{X:Support (Domain N B)}(H:Duo SU.group S U W' X)(p:Ready T x)(hp:1000≤ radiusB x)
local notation "P'"=> W'.sent x T q θ l β
local notation "P₁"=>pull s 0 P'
local notation "B₀"=> radiusB x
open Work.E03
variable (hk: (A.post+90)*radiusB x ≤ k) -- binder issues notation
include H p hp hk
lemma roll_f (i:Site m')(L:Atom SU.group n)(hx:(shoreH (S:=S) s k i L).val⊆X): Agrees (L.footprint i) U₀ P₁:=by
 intro z v u; let j':=S.ratio.parent z.1; let t:= (insert i (L.footprint i)).image (fun i=> s.act (S.ratio.parent i)); change halo k t ⊆ X at hx
 have ht:s.act j'∈ t:= mem_image_of_mem _ (show z.1∈insert i (L.footprint i) from mem_insert_of_mem v)
 have hx':Beat.shadows (o:=s.act j') X ((0:ℕ)+(l+64)*radiusB x):= (Corona.halo_mono (show (0:ℕ)+(l+64)*B₀ ≤ k from by simp only [Nat.add_mul] at *; omega) (singleton_subset_iff.mpr ht)).trans hx
 have hw: AgreeNear S.ratio.parent j' 0 U₀ P₁:= uf_b s H p hp j' hx'
 exact hw z (by simp [j'])
lemma hearC{i:Site m'}(hx:Beat.shadows (o:=s.act (S.ratio.parent i)) X k)(z:Cell m')(hz:separation i z.1 ≤ B₀): faceValue U₀ z=faceValue P₁ z∧ (z∈X₀↔ z∈ (turnStore s W'.key).costs):=by
 let o:= S.ratio.parent i; have he: AgreeNear S.ratio.parent o (4*B₀) U₀ P₁:=uf_b s H p hp o (aroundBk X hx (by unfold o; simp only [separation_self,Nat.add_mul] at *; omega)); have hg:= Work.E04.parent_separation S.ratio i z.1; refine ⟨travel_near S.ratio.parent (parent_step S) _ _ z.1 _ 4 (le_of_eq rfl) (he.shrink (by unfold o; omega)),?_⟩
 simp only [costs_turn]; exact H.cost (Face.send s 0 z) (fun t=> disjoint_left.mp t (show s.act (S.ratio.parent z.1)∈ startPos S (Face.send s 0 z) from startPos_turn s z ▸ mem_image_of_mem _ (mem_image_of_mem _ (Work.E01.base_touched _))) (H.toBeat.sees hx (by rw [separation_signed]; simp only [Nat.add_mul] at *; omega))) -- tune big simp
local notation "Wc"=>pull s 0 W'.V
local notation "A₂"=> traceZ (turnStore s W'.key).flags
lemma roll_c (i:Site m)(L:Atom SU.group n)(hx:(shoreS s k i L).val ⊆ X): Agrees (L.footprint i) V₀ Wc:=by
 intro z v u; have he:Beat.shadows (o:=s.act z.1) X k:= Subset.trans (Corona.halo_mono le_rfl (singleton_subset_iff.mpr (mem_image_of_mem _ (mem_insert_of_mem v)))) hx; exact cu_b s H p hp z.1 (aroundBk X he (by change separation (s.act z.1) (s.act z.1)+(0+13*B₀)≤ k; simp only [Nat.add_mul,separation_self] at *; omega)) z (by simp)
lemma hearP{i:Site m}(hx:Beat.shadows (o:=s.act i) X k) (z:Cell m)(hz:separation i z.1 ≤ B₀): faceValue V₀ z=faceValue Wc z∧ (z∈K₁↔ z∈A₂):=by
 have he:AgreeNear id i (4*B₀) V₀ Wc:= cu_b s H p hp i (aroundBk X hx (by simp only [Nat.add_mul,separation_self] at *; omega)); refine ⟨travel_near id Work.E03.sep_step _ _ _ _ 4 (le_of_eq rfl) (he.shrink (by simp only [id_eq]; omega)),?_⟩
 simp only [traceZ,mem_filter,mem_univ,true_and,flag_turn]; exact H.flags _ (H.toBeat.sees hx (by simp_rw [Nat.add_mul] at hk; rw [separation_signed]; omega))
end Muster
end YM.CF.Lich
