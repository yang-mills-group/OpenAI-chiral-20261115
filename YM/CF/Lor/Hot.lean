import YM.CF.Lor.Haven
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
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
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
open Nacre Font
open BoreP Fief rates Braid Rel Souk Girt
variable{m X B M:Side}{G:Ratio (mid m B) (mid X B)}{e x β d:ℝ} {T:Roam m X B}(F:Tube G₅ T)
local notation "L"=> mid m B
local notation "K"=> More (mid m B)
local notation "K'"=> More (mid X B)
local notation "Y"=> Rent0 G e
local notation "S₀"=>portA (X:=X) (B:=B) (Stores.till x)
section lens
variable {ρ η C D a b:ℝ}{S:E→ Rent0 G e}{u:E}(H:Haze m X B G e)(G)
local notation "Ϊ"=>Single L
lemma bound_w{W:mSeal X B→ Toll (Single L)}(p:∀ i j k,0 ≤ W i j k)(h:Ledger ρ W b)(hp:0≤ρ)(M:Finset (mSeal X B))(i j:Single L): (∑ t∈M,W t i j)≤ b:=by
 apply le_trans (Finset.sum_le_sum (g:=fun t=>Branch.rent ρ t*W t i j) (fun t _=> le_mul_of_one_le_left (p t i j) (rent_one hp _)))
 refine (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _=> mul_nonneg (Branch.rent_pos ..).le (p ..))).trans ?_; exact (single_le_sum (fun j (_:j∈(univ:Finset _))=> sale_nn p ρ i j) (mem_univ j)).trans (h.rows i)
-- joint actual monitor per rent required read only. cap local. readability
structure RawK (S:E→ Rent0 G e)(o:Site (Domain m B))(x η:ℝ)(k:ℕ)(u:E):Prop where
 radius : η < e
 stem :JointB G (S u).val η
 pose (v:mSeal X B):Grove (Tenant.terr _) v → o∈ Facet.mount (ratio G) v → v.card ≤ Stores.till x → (∀ j:Bond (Domain X B),Skye.ends j⊆ v→ Allows k (fun t=> SU.fund ((S t).val.1 j)) u 1) ∧(∀ j:Bond (Domain m B), Skye.ends j ⊆ cloudG G v→ Allows k (fun t=> SU.fund ((S t).val.2 j)) u 1)
variable {Ψ:nomA m X B→ℂ}{v C c:ℝ}{k:ℕ}{θ: nomA m X B→ Op (Single (mid m B))}
lemma wrath (i j:Ϊ)(p:RawK G S (place_x i) x η k u)(h:Hest.Ind G H ρ b C k θ)(hz:1<C)(hp:0 ≤ ρ): Allows k (fun t=> Corne.led G x H (S t) i j) u b:=by
 obtain ⟨W,H,K0⟩:= h.port; simp_rw [Corne.led,Matrix.sum_apply]; apply Allows.mono (C:=(∑ t∈S₀,W t i j)) _ (bound_w (X:=X) (B:=B) (m:=m) (fun i=> (H i).pos) K0 hp _ i j)
 refine Jet.allows_sum ?_; intro v t; by_cases hz': W v i j=0
 · rw [hz']; have hy(t):= norm_le_zero_iff.mp ((H v).gate i j (S t)|>.trans_eq hz'); simp_rw [hy]; exact allows_const u norm_zero.le
 obtain ⟨x',e,w⟩:= (H v).root i j hz'; obtain ⟨z,p'⟩:=p.pose v x' (mem_image.mpr ⟨_,(mem_filter.mp e).2,Ratio.embed_parent ..⟩) (mem_filter.mp t).2; exact riseP k S _ ((H v).folk i j) (fun a b t=>congrArg (fun U:Op Ϊ=> U i j) ((H v).reads _ _ t)) p.radius hz p.stem z p'
lemma weight (A:Msca m X B G e)(o:Site (Domain m B))(v:RawK G S o x η k u)(p:Tally A Ψ a C c D k)(hc:1<C)(t:0 ≤c): Allows k (fun y=>fJ G A x (S y) o) u (G.count.val^4*D):=by
 obtain ⟨W,H,H'⟩:= p.members; let M:=turtle (ratio G); have hp:=owing (ratio G) W D (fun i=>(norm_nonneg _).trans ((H i).sumline (S u))) H' o t S₀ -- tune `positive`
 apply Allows.mono (C:=(∑ j∈S₀, |M j o| * W j)) _ hp
 refine Jet.allows_sum (f:=fun j y=> M j o • A j (S y)) ?_; intro i hi; let z:=M i o; by_cases he:W i=0
 · rw [he,mul_zero]; have hv(t):= norm_le_zero_iff.mp ((H i).sumline (S t)|>.trans_eq he); simp_rw [hv,smul_zero]; exact Jet.allows_const u norm_zero.le
 by_cases h:o∈Facet.mount (ratio G) i; swap; simp_rw [M,turtle,if_neg h,zero_smul,abs_zero,zero_mul]; exact Jet.allows_const u norm_zero.le
 obtain ⟨s',v'⟩:= v.pose i ((H i).travel he) h (mem_filter.mp hi).2; apply Allows.smul; exact Fief.riseP k S _ (H i).plot (H i).reads v.radius hc v.stem s' v'
end lens
end YM.CF.Lor
