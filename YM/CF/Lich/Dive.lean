import YM.CF.Lich.Mure
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
variable{c :Side}{F0 :Support c}{U1 V1:Config SU.group c}{P2 P3:Finset (Cell c)}
lemma port_g (t:ℝ)(h:∀ i∈Cloak.costA F0,(i∈P2↔i∈P3)∧Pressure.toll U1 i=Pressure.toll V1 i): polP t U1 F0 P2 ↔ polP t V1 F0 P3:=by
 constructor; intro p i v; obtain ⟨v,g⟩:=mem_inter.mp v; obtain ⟨u,h⟩:=h i g; rw [←h]; exact p i (mem_inter.mpr ⟨u.mpr v,g⟩)
 intro p i v; obtain ⟨v,g⟩:=mem_inter.mp v; obtain ⟨u,h⟩:=h i g; rw [h]; exact p i (mem_inter.mpr ⟨u.mp v,g⟩)
lemma port_h(t:ℝ)(q':Chi)(h:∀ i∈Cloak.costA F0,(i∈P2↔i∈P3)∧Pressure.toll U1 i= Pressure.toll V1 i): east q' F0 P2 t U1=east q' F0 P3 t V1:=by
 unfold Cloak.east; rw [port_g t h]; split; swap; exact rfl
 have he:costA F0 \ P2=costA F0 \ P3:= Finset.ext fun i=> by exact mem_sdiff.trans ((and_congr_right fun u=>not_congr (h i u).1).trans mem_sdiff.symm)
 unfold nose wrapM shutters; rw [he]; exact prod_congr rfl fun i p=> congrArg (q'.innerShare _) (h i (mem_sdiff.mp p).1).2
local notation "P4"=>pull s 0 W'.V
include H p hp hk s
lemma eastV (i:Site m')(L:Atom SU.group n)(hx:(shoreH (S:=S) s k i L).val⊆X): lush_k q L X₀ U' i U₀=lush_k q L (turnStore s W'.key).costs U' i P₁:=by
 let Q:=L.footprint i; unfold lush_k
 refine congrArg₂ (·*·) (port_h _ q ?_) (Extra.Iteration.Derivs.atom_local L i _ _ (roll_f A U s k H p hp hk i L hx)) -- tune
 intro z t; obtain ⟨a,v,w⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp t).2); let V:= (insert i (L.footprint i)).image (fun i=> s.act (S.ratio.parent i)); change halo k V ⊆ X at hx
 have hv:s.act (S.ratio.parent a)∈ V:= mem_image_of_mem _ (mem_insert_of_mem v); have he:=hearC (i:=a) A U s k H p hp hk (Subset.trans (Corona.halo_mono le_rfl (singleton_subset_iff.mpr hv)) hx) z (by rw [separation_comm]; have he:=Work.E01.sep_touched z a w; omega); exact ⟨he.2,congrArg SU.group.chord he.1⟩
local notation "P6"=>traceZ (turnStore s W'.key).flags
lemma eastW(i:Site m)(L:Atom SU.group n)(hx:(shoreS s k i L).val⊆ X): peer_k L K₁ V' i V₀=peer_k L P6 V' i P4:=by
 unfold peer_k; rw [port_g (V1:=P4) (P3:=P6) V' ?_]; swap
 · intro z v; obtain ⟨a,v,w⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp v).2); have he:=hearP (i:=a) A U s k H p hp hk (Subset.trans (Corona.halo_mono le_rfl (singleton_subset_iff.mpr (mem_image_of_mem _ (mem_insert_of_mem v)))) hx) z (by rw [separation_comm]; have he:=Work.E01.sep_touched z a w; omega); exact ⟨he.2,congrArg SU.group.chord he.1⟩
 split_ifs; exact Extra.Iteration.Derivs.atom_local L i _ _ (roll_c A U s k H p hp hk i L hx); rfl
lemma sleeves_v(i:Site m)(L:Atom SU.group n)(h:(shoreS s k i L).val⊆ X)(t:V'=temp x): Cloak.sleeve L K₁ T.low i V' V₀=Cloak.sleeve L P6 T.low i V' P4:=by
 let K':= (insert i (L.footprint i)).image (fun i=> s.act i); have ht:(s.act i)∈K':=mem_image_of_mem _ (mem_insert_self _ _); have he:= hearP (i:=i) A U s k H p hp hk (Subset.trans (Corona.halo_mono le_rfl (singleton_subset_iff.mpr ht)) h)
 unfold Cloak.sleeve; rw [pers_b _ V' _ ?_ (fun z w=> he z w)]; swap; · rw [t]; exact fun S _ _=> (p.mask S _ _ (by assumption)).trans (Nat.div_le_self ..)
 split_ifs; exact Extra.Iteration.Derivs.atom_local L i _ _ (roll_c A U s k H p hp hk i L h); rfl
lemma sleeves_f(i:Site m')(L:Atom SU.group n)(h:(shoreH (S:=S) s k i L).val⊆ X)(t:U'=fiery SU.group x S.patch.L)(ht:spanO T x): Cloak.sleeve L X₀ T.high i U' U₀=Cloak.sleeve L (turnStore s W'.key).costs T.high i U' P₁:=by
 let K':=(insert i (L.footprint i)).image fun i=> s.act (S.ratio.parent i); have hb:s.act (S.ratio.parent i)∈K':= mem_image_of_mem _ (mem_insert_self ..); have he:=hearC (i:=i) A U s k H p hp hk (Subset.trans (Corona.halo_mono le_rfl (singleton_subset_iff.mpr hb)) h)
 unfold Cloak.sleeve; rw [pers_b _ U' _ ?_ (fun z w=> he z w)]; swap; · rw [t]; exact fun S _ u=> ht _ (u.trans_le (SU.group.chord_le_two _))
 split_ifs; exact Extra.Iteration.Derivs.atom_local L i _ _ (roll_f A U s k H p hp hk i L h); rfl
end Muster
end YM.CF.Lich
