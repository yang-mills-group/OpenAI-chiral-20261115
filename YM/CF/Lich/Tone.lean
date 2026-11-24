import YM.CF.Lich.Dive
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
local notation "Wc"=> pull s 0 W'.V
local notation "Q₀"=> ((l+90)*radiusB x)
include H p hp s
lemma rotL (i:Site m')(hx:Beat.shadows (o:=s.act (S.ratio.parent i)) X (radiusB x+10+Q₀))(Z:ℕ→ Atom SU.group n): Cloak.park F s U.key q A.phaseUp (batch Z b₀) i = Cloak.park P' s W'.key q A.phaseUp (batch Z b₀) i:=by
 refine tsum_congr fun z=>?_ ; unfold batch; split
 next v =>
    apply eastV A U s Q₀ H p hp le_rfl; intro t h; obtain ⟨u,g,w⟩:=halo_spec.mp h; obtain ⟨k,f,rfl⟩:=mem_image.mp g
    have he:separation i k ≤ b₀:= (mem_insert.mp f).elim (fun t=>by rw [t.symm,separation_self]; omega) (fun t=> (Push.AbsoluteSums.Paths.where_slot i (Z z).leg k (Push.AbsoluteSums.Paths.atom_foot i (Z z) ▸ t)).trans v)
    have hp':b₀≤B₀:= Nat.div_le_self ..; refine hx (halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle _ _ _).trans (Nat.add_le_add ?_ w)⟩); have h:=Work.E04.parent_separation S.ratio i k; rw [separation_signed]; exact (show separation (S.ratio.parent i) (S.ratio.parent k) ≤ radiusB x+10 by omega)
 simp only [lush_k,dimU,mul_zero]
lemma rootL (i:Site m)(hx:Beat.shadows (o:=s.act i) X (radiusB x+10+Q₀))(Z:ℕ→ Atom SU.group n):visit U.V s U.key A.phaseLow (batch Z b') i= visit W'.V s W'.key A.phaseLow (batch Z b') i:=by
 refine tsum_congr fun z=>?_ ; unfold batch; split
 next v=>
    apply eastW A U s Q₀ H p hp le_rfl; intro t h; obtain ⟨u,g,w⟩:=halo_spec.mp h; obtain ⟨k,f,rfl⟩:=mem_image.mp g
    have he:separation i k ≤ b':= (mem_insert.mp f).elim (fun t=> by rw [t.symm,separation_self]; omega) (fun t=> (Push.AbsoluteSums.Paths.where_slot i (Z z).leg k (Push.AbsoluteSums.Paths.atom_foot i (Z z) ▸ t)).trans v)
    have ht:b'≤b₀:= Nat.div_le_self ..; have hq: b₀≤B₀:=Nat.div_le_self ..; refine hx (halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle (s.act i) (s.act k) _).trans (Nat.add_le_add ?_ w)⟩); rw [separation_signed]; omega
 simp only [peer_k,dimU,ite_self]
-- core heat and kite local stamps
local notation "T₀"=> (A.loft*B₀)
local notation "D₁"=> (A.loft+l+200)*radiusB x
lemma crownL (i:Cell m)(g:Beat.shadows (o:=s.act i.1) X (16*B₀))(hv:V'=temp x) :king K₁ T.down T.low b₀ S.patch.L.val V' V₀ i=king (traceZ (turnStore s W'.key).flags) T.down T.low b₀ S.patch.L.val V' Wc i:=by
 rw [hv]; have hg:=lo_b s H p hp (i,true) g; unfold Esti.king; rw [show hallP _ _ _ _ _=_ from hg.2.1,hg.1] -- tune inference T inp
lemma verve(O:Stores S)(hx:O.dome D₁⊆ X)(hv:V'=temp x)(v:Along S)(h:v∈strum x s O j):heatR T F U.V s U.key q A.phaseUp A.phaseLow x Δ v=heatR T P' W'.V s W'.key q A.phaseUp A.phaseLow x Δ v:=by
 have he:=foster (show herald S s v∈ O.dome T₀ from (mem_filter.mp h).2) hx (show T₀+(B₀+10+Q₀) ≤ D₁ from by simp_rw [Nat.add_mul]; omega)
 rcases v with (i | i | i | i)|i|i; exact rfl; exact rfl; exact congrArg (-Δ *·) (crownL A U s H p hp i (Subset.trans (Corona.halo_mono (by simp_rw [Nat.add_mul]; omega) (Subset.refl _)) he) hv); exact rfl; exact rotL A U s H p hp i he _; exact congrArg Neg.neg (rootL A U s H p hp i he _)
omit s in
lemma crownF(O:Stores S)(hx:O.dome D₁ ⊆ X): oak T x U q θ l β A.phaseUp A.phaseLow j O=oak T x W' q θ l β A.phaseUp A.phaseLow j O:=by
 unfold oak; congr 2; apply funext; intro y; refine sum_congr rfl fun k u=>?_ ; have he:=foster (show herald S y (.inr k)∈ O.dome T₀ from (mem_filter.mp u).2) hx (show T₀+(B₀+10+Q₀) ≤ D₁ from by simp_rw [Nat.add_mul]; omega); rcases k with i|i; exact congrArg₂ (·+·) (rotL A U y H p hp i he _) (rotL A U y H p hp i he _); exact congrArg Neg.neg (congrArg₂ (·+·) (rootL A U y H p hp i he _) (rootL A U y H p hp i he _))
end Muster
end YM.CF.Lich
