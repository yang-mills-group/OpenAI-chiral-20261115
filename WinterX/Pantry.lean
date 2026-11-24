import YM.CF.Song.Beat
import WinterX.Locks
import WinterX.Walrus
import YM.CF.Ione.Cover
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Both
open Ione
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
variable {n:Side}(P:BudgetPoint)(v:Sweep n)
open Ione Sour.BondL Wray Larch Salt Bake Vow Lilt Sour Cadre
-- all comparisons stated using action sending anchor i to inspire v i. Step_F orientation
abbrev PotR(s:Sweep n)(X Y: Vow.Cusp n) := ∀ (V:Orbit n)(t:Injective (priorP V.2))(m:Aura n)(D:Support (More n)),D⊆ m.val→ Y (moldA s m) (actY s D) (yellA s V)=suit_Y s (X m D V)
-- KΦ only nonempty
abbrev PotZ(s:Sweep n)(X Y:Vow.Cusp n) := ∀ (V:Orbit n)(t:Injective (priorP V.2)), ∀ i:Aura n,∀ D:Support (More n),D.Nonempty→D⊆i.val→ Y (moldA s i) (actY s D) (yellA s V)= suit_Y s (X i D V)
abbrev ForceR(s:Sweep n)(F G:Scree.ForceBudget n):=∀ (V:Orbit n)(t:Injective (priorP V.2))(i:Scree.Force n),G (moveForce s i) (yellA s V)= suit_Y s (F i V)
abbrev PhaseR (s:Sweep n)(F G:Pax n):=∀ (V:Orbit n) (i:Aura n),G (moldA s i) (yellA s V)= suit_Y s (F i V)
abbrev Fex(F:Vow.Cusp n):Pax n:=fun i=> F i ∅
open Push.AbsoluteSums Trees
-- chooses beforehand Lxks for vision $AR
def PivotQual {n:Side}(P:BudgetPoint)(h γ:ℝ)(F Fv:Vow.Cusp n)(f:Vow.Cusp n→Vow.Cusp n): Prop :=
 (∀ s:Sweep n,∀ T:Vow.Cusp n, PotR s F T→ PotR s Fv (f T)) ∧
 Fv=f F ∧ Turf (Fex Fv)∧∃ C:Aura n→ℝ,Ready Palot.stern P.B C (P.supportExponent+1+1) γ wΨ (degreePrice P.B γ wΨ)∧∀ i:Aura n, Medal P i.val ∅ (Fex Fv i) h (C i)
#check degreePrice
#check wΨ
variable {γ h:ℝ}(F Fv X Xv:Vow.Cusp n)(A: Vow.Cusp n→Vow.Cusp n)
-- derive
lemma filings (e:PotR v Fv Xv)(u:Turf (Fex Fv))(y:Turf (Fex Xv)):PhaseR v (Fex Fv) (Fex Xv):=by
 intro T i; let Y:=moldA v i
 obtain ⟨j,h⟩:=(Skye.sepT (n:=n)).exists
 let W:Orbit n:=(T.1,j); rw [show Fex Xv _ _=Fex Xv _ (yellA v W) from y Y (yellA v T) (yellA v W).2,u i T j]
 have ht:=e W h i ∅ (Finset.empty_subset _); rw [show actY v ∅=∅ from Finset.map_empty ..] at ht; exact ht
lemma ion_A (u:PivotQual P h γ F Fv A)(y:PivotQual P h γ X Xv A)(t:PotR v F X)(K K1:Vow.Cusp n)(hK:PotZ v K K1)(hv:1≤h) : PotR v Fv Xv ∧
 PhaseR v (FeeD P (Fex Fv)) (FeeD P (Fex Xv))∧ForceR v (budgetR (roomV P (Fex Fv) Fv K)) (budgetR (roomV P (Fex Xv) Xv K1)):=by
 obtain ⟨e,z,QA,C,QK,p⟩:=u; obtain ⟨d,i,QaE,E,vp,x'⟩:=y
 have H:PotR v Fv Xv:=i.symm ▸ e v X t
 have hp:0≤ P.supportExponent+1+1:=by linarith [P.exponent_pos]
 have hQ:= filings v Fv Xv H QA QaE
 refine ⟨H,fun M i=>?_,fun M hm j=>?_⟩
 · exact spinsEW v i (suit_Y v) M QK hv p hp (hQ M) vp x' 0
 exact valiantW v (suit_Y v) M (fun i D _ t=> H M hm i D t) K (hK M hm) (hQ M) QK hv p hp vp x' j
#check spinsEW
#check valiantW
end YM.CF.Both
