import YM.CF.Lich.Sail
import YM.CF.Lich.Fi
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
local notation "m"=> Domain N B
local notation "m'"=> Domain P B
variable{M:Monk SU.group S}{X:Support (Domain N B)}(H:Duo SU.group S U M X)(p:Ready T x)(h:1000≤radiusB x)
open Rel
abbrev Tips(l':ℕ) (V: Tab S→ DirP m): Prop:= ∀ P':Tab S,∀ i z:Site m,(V P' i z≠0→ separation i z≤ l')∧∀ K':Tab S,∀ x y:Config SU.group m,Kind S P' K' (Rel.pavilion l' i) → Tarn.drift SU.group i l' x y→ V P' i z x=V K' i z y
abbrev waysS (l':ℕ)(V:Tab S→ FileM m SU.group):Prop:=∀ t P':Tab S,∀ i:Site m,∀ x y: Config SU.group m, Kind S t P' (Rel.pavilion l' i) → Tarn.drift SU.group i l' x y→ V t i x= V P' i y
variable (g:Kind S (U.park,U.k) (M.park,M.k) X)(o:Site (Domain N B))(n':ℕ)(hp:Beat.shadows (o:=o) X n')
local notation "L'"=> (M.park,M.k)
local notation "t'"=> (U.park,U.k)
include H hp
lemma gateL {i:Site m}{d:ℕ}(p:separation o i + d≤ n'): i∈U.key.dome d↔ i∈ M.key.dome d:= ⟨fun v=>H.toBeat.same hp v p,fun z=> H.toBeat.sym.same hp z p⟩
lemma driftP(i:Site m)(r:ℕ)(ht:separation o i + (r+1) ≤ n'): Tarn.drift SU.group i r U.V M.V:=by
 have he:= aroundBk X hp ht; intro z v; have hx:= Work.E01.sep_step_le z.1 z.2; apply H.view _ (H.toBeat.sees he (by change separation _ _ ≤ r at v; omega)) (H.toBeat.sees he (_root_.le_trans (separation_triangle i z.1 _) (Nat.add_le_add v hx)))
include g
lemma oaths {l' d' k w:ℕ}{V₀:Tab S→ FileM m SU.group} {U₀: Tab S→ DirP m} (v: waysS l' V₀) (u:Tips d' U₀) (hs:l'+1 ≤ n')(hv:d'+d'+1≤n')(hq:k*radiusB x ≤ n')(hk:w*radiusB x+d' ≤ n'):
 issued x k w V₀ U₀ U.key t' o U.V=issued x k w V₀ U₀ M.key L' o M.V:=by
 let K1:= cClip x w U₀ U.key t'; let K2:=cClip x w U₀ M.key L'; have he(Z:Tab S)(N':Stores S)(i j':Site m)(p:d'<separation i j'): cClip x w U₀ N' Z i j'=0:=by unfold cClip; split; exact not_not.mp (fun h=> p.not_ge ((u _ i j').1 h)); rfl
 have hu(i j':Site m)(hy:separation o i ≤d')(hu:separation o j' ≤d'):K1 i j' U.V=K2 i j' M.V:=by
    unfold K1 K2 cClip; simp only [gateL U H o n' hp (d:=w*radiusB x) (i:=i) (by omega),gateL U H o n' hp (d:=w*radiusB x) (i:=j') (by omega)]; split
    next=> exact (u _ i j').2 _ _ _ (kind_m g (aroundBk X hp (by omega))) (driftP U H o n' hp i d' (by omega))
    rfl
 unfold issued dict; simp only [Finset.sum_apply, Pi.add_apply,Pi.sub_apply]; simp only [gateL U H o n' hp (i:=o) (d:=k*radiusB x) (by rw [separation_self]; omega)]; refine congrArg₂ (·+·) ?_ ?_; · split; rfl; exact v _ _ _ _ _ (kind_m g ((Corona.halo_mono (show l'≤ n' by omega) (Subset.refl _)).trans hp)) (driftP U H o n' hp o _ (by rw [separation_self]; omega))
 refine congrArg₂ (·-·) (sum_congr rfl fun i _=> ?_) (sum_congr rfl fun i _=> ?_)
 · by_cases H: separation o i≤d'; exact hu _ o H (by simp); rw [show cClip x w U₀ U.key _ i o=0 from he _ _ i o (by rwa [separation_comm,← not_le]),he L' M.key i o (by rwa [separation_comm,←not_le])]; rfl
 by_cases H:separation o i ≤ d'; exact hu _ i (by simp) H; rw [he t' U.key o i (lt_of_not_ge H),he L' M.key o i (lt_of_not_ge H)]; rfl
end Muster
end YM.CF.Lich
