import YM.CF.Esti.Gory
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]{A B:Stores S}{U:E→ Config G f}{V:E→ Config G c}{q:Chi}{u:E}{k:S.Choices}{N N': Support c}{M:ℝ}
structure Mesh (n:ℕ)(f:E→ℝ)(x:E)(c:ℝ):Prop where
 cia : Allows n f x c
 nat:Zed n f x
lemma mesh(q v:E→ℝ)(x:E)(p:Mesh n q x K)(t:Mesh n v x C): Mesh n (fun i=> q i * v i) x (zest n*K*C):=⟨allot p.cia t.cia,fern p.cia t.cia p.nat t.nat⟩
private lemma tagm {y:E→ℝ}(p:‖y u‖≤ 1)(q:(fun _=>y u)=ᶠ[𝓝 u] y):Mesh n y u 1:=by
 refine ⟨(allows_const u p).germ q,fun h=>?_⟩; exact (allows_const (v:=(0:ℝ)) u (C:=0) (by simp)).germ (show _ from by filter_upwards [q] with i b; exact h ▸ b) -- tune
lemma taleF(k:S.Choices)(i:Site c)(p:Frolic A x U u)(hS:S.patch.Branches S.kernel G)(hp:shovel S.patch+10 ≤ radiusB x): Mesh n (fun w=>litF A x k (U w) i) u 1:=by
 unfold litF; split; next h=>
    apply tagm (y:=fun w=>AnalyticBridge.Annulus1AD.frame k (U w) i) (u:=u) ((Real.norm_of_nonneg (frame_zero ..)).trans_le (frame_price k _ hS _)); let j : Bond c:=(i,0); filter_upwards [p j (tuck hp h (show i∈pinPos j from mem_insert_self ..))] with v w; exact (Push.GridApprox.site_dep S hS _ (fun i p1 p2=> w i (Or.inl p1) (Or.inl p2)) _).2
 apply tagm _ (by rfl); let C:= Fintype.card S.patch.FrameTag; have : (1:ℝ) ≤ (C:ℝ):= Nat.one_le_cast.mpr (by exact Fintype.card_pos); rw [Real.norm_of_nonneg (by unfold C at *; positivity)]; exact inv_le_one_of_one_le₀ this
lemma taleB(k:S.Choices)(i:Bond c)(p:Frolic A x U u)(hS:S.patch.Branches S.kernel G): Mesh n (fun w=>litB A x k (U w) i) u 1:=by
 unfold litB; split; next h=>
    apply tagm (y:=fun w=>bond k (U w) i) (u:=u) ((Real.norm_of_nonneg (bond_zero ..)).trans_le (bond_price ..)); filter_upwards [p i h] with v w; unfold bond; rw [connector_p S G hS i k (U u) _ w]
 apply tagm _ (by rfl); let C:= Fintype.card S.patch.Points; have : (1:ℝ) ≤ (C:ℝ):=Nat.one_le_cast.mpr (by exact Fintype.card_pos); rw [Real.norm_of_nonneg (by unfold C at *; positivity)]; exact inv_le_one_of_one_le₀ this
private lemma paySum {I:Type}[DecidableEq I](S:Finset I)(f:I→ E→ ℝ) (p:∀ i∈S,Mesh n (f i) u C):Mesh n (fun w=>∏ i∈S,f i w) u ((zest n*C)^S.card):=let P:=fuel S f fun i t=> ⟨(p i t).1,(p i t).2⟩; ⟨P.1,P.2⟩
def dream (P:Patch)(n:ℕ)(x w a C M m:ℝ)(c g b:ℕ):ℝ:= zest n*(zest n*((zest n*dam G n (fiery G x P.L/4) M C)^b)*((zest n*trout P x w a C M m n)^g))*(zest n*((zest n*1)^c)*((zest n*1)^g))
lemma como (k:S.Choices)(w:ℝ)(N Q:Support c)(p:Frolic A x U u)(hp:shovel S.patch+10 ≤ radiusB x)(hS:S.patch.Branches S.kernel G)(ht:FuelG _ U u n C)(ht':FuelG _ V u n C)(hq:Dane G n q M)(g:Volo S n a b C m)(ha:0<a)(h₁:1≤M)(hm:0 ≤ m)(hv:1≤ C): Mesh n (fun i=> cohoT A x w a q (V i) (U i) k N Q) u (dream S.patch n x w a C M m N.card (nearNoise N).card (nearFace S Q).card):=by
 have hx(i):Mesh n (fun w=>tokenF A q x (U w) i) u (dam G n (fiery G x S.patch.L/4) M C) :=let L:=earn_f (x:=x) (A:=A) i ht hq; ⟨L.1,L.2⟩
 have hh(i): Mesh n (fun y=>tidal A x w a q (U y) (V y) k i) u (trout S.patch x w a C M m n):=let L:=earn p ht ht' hq hS g ha h₁ hm hv i w k; ⟨L.1,L.2⟩
 let L:=paySum (nearFace S Q) _ (fun i _=>hx i); let J:= paySum (nearNoise N) _ (fun i _=>hh i)
 let U':=paySum N _ (fun i _=>taleF (n:=n) k i p hS hp); let V':=paySum (nearNoise N) _ (fun i _=>taleB (n:=n) k i p hS); exact mesh _ _ _ (mesh _ _ _ L J) (mesh _ _ _ U' V')
end YM.CF.Esti
