import YM.CF.Mica.Leg
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
abbrev blind_E {N:Type*}[LinearOrder N][Fintype N](A:Dough N):=A- wage_Q 0 A
lemma shelter_Q {N:Type*}[LinearOrder N][Fintype N](A:Dough N)(i:Finset N): crumb (blind_E A).val i=if i.card=0 then 0 else crumb A.val i:=by
 change crumb A.val i-crumb (wage_Q 0 A).val i=_; rw [price_X]; split <;>simp
lemma sanct_E{N:Type*}[LinearOrder N][Fintype N](b r:Bool)(U:UNI N)(A:ribbon N): blind_E (paintR b r U A)=paintR b r U (blind_E A):=by unfold blind_E; rw [map_sub,pose_U]
variable {F G:InkD n}{X Y: Scree.Hub n}
lemma easy_W (p:PressB P X F h a): PressB P X (blind_E ∘ F) h a:=by
 obtain ⟨x,v,t,j,G,u,T,w⟩:=p; refine ⟨fun i j p=>congrArg blind_E (x _ _ p),fun i=>?_,t.sub ((peek_P 0).measurable.comp t),fun i v=>?_,G,u,fun i p j=>?_,w⟩ -- Flour.sub via sub_eq
 · simp only [Function.comp_apply,blind_E,sub_eq_add_neg]; apply (v i).add; have hp: -(wage_Q 0 (F i)).val=(-1:ℝ) • (wage_Q 0 (F i)).val:=by rw [neg_smul,one_smul]
   change Flour _ (-(wage_Q 0 (F i)).val); rw [hp]; exact (worthS 0 _ _ (v i)).rsmul _ -- tune placeholders
 · simp only [Function.comp_apply,j]; exact sanct_E ..
  -- opacity
 · simp only [Function.comp_apply,shelter_Q]; split; exact hail (by rw [norm_zero]; exact u j); exact T i p j -- indentation
local notation "qk"=> fun (_:Sweep n)=> False
local notation "nX"=> Scree.Hub n
variable {R E:RegBudget n}
abbrev cry_H(E:RegBudget n)(i:Scree.Hub n): InkD n:=sage_L (E i)
abbrev head_L(E:RegBudget n)(i:Scree.Hub n):InkD n:=blind_E ∘ E i
abbrev shine_M(k p:ℕ):ℝ:=(fare_T 0:ℝ)*duty_Q k p
lemma mode_W(k p:ℕ): 0 ≤ shine_M k p:=by unfold shine_M duty_Q composeCost; positivity
lemma thrive_X (p:IncX (fun _ :Sweep n=>False) E P h a)(v:0≤h): IncX (fun _=>False) (base_Q s (cry_H E)) P h (shine_M P.order P.power*a):=by
 obtain ⟨F,p,j⟩:=p.weight; let H:= shine_M P.order P.power
 refine ⟨⟨fun i=> H*F (moveHub s i),fun i=>?_ ,fun i=>?_⟩,fun _ t=>t.elim⟩
 · unfold H shine_M; dsimp only; rw [mul_assoc]; exact swirl_x P s _ _ (p _) v -- supply args
 apply le_trans _ (mul_le_mul_of_nonneg_left (j ((boxA s).symm i)) (mode_W ..)); rw [mul_sum]; conv_rhs=>rw [←Equiv.sum_comp (scope_q s)] -- direction occurrence
 apply le_of_eq; apply sum_congr rfl; intro j _; change ite _ _ _=_; split_ifs with v p h
 · have hp:= mold_q P s j; unfold BudgetPoint.mass; rw [show coverNumber _ (scope_q s j).val.2= _ from glow_q s P.B j.val.2]; change (Trees.currency P.B P.supportExponent j.val.2)*(H*F _)=H*(Trees.currency _ _ _* F (moveHub s j)); ring
 · exact False.elim (p (congrArg (boxA s).symm v))
 · exact False.elim (v ((boxA s).symm.injective h))
 rw [mul_zero]
end YM.CF.Ione
