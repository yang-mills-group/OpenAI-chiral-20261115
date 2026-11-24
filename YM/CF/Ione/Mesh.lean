import YM.CF.Ione.Tape
import YM.CF.Hype.Ace
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
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
abbrev deadP {N:Type*}[LinearOrder N][Fintype N](A:Dough N):=A- wage_Q 2 A
lemma skid_X {N:Type*}[LinearOrder N][Fintype N](A:Dough N)(i:Finset N): crumb (deadP A).val i=if i.card=2 then 0 else crumb A.val i:=by
 change crumb A.val i-crumb (wage_Q 2 A).val i=_; rw [price_X]; split <;>simp
lemma dead_v{N:Type*}[LinearOrder N][Fintype N](b r:Bool)(U:UNI N)(A:ribbon N): deadP (paintR b r U A)=paintR b r U (deadP A):=by unfold deadP; rw [map_sub,pose_U]
variable {F G:InkD n}{X Y: Scree.Hub n}
lemma post_C (p:PressB P X F h a): PressB P X (deadP ∘ F) h a:=by
 obtain ⟨x,v,t,j,G,u,T,w⟩:=p; refine ⟨fun i j p=>congrArg deadP (x _ _ p),fun i=>?_,t.sub ((peek_P 2).measurable.comp t),fun i v=>?_,G,u,fun i p j=>?_,w⟩ -- Flour.sub via sub_eq
 · simp only [Function.comp_apply,deadP,sub_eq_add_neg]; apply (v i).add; have hp: -(wage_Q 2 (F i)).val=(-1:ℝ) • (wage_Q 2 (F i)).val:=by rw [neg_smul,one_smul]
   change Flour _ (-(wage_Q 2 (F i)).val); rw [hp]; exact (worthS 2 _ _ (v i)).rsmul _ -- tune placeholders
 · simp only [Function.comp_apply,j]; exact dead_v ..
  -- opacity
 · simp only [Function.comp_apply,skid_X]; split; exact hail (by rw [norm_zero]; exact u j); exact T i p j -- indentation
lemma scale_E (p:PressB P X F h a)(v:ℝ): PressB P X (v • F) h (|v| *a):=by
 obtain ⟨x,f,t,g,A,u,T,w⟩:=p; refine ⟨fun i j p=>congrArg (fun c:Cipher n=>v•c) (x _ _ p),fun i=>(f i).rsmul _,measurable_const.smul t,fun i y=> (congrArg (v • ·) (g i y)).trans (map_smul ..).symm,(fun i=> |v| *A i),fun i=>mul_nonneg (abs_nonneg _) (u i),fun i h y=> skills ?_,?_⟩
 · exact (skin (T i h y)).smul v
 simp_rw [mul_left_comm _ |v|,←mul_sum]; exact mul_le_mul_of_nonneg_left w (abs_nonneg _)
local notation "qk"=> fun (_:Sweep n)=> False
local notation "nX"=> Scree.Hub n
variable {R E:RegBudget n}
def base_Q (s:Sweep n)(R:RegBudget n)(x:Scree.Hub n):InkD n:=step_F s (R (moveHub s x))
abbrev Sym_P(R:RegBudget n):Prop:=∀ s:Sweep n,base_Q s R=R
abbrev tree_C(E:RegBudget n)(i:Scree.Hub n): InkD n:=restK (E i)
abbrev numbD(E:RegBudget n)(i:Scree.Hub n):InkD n:=deadP ∘ E i
abbrev plight_C(n:Side):ℝ:=(Fintype.card (Sweep n):ℝ)⁻¹
lemma envy(n:Side):0<plight_C n:=by unfold plight_C; positivity
abbrev scope_q(s:Sweep n):Equiv.Perm (Scree.Hub n) where
 toFun:= moveHub s
 invFun:=moveHub s⁻¹
 left_inv:=fun x=>Subtype.ext (Prod.ext (by simp [moveHub,sitU]) (tape_C ..)) -- boxA⁻¹.symm defeq? use rw
 right_inv:=fun x=>Subtype.ext (Prod.ext (by simp [moveHub,sitU]) (by have hp:= tape_C s⁻¹ x.val.2; rw [inv_inv] at hp; exact hp))
lemma glow_q(k:ℕ)(X:Support (More n)):coverNumber k (actY s X)= coverNumber k X:=by
 unfold actY; rw [←sitU,map_eq_image]; exact ProjectorNext.Equivariance.moves_cost .. -- maybe not defeq
lemma mold_q(x:nX): P.mass (moveHub s x).val.2=P.mass x.val.2:=by funext y; unfold BudgetPoint.mass; rw [show coverNumber _ (moveHub s x).val.2= _ from glow_q s P.B x.val.2]
abbrev terra_C(k p:ℕ):ℝ:=(fare_T 2:ℝ)*duty_Q k p
lemma lucre(k p:ℕ): 0 ≤ terra_C k p:=by unfold terra_C duty_Q composeCost; positivity
lemma earth_F (p:IncX (fun _ :Sweep n=>False) E P h a)(v:0≤h): IncX (fun _=>False) (base_Q s (tree_C E)) P h (terra_C P.order P.power*a):=by
 obtain ⟨F,p,j⟩:=p.weight; let H:= terra_C P.order P.power
 refine ⟨⟨fun i=> H*F (moveHub s i),fun i=>?_ ,fun i=>?_⟩,fun _ t=>t.elim⟩
 · unfold H terra_C; dsimp only; rw [mul_assoc]; exact consume_F P s _ _ (p _) v -- supply args
 apply le_trans _ (mul_le_mul_of_nonneg_left (j ((boxA s).symm i)) (lucre ..)); rw [mul_sum]; conv_rhs=>rw [←Equiv.sum_comp (scope_q s)] -- direction occurrence
 apply le_of_eq; apply sum_congr rfl; intro j _; change ite _ _ _=_; split_ifs with v p h
 · have hp:= mold_q P s j; unfold BudgetPoint.mass; rw [show coverNumber _ (scope_q s j).val.2= _ from glow_q s P.B j.val.2]; change (Trees.currency P.B P.supportExponent j.val.2)*(H*F _)=H*(Trees.currency _ _ _* F (moveHub s j)); ring
 · exact False.elim (p (congrArg (boxA s).symm v))
 · exact False.elim (v ((boxA s).symm.injective h))
 rw [mul_zero]
end YM.CF.Ione
