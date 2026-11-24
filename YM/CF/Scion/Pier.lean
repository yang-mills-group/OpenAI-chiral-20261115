import YM.CF.Scion.Omen
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel
lemma full_s (x: FC (LeanV n))(y: FC n)(W:Weave n M):spanP _ (issue W x y):=pitch_s W.pals W.seats _ _ W.ward.1 W.ward.2 x y
lemma glueT (W:Weave n M)(P Q:Op M)(L:Op n)(T:Op M)(p:IsStarProjection L)(u:IsStarProjection T)(h:Wave n→ₗ[ℂ] Wave M)(i:Wave n)(v:Wave M)(c:ℂ)(q:TagG T P)(t:TagG T Q)(H:∀ a:List (LeanV n),∀ b:List (Oboe n),h (acts ((nursery L p).eval (rollC put a)*rollC bell b) i)= c • acts ((nursery T u).eval (issue W (rollC put a) (rollC bell b))) (acts (exp (dg P)) (acts (exp (dg Q)) v))) (X:FC (LeanV n))(B:FC n)(hp:spanP _ X): h (acts ((nursery L p).eval X * B) i)= c • acts ((nursery T u).eval (issue W X B * (exp (boat Q)).val)) (acts (exp (dg P)) v):=by
 let Z:=nursery T u
 have hc:Commute (exp (dg P)) (exp (dg Q)):=by rw [← Hest.bloom _ P u q,← Hest.bloom _ Q u t]; exact (Commute.all (exp (boat P)) _).map _
 rw [Scree.fireT _ (full_s X B W) (Pastry.Flour.allP (s:=univ) ((fineShape _): Flour _ (exp (boat Q)).val)),show (nursery T u).eval (exp (boat Q)).val= exp (dg Q) from Hest.bloom _ _ u t,act_mul ((nursery T u).eval _)];
 rw [←act_mul (exp (dg Q)), ←hc.eq,act_mul _ (exp (dg Q))]; have ht:B=pour ((hope _).symm B):=by
    conv_lhs=>rw [← (hope _).apply_symm_apply B]
    change wont orchestra _= _; unfold wont; simp_rw [playB]
 rw [hp,ht]; unfold Hake.pour; simp only [map_sum, LinearMap.sum_apply,Finset.sum_mul,Finset.mul_sum,_root_.sum_apply,Finset.smul_sum]
 refine sum_congr rfl fun j _=> sum_congr rfl fun z _=>?_
 obtain ⟨D,hd⟩:=along_p (n:=LeanV n) z; obtain ⟨E,f⟩:= duet (n:=n) j; simp only [hd,f,map_smul, LinearMap.smul_apply,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; -- tune 
 simp only [smul_smul, mul_comm]; rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,map_smul]; exact (congrArg (fun t => (crumb X z * (hope n).symm B j) • t) (H D E)).trans (smul_comm _ _ _)
end YM.CF.Scion
