import YM.CF.Pyx.Hand
import YM.Branch.Covariant
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Pyx
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
open Girt
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
open Broc
variable {M:Side}{x W:ℝ}
-- Π Ward through RG reader transport ALL selected scales. preserve GAUGE for scalar singlet readers; open transforms later.note legal masks.
section eig
variable {m b:Type*}[LinearOrder m][LinearOrder b][Fintype m][Fintype b]
variable (i:m↪b)(s:Finset b)(h:Deck i s)
variable (P:UNI b)(Q:UNI m)
lemma rotate_z(U:UNI m)(x:Ket m): (quant U.val)*remove x= remove (acts U.val x)*quant U.val :=by
 rw [←twist_remove U,twist_formula]; change _= quant U.val*_*star (quant U.val)*_
 rw [mul_assoc (quant U.val*_),show star (quant U.val)*quant U.val=1 from (quantU U).property.1,mul_one] -- tune
include h
lemma charge_i (R:Finset m)(x:Wave m)(p:Sea (cutM R) x)(g:∀ j:Ket m,acts P.val (coat i j)=coat i (acts Q.val j))(w:acts (quant Q.val) x=x)(f:acts (quant P.val) (hoist i s x)= hoist i s x)(V:Wave m): hoist i s (acts (quant Q.val) V)=acts (quant P.val) (hoist i s V):=by
 let C:= (hoist i s).comp (acts (quant Q.val)); let F:= (acts (quant P.val)).comp (hoist i s)
 have he(Z:Finset m):C (basisKet Z)=F (basisKet Z):=by
    have hv:C (basisKet R)= F (basisKet R):=by
      let a:=x.ofLp R; have he:x=a • basisKet R:=by have ht:=p.1; rw [cutLine,cut_oneAct] at ht; exact ht.symm -- tune
      have hx:a≠0:=fun v=> absurd (show ‖x‖=0 from (by rw [he,v,zero_smul,norm_zero])) (p.2.symm ▸ (by norm_num : (1:ℝ) ≠ 0))
      have hP:C x=F x:=by simp only [C,F,ContinuousLinearMap.comp_apply,w,f]
      rw [he,map_smul,map_smul] at hP; exact smul_right_injective (Wave b) hx hP
    have hA(R:Finset m)(p:C (basisKet R)= F (basisKet R)):C (basisKet ∅)= F (basisKet ∅):=by
       induction R using Finset.induction_on with
       | empty=>exact p
       | insert a r u ih=>
          let Y:= basisKet (insert a r); let c:=parity a (insert a r); have he:c≠0:=pow_ne_zero _ (by norm_num)
          have hg:F (acts (takeF a) Y)=C (acts (takeF a) Y):=by
             change acts (quant P.val) (hoist i s (acts (takeF a) Y))= hoist _ _ (acts _ _); rw [hoist_t _ _ h, ← act_mul, ←remove_take a, ←remove_take (i a), rotate_z, act_mul, ←act_mul (quant Q.val), rotate_z,act_mul,hoist_r _ _ h, ← basis_shell i a, g,show acts (quant P.val) (hoist i s Y)= _ from p.symm]; rfl -- tune rw first target `acts.comp` order
          rw [show acts (takeF a) Y=c • basisKet r from (by unfold Y c; rw [take_act,if_pos (mem_insert_self ..),erase_insert u]),map_smul,map_smul] at hg; exact ih ((smul_right_injective _ he hg).symm)
    induction Z using Finset.induction_on with
    | empty=>exact hA _ hv
    | insert a r u ih=>
       let V:= basisKet r; have hp:C (acts (put a) V)=F (acts (put a) V):=by
          change hoist _ _ (acts _ _)= acts _ (hoist _ _ _); rw [hoist_put,←create_put a,←create_put (i a),←act_mul,←act_mul, quant_create,quant_create,act_mul,act_mul, hoist_c _ _ h,←basis_shell i a,g,show hoist i s (acts (quant Q.val) V)=_ from ih]; rfl
       rw [show acts (put a) V=_ from put_act a r, if_neg u,map_smul,map_smul] at hp; exact smul_right_injective (Wave b) (show parity a r ≠ 0 from pow_ne_zero _ (by norm_num)) hp
 change C V =F V; rw [← basis_expand V, map_sum,map_sum]; simp_rw [map_smul,he]
end eig
end YM.CF.Pyx
