import YM.CF.Gully.Wax
import YM.CF.Spark.Org
import YM.CF.Spire.Thick
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
section
open Spark
variable {I J:Type*}[LinearOrder I][Fintype I][LinearOrder J][Fintype J](e:I≃J)
private lemma crossT (e:I≃J)(z:ℂ)(A:FC J) : crossL e (z • A)=z • crossL e A:= cx_eq e _ _ (fun x=>by rw [act_smul,act_smul,carts_s,crossed])
def cisT(e:I≃J) : FC J→+* FC I where
 toFun:=crossL e
 map_add' x y:=cx_eq e _ _ fun k=> by rw [act_add,act_add, ←crossed, ←crossed]; exact map_add (Fock.hoist e.toEmbedding ∅) _ _
 map_one':= cx_eq e _ _ (fun k=> by rw [act_one,act_one])
 map_mul':=cx_m e
 map_zero':= cx_eq e _ _ (fun k=> by rw [act_zero,act_zero]; exact map_zero _)
lemma coastP (A:FC J) (z:ℂ): cisT e (z • A)= z • cisT e A:=crossT ..
lemma railN(A:FC J): ‖cisT e A‖ ≤ ‖A‖:=by
 rw [← Matrix.l2_opNorm_toEuclideanCLM]; refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_; intro x; change ‖acts (crossL e A) x‖≤_; rw [←carts_n e (acts (crossL e A) x),crossed,← carts_n e x]; exact le_trans ((acts A).le_opNorm _) (le_of_eq (congrArg (·*_) (Matrix.l2_opNorm_toEuclideanCLM A))) -- tune
lemma trails(i:J):cisT e (put i)=put (e.symm i):=by obtain ⟨i,rfl⟩:=e.surjective i; rw [Equiv.symm_apply_apply]; exact (cx_p ..).1
lemma coal(S:Finset J):∃ v:ℂ,cisT e (poke S)=v • poke (S.map e.symm.toEmbedding):=by
 induction S using Finset.induction_on_min with
 | empty => simp only [Finset.map_empty,poke,Poly.tag_void,map_one]; exact ⟨1,(one_smul ..).symm⟩
 | insert j S p ih =>
    obtain ⟨v,hv⟩:= ih; have h:j∉ S:= fun v=>lt_irrefl _ (p j v); have ht:e.symm j∉S.map e.symm.toEmbedding:=by simp [h]
    let T:=S.map e.symm.toEmbedding; refine ⟨parity (e.symm j) T*v,?_⟩; rw [map_insert, poke,Poly.tag_min _ _ _ p, map_mul,show cisT e ((cane J).term j)=put (e.symm j) from trails e j,hv, show e.symm.toEmbedding j=e.symm j from rfl,show poke (insert _ _)=_ from Poly.tag_any (cane I) _ _ ht, smul_smul]; rw [show parity (e.symm j) T*v*parity (e.symm j) (S.map e.symm.toEmbedding)=v by rw [mul_right_comm]; simp [T]]; exact Algebra.mul_smul_comm .. -- tune
lemma cloud_i (S: Finset J)(A:FC J)(h: Flour S A): Flour (S.map e.symm.toEmbedding) (cisT e A):=by
 rw [h.pin,map_sum]; apply Flour.sum; intro i g; rw [coastP]; have ht:i.map e.symm.toEmbedding∈ Wheat (S.map e.symm.toEmbedding):=by obtain ⟨p,q⟩:=mem_filter.mp g; exact mem_filter.mpr ⟨mem_powerset.mpr (map_subset_map.mpr (mem_powerset.mp p)), by rwa [card_map]⟩ -- tune
 obtain ⟨v,s⟩:= coal e i; rw [s]; exact ((Flour.point ht).smul _).smul _
private lemma stem(A:Dough J): Flour univ (cisT e A.val):= (cloud_i e univ A.val (fineShape A)).lift (subset_univ _)
def Artifact (e:I≃J): Dough J→ₐ[ℝ] Dough I where
 toFun x:=⟨cisT e x.val,stem e x⟩
 map_mul' x y:= Subtype.ext (map_mul ..)
 map_add' x y:= Subtype.ext (map_add ..)
 map_zero':= Subtype.ext (map_zero (cisT e))
 map_one':= Subtype.ext (map_one (cisT e))
 commutes' x:= Subtype.ext (by change cisT e ((algebraMap ℝ (FC J)) x)=algebraMap ℝ (FC I) x; simp_rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul ℂ x]; rw [coastP,map_one])
lemma dipV(S:Dough J)(h:ℝ) : Artifact e (dilF h S)=dilF h (Artifact e S):=by
 apply Subtype.ext; change cisT e ((doseN h).eval S.val)=(doseN h).eval (cisT e S.val); rw [(fineShape S).pin,map_sum,map_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=> ?_; rw [map_smul,coastP,coastP,map_smul]; obtain ⟨v,p⟩:=coal e i; rw [Poly.eval_oneT,toneB,coastP,p,map_smul,Poly.eval_oneT,toneB,card_map]; rw [smul_comm ((h:ℂ)^i.card)]
end
end YM.CF.Gully
