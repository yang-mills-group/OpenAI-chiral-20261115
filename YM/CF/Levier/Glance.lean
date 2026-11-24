import YM.CF.Levier.Cane
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
-- dual locally evaluate on conjugated ambient
variable {C:Seal (Site (More P))→Toll (Iota G)}{d p r:ℝ}{v t:Bool}
abbrev homZ(i:Iota G):= (hall G e).home i
def halo: NoteS G e:= fun S _=>diagonal fun i=> if S={homZ G e i} then 1 else 0
lemma halo_p : Bisca G e t t d (Real.exp d) (halo G e):=by
 let CostV(S:Seal (Site (More P)))(i j: κ):ℝ:= if i=j ∧ S={homZ G e i} then 1 else 0
 let T:= pinH G e t; let b:=hall G e
 have hi (S i j)(d:cro G e):halo G e S d i j=↑(CostV S i j):=by unfold halo CostV; by_cases p:i=j; subst j; by_cases h:S={homZ G e i}<;>simp[h]; simp[p]
 have hl i j:saleM d CostV i j= if i=j then Real.exp d else 0:=by unfold saleM; by_cases p:i=j<;> simp [p,CostV,Branch.rent] -- tune
 refine ⟨CostV,fun S=> ⟨⟨?_,?_⟩,fun i j=> (badge (cro G e)).con _⟩,⟨(Real.exp_pos _).le,fun i=>?_,fun i=>?_⟩⟩
 · intro g d; unfold halo; ext i j; rw [diagonal_mul,mul_diagonal]; by_cases h:(hall G e).home i=(hall G e).home j
   · simp only [show homZ G e i=_ from h]; -- tune
     unfold homZ; split <;> simp
   rw [T.keeps _ _ _ h,mul_zero,zero_mul] -- tune
 · intro i j; simp_rw [hi]; unfold CostV; split; next h=>
     refine ⟨zero_le_one,fun _=> ?_,fun x=>by simp,fun x y=>by simpa using (hall G e).pos S x y, continuous_const⟩; rw [h.2]; rw [h.1]; exact ⟨Grove.single _,mem_singleton_self _,mem_singleton_self _⟩
   simp only [Complex.ofReal_zero]; exact nothing ..
 · simp_rw [hl]; simp
 simp_rw [hl]; simp
lemma halo_sum (x:cro G e): ∑ S:Seal (Site (More P)),halo G e S x=1:=by ext i j; rw [Matrix.sum_apply]; by_cases p:i=j<;> simp [p,halo, Matrix.one_apply] -- tune
lemma halo_base (S:Seal (Site (More P)))(x:cro G e): star (halo G e S x)=halo G e S x:=by ext i j; by_cases p:i=j; subst j; by_cases g:S={homZ G e i}<;> simp [halo,g]; simp [halo,p, Ne.symm p]
include h
lemma halo_t (S:Seal (Site (More P)))(x y:cro G e): toSpin G k (halo G e S x)= halo G e (toRoar G k⁻¹ S) y:=by
 apply Epin G; rw [toSpin,steer,port_back]
 let W(d:cro G e)(S:Seal (Site (More P))):= (halo G e S d).submatrix (abbe G).symm (abbe G).symm; have he(d S)(i j:Hand G):tap (W d S) i j= if i=j ∧ S={meetH G true i} then 1 else 0:=by
    ext p q; unfold W; change (halo G e S d) (beamH G i p) (beamH G j q)= _; rw [halo,Matrix.diagonal_apply]; have ht(i j: Hand G)(p q:QuiltF):beamH G i p=beamH G j q ↔ i=j ∧ p=q:=by simp [beamH]
    by_cases h:S={meetH G true i}; · rw [if_pos (show S={homZ G e (beamH G i p)} from h)]; by_cases g:i=j <;> by_cases v:p=q <;>simp [ht,g,v,h,Matrix.one_apply]
    rw [if_neg (show ¬ S={homZ G e (beamH G i p)} from h)]; rw [if_neg (fun t:i=j ∧ S={meetH G true i}=>h t.2)]; simp
 let a:= castX k; let Y:=fros a G (spinU k.charge a.s) (xtra k.charge); suffices H:∀ i j:Hand G,tap (sings k.charge Y (W x S)) i j=tap (W y (toRoar G k⁻¹ S)) i j from by ext ⟨i,p⟩ ⟨j,t⟩; exact congr_fun (congr_fun (H i j) p) t
 intro i j; unfold Y fros; rw [tap_sg,he,he]; have hf:S={meetH G true (paceU a G i)} ↔ toRoar G k⁻¹ S={meetH G true i}:=by
    have hx:= (weaveS G k).injective.eq_iff (a:=toRoar G k⁻¹ S) (b:={meetH G true i}); -- tune names
    rw [← show toRoar G k (toRoar G k⁻¹ S)=toRoar G k _ ↔ _ from hx, wish_inv _ h, toRoar,roarD,image_singleton,meet_x G h] -- tune may rewrite
 simp only [hf,(paceU a G).injective.eq_iff]; split_ifs with hp
 · rw [hp.1,win_i,mul_one]; exact (milU ..).property.2
 rw [win_z,mul_zero,zero_mul]
end YM.CF.Levier
