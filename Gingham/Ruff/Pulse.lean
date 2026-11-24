import Gingham.Ruff.Throb
import YM.CF.Fock.Glacier

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]


/-! Right commutator errors have no T left in their input-letter
 substitution. Exterior height can be left unchanged. -/

def spur (S W:Op n) (b:Bool) : Op n :=
  if b then -(W*(1-S)) else (S*W)ᵀ
def hitch (S W:Op n) : Op (LeanV n) :=
  fun i j => if i.1=j.1 then (spur S W i.1) i.2 j.2 else 0

variable {S : Op n}
lemma stir_take (M:Op n) (v:Ket n) :
    shock (dg M) (Fock.remove v) = -Fock.remove (acts (star M) v) := by
  have h : star (dg (star M)) = dg M := by rw [←dg_star,star_star]
  have y := congrArg star (lever (star M) v)
  rw [star_sub,star_mul,star_mul,h] at y
  change dg M * star (create v)-star (create v)*dg M = -star _
  rw [←y,neg_sub]

lemma stir_seek (h : IsStarProjection S) (T W : Op n) (i:n) :
    shock (𝒵 S T W) (seekF S i)= prong (seekF S) (spur S W true) i := by
  rw [𝒵,shock_scal,seekF,prong_p,
      show ∀ (K:Op n) (v), shock (dg K) (create v) = create (acts K v) from lever,
      ←act_mul,sheaf_q h]
  rw [prong_ply,spur,if_pos rfl,mul_neg,←mul_assoc,prong_p,act_neg,map_neg]


lemma stir_hide (h : IsStarProjection S) (T W : Op n) (i:n) :
    shock (𝒵 S T W) (hideF S i)= prong (hideF S) (spur S W false) i := by
  have z : star (sheaf S T W) * S = S * star W * S := by
    simpa only [star_mul,h.isSelfAdjoint.star_eq,mul_assoc] using
       congrArg star (sheaf_p h T W)
  have u : spur S W false = cc (star W * S) := by
    rw [spur,if_neg (show false ≠ true by decide),
      show star W * S = star (S*W) by rw [star_mul,h.isSelfAdjoint]]
    change (S*W)ᵀ=((star (star (S*W)))ᵀ)
    rw [star_star]
  rw [𝒵,shock_scal,hideF,prong_t,stir_take,
      ←act_mul,z,prong_ply,u,←cc_mul,←mul_assoc,
      prong_t,neg_neg]

lemma stir_draw (h : IsStarProjection S) (T W : Op n) (i: LeanV n) :
    shock (𝒵 S T W) (drawT S i)=
    ∑ j:LeanV n, hitch S W j i • drawT S j := by
  rcases i with ⟨b,i⟩
  rw [Fintype.sum_prod_type,sum_eq_single b]
  · cases b
    · change shock _ (hideF S i)=_
      rw [stir_hide h]; simp [hitch,prong,drawT]
    change shock _ (seekF S i)=_
    rw [stir_seek h]; simp [hitch,prong,drawT]
  · intro j _ p; simp [hitch,p]
  simp


lemma stir_tank (h : IsStarProjection S) (T W : Op n) (r : ribbon n) :
    shock (𝒵 S T W) (tank S r)= tank S (jolt (hitch S W) r) :=
  shock_lift _ _ (nursery S h) (stir_draw h T W) r

lemma striking (Z X : FC n) (q:Wave n) (k : acts Z q=0) :
    acts Z (acts X q) = acts (shock Z X) q := by
  change _ = acts (Z*X-X*Z) q
  rw [act_sub,act_mul,act_mul,k,map_zero,sub_zero]

