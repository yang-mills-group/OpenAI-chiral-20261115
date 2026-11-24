import YM.CF.Song.Agape
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
variable {n:Side}
/- adapted from θS for public linear map. -/
abbrev ionX (k:ℕ)(u:1≤k)(M: Male) : Op (Single n)→ₗ[ℝ] Op Slot:=by
 let L(F:Op (Single n))(p:ℝ):=potion k M (heroP F) (bout 0 p)
 have he(F):DifferentiableAt ℝ (L F) 0:=by
    have hp:DifferentiableAt ℝ (fun p:ℝ=> heroP F (bout 0 p)) 0:=by unfold heroP; apply DifferentiableAt.fun_sum; intro j _; unfold Laurent.mode Tap.bout; fun_prop
    let h:= (barox k u M 0).differentiableAt; exact (((differentiableAt_const 1).sub h).mul hp).mul h
 let T: Op (Single n)→ₗ[ℝ] Op Slot :=
   { toFun:=fun F=>zeus k M (heroP F)
     map_add':=fun i j=>by
       have hp:L (i+j)= L i+L j:=by
          funext x; unfold L potion; let v:=bout 0 x; rw [show heroP (i+j) (bout _ _)=heroP i v+heroP j v from ?_, mul_add,add_mul]; rfl; apply eq_add_of_sub_eq; rw [←Exa.weights,add_sub_cancel_right]
       change spaX (deriv (L _) 0) 0=spaX (deriv (L _) 0) 0+spaX (deriv (L _) 0) 0; rw [hp,deriv_add (he i) (he j),pedal]
     map_smul':=fun r F=>by
       have hp:L (r • F)= fun x:ℝ=>r • L F x:=by funext x; unfold L potion; rw [coreF,Matrix.mul_smul,Matrix.smul_mul]
       change spaX (deriv (L _) 0) 0=r • spaX (deriv (L _) 0) 0; rw [hp]; change spaX (deriv (r • L F) 0) 0=_; rw [((he F).hasDerivAt.const_smul r).deriv,pedal_r] }
 exact T
end YM.CF.Haro
