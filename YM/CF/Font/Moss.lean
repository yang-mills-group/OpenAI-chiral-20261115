import YM.CF.Font.Mints
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L c f n:Side}{a b A B:ℝ}{m:ℕ}
abbrev TaxX (m:ℕ)(G:Gauge):= ContinuousMultilinearMap ℝ (fun _:Fin m=>G.Color) ℂ
abbrev Toy(m:ℕ)(n:Side):= Emit m n (TaxX m SU.group)
def pyre {G:Gauge}(X:Emit m n (TaxX m G))(A:fieldDir G (More n) 1): Op (Single n):=Matrix.of fun i j=> ∑ r:Trip m n, X i j r (fun u=>heat (place_x i) (collect G A) (r u))
theorem tap_paid (G:Gauge)(K:Single f→Single c→PrizeX f→ PrizeX c→ℝ)(Z:fieldDir G (More f) 1)(W:fieldDir G (More c) 1)(h:∀ x i j,heat (place_x x) (collect G Z) j=∑ z,K x i j z • heat (place_x i) (collect G W) z)(U V:Matrix (Single f) (Single c) ℂ)(P:Emit m f (TaxX m G)): pyre (tapH U V K P) W=Matrix.conjTranspose U * pyre P Z * V:=by
 ext x y
 let X i:= K i x; let Y (r:Trip m c)(u:Fin m):= heat (place_x x) (collect G W) (r u)
 have he(i:Single f)(r:Trip m f): (heat (place_x i) (collect G Z) ∘ r)=fun u=>∑ z, K i x (r u) z • heat (place_x x) (collect G W) z:= funext (fun s=> h i x (r s))
 have hv i j (r:Trip m f): P i j r (heat (place_x i) (collect G Z) ∘ r)= ∑ t:Trip m c, (∏ u:Fin m,X i (r u) (t u)) • P i j r (Y t):=by
    rw [he,ContinuousMultilinearMap.map_sum]; refine sum_congr rfl fun t _ => ?_; exact MultilinearMap.map_smul_univ (P i j r).toMultilinearMap _ (Y t)
 change (∑ t:Trip m c,(tapH U V K P) x y t (Y t))=(Matrix.conjTranspose U * pyre P Z *V) x y
 simp only [tapH,Matrix.mul_apply,pyre,Matrix.of_apply]; -- tune
 simp only [_root_.sum_apply,_root_.smul_apply,Matrix.conjTranspose_apply,smul_eq_mul]; simp only [Function.comp_def] at hv; simp_rw [hv,mul_sum,sum_mul,Complex.real_smul]; rw [sum_comm]; conv_rhs=> rw [sum_comm]
 refine sum_congr rfl fun i _ => ?_; rw [sum_comm]; refine sum_congr rfl fun j _=>?_ ; rw [sum_comm]; refine sum_congr rfl fun r _=>?_ ; refine sum_congr rfl fun t _=>?_; unfold X; ring
end YM.CF.Font
