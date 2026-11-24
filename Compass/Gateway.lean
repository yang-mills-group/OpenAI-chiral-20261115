import Compass.Trims
import Compass.Sills
import YM.CF.Haro.Cubit
import Compass.Cells
import Compass.Door
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Hake Levier Hove
-- adapt Mantel. sign.
-- check base
open Nacre Ione
variable {N:Side}(A:Shape)(U:UNI SpinIdx)(p r: Bool)(t:JetS A.s p r U)
variable (o x:Site N)(h:10*separation x o < N.val)
local notation "WS"=>twoU U p
local notation "VS"=>siteU A p U N
local notation "ea"=>A.payA
-- leave include t? check head
open Matrix Classical Pastry Scree
open scoped Classical
variable {a b:Type*}[Fintype a][DecidableEq a][Fintype b][DecidableEq b]
lemma tableauMate (U:UNI a)(V:UNI b)(F G:Matrix a b ℂ)(M:Op a)(W Y:Matrix a b ℂ)(L C:Op a) (l q:ℂ)
    (h1:Lᴴ=L)(hl:l*star l=1)(hq:q*star q=1)(hz:windX p L=L)(h0:Cᴴ=C)(hC:C * U.val=U.val * L)
    (hM:L*M*L=M)
    (hF: C *(U.val * foreQ p F)= l •( C * (W*V.val)))
    (hG: C *(U.val * foreQ p G)= q • (C * (Y*V.val))):
    Wᴴ * (sings p U M)* Y = (l * star q) • sings p V (Fᴴ*M*G) := by -- precedence. actually factors! hF says U*F'=l W V. Want W'= l^-1 * U*F' V*. so product = (star l)^-1 q^-1. if |l|=1, l * star q. need phases.
 let X:=windX p M; let B:= U.val*X*star U.val
 have hX:L*X*L=X:=by nth_rw 1 [←hz]; nth_rw 2 [←hz]; exact (show _=_ from (by unfold X; rw [←win_m,←win_m,hM])) -- second occurrence indexing
 have h':star U.val*C=Lᴴ*star U.val:=by
    have hr:= congrArg Matrix.conjTranspose hC; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,h0] at hr; exact hr
 -- if Lᴴ=L require
 have hB (uL:Lᴴ=L): C* B* C=B:=by
    rw [uL] at h'; unfold B; rw [show C*(U.val*X*star _)=(C*U.val)*X*star U.val from (by simp only [mul_assoc]), hC, mul_assoc _ (star U.val),h']; rw [show U.val* L *X *(L*star U.val)= U.val*(L*X*L)*star U.val from (by simp only [mul_assoc]),hX]
 have he: sings p V (Fᴴ*M*G)= (star l*q) • (Wᴴ*B*Y):=by
    let f':= U.val * foreQ p F
    let g':= U.val * foreQ p G
    let v':=V.val
    have hv:windX p (Fᴴ*M*G)= f'ᴴ* B*g':=by
       rw [←foreS, fore_mul, fore_mul,fore_adj,foreS]; unfold B X f' g'; simp only [Matrix.conjTranspose_mul]; change _=((foreQ p F)ᴴ*star U.val)*(U.val*_*star U.val)*(_*_)
       generalize hs:windX p M=Z; generalize ht:foreQ p G=u0; generalize hz:(foreQ p F)ᴴ=A0
       rw [show A0* star U.val*(U.val*Z*star U.val)*(U.val*u0) = A0*(star U.val*U.val)*Z*(star U.val*U.val)*u0 from (by simp only [Matrix.mul_assoc]),U.property.1,Matrix.mul_one,Matrix.mul_one]
    have hz:v' *((C*(W *v'))ᴴ* B*(C*(Y*v')))*star v' = Wᴴ*B*Y:=by
       simp only [Matrix.conjTranspose_mul,h0]
       rw [show v' *(v'ᴴ*Wᴴ*C*B*(C*(Y*v')))*star v'= (v'*star v') *Wᴴ*(C*B*C)*Y*(v'*star v') from (by simp only [Matrix.mul_assoc]; rfl),show v'*star v'=1 from V.property.2, hB h1, Matrix.one_mul,Matrix.mul_one]
    rw [singT,twist_formula,hv,show f'ᴴ*B*g'=(C*f')ᴴ*B*(C*g') by rw [Matrix.conjTranspose_mul C f',h0]; symm; rw [show f'ᴴ*C*B*(C*g')=f'ᴴ*(C*B*C)*g' by simp only [Matrix.mul_assoc], hB h1],hF,hG,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_smul, Matrix.smul_mul,Matrix.smul_mul,smul_smul]; rw [mul_comm q]; exact congrArg (fun i=> (star l * q) • i) hz
 rw [he,smul_smul,show l*star q*(star l*q)=1 from ?_,one_smul]; rfl
 calc
 _=l*star l*(q*star q) := by ring
 _=1 :=by rw [hl,hq,mul_one]
end YM.CF.Compass
