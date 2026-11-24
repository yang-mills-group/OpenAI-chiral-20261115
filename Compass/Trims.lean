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
open Pastry Ione Hake Nacre Scree
open Matrix Classical
open scoped Classical
abbrev tolC(X: Support (More N)): Finset (Single N):=univ.filter fun y=> Cube.node y.1.1∈ X
lemma op_rad (Q:Pastry.ribbon (Single N))(X:Support (More N))(p:Flour (camp X) Q.val) (i j:Single N)(h:Haro.orbitPH Q i j≠0): Cube.node i.1.1∈ X∧ Cube.node j.1.1∈ X:=by
 have hi: Prism.portB Q.val (true,i) (false,j)≠0:=h
 rw [Prism.port_eq] at hi
 have hx: ({(true,i),(false,j)}:Finset (LeanV (Single N))) ⊆ camp X:=by
    by_contra g; have hG: ({(true,i),(false,j)}:Finset (LeanV (Single N)))∉ Wheat (camp X):=fun p=>g (mem_powerset.mp (mem_filter.mp p).1)
    rw [p.door hG,mul_zero] at hi; split at hi <;> contradiction
 exact ⟨(mem_filter.mp (hx (Finset.mem_insert_self ..))).2,(mem_filter.mp (hx (mem_insert_of_mem (Finset.mem_singleton_self _)))).2⟩
lemma op_cut (Q: Pastry.ribbon (Single N))(X:Support (More N))(t:Flour (camp X) Q.val):let M:= Haro.orbitPH Q; cutM (tolC X)* M * cutM (tolC X)=M:=by
 intro M; ext i j; let v:= cutM (tolC X); by_cases e: M i j=0; · simp [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,e]
 obtain ⟨a,b⟩:=op_rad Q X t i j e; simp [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,tolC,a,b]
local notation "g"=>Tofu A N
abbrev markT {N:Side}(A:Shape)(X:Support (More N)):Support (More N):=  univ.filter fun i=> A.anon N i∈X
lemma plex (X: Support (More N))(i:Site N): Cube.node i ∈ markT A X ↔ Cube.node (g i)∈ X:=by simp [markT, Shape.nodex, Tofu]
lemma maskV (X: Support (More N)) : cutM (tolC (markT A X)) * (VS).val= (VS).val * cutM (tolC X):=by
 let Z:=tolC (markT A X); let Y:=tolC X; let T:Op (Single N):=(VS).val
 suffices e:cutM Z*T=T*cutM Y from e
 ext i j; change (cutM Z*T) i j=(T*cutM Y) i j
 rw [cutM,cutM,Matrix.diagonal_mul, Matrix.mul_diagonal]
 by_cases h:T i j=0; · change (if i∈Z then (1:ℂ) else 0)*T i j=T i j * _; rw [h,mul_zero,zero_mul]
 have t:= Tye.birth_l i j A U p h
 have hx: i∈Z ↔ j∈Y:=by unfold Z Y tolC; simp only [mem_filter,mem_univ,true_and]; rw [show A.anon N (Cube.node i.1.1)=Cube.node j.1.1 from t]
 change (if i∈Z then _ else _)*T i j=T i j*(if j∈Y then _ else _); by_cases v:j∈Y; rw [if_pos (hx.mpr v),if_pos v, mul_one,one_mul]; rw [if_neg (mt hx.mp v),if_neg v,mul_zero,zero_mul]
-- masks adj $ algebra. general
lemma sign_cut (X:Finset (Single N)): windX p (cutM X)=cutM X:=by cases p; rfl; ext i j; rw [windX,if_pos rfl]; by_cases h:i=j; subst j; change star (cutM X i i)=_; rw [cutM,diagonal_apply_eq]; split <;> simp; change star (cutM X i j)=_; simp [cutM,h]
#print axioms op_cut
#check Tye.birth_l
end YM.CF.Compass
