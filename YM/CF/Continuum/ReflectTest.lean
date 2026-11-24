import YM.CF.Continuum.Square
/-! # One normalization, PSD statement
    Together with exact mirror (`expectationsMirror`) and bounds on real
    reflected square components for every `F∈nonnegativeTime` suffices. May
    also test by complex-order without separate symmetry hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Fock Lattice Lat MeasureTheory Filter Finset Cube Wilson RG
open scoped Topology InnerProductSpace BigOperators Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192

variable {m B:Side} (i:Axis)
local notation "Λ"=> CSide m B
local notation "A₊"=> nonnegativeTime m B i
local notation "Γ"=> allObs (CSide m B)

structure TestOK (m B:Side) (i:Axis)(f:Evaluation (CSide m B)→ℂ) : Prop where
   summed {X Y} : X∈ allObs (CSide m B)→Y∈ allObs (CSide m B)→f (X+Y)=f X+f Y
   scaled {X} : X∈ allObs (CSide m B)→ ∀ c:ℂ, f (c • X)=c*f X
   squares {X} : X∈ nonnegativeTime m B i→0 ≤ crossForm m B i f X X

variable {f: Evaluation (CSide m B)→ℂ} (K:TestOK m B i f){X Y Z:Evaluation (CSide m B)}(e:X∈(nonnegativeTime m B i))(w:Y∈(nonnegativeTime m B i))(z:Z∈(nonnegativeTime m B i))
namespace TestOK
local notation "Q"=> crossForm m B i f
include K e w z
private lemma right_plus : Q X (Y+Z)=Q X Y+ Q X Z:=by
 unfold crossForm; rw [mul_add, K.summed]; exact (allObs (CSide m B)).mul_mem (flipTime_all _ (fits_all e)) (fits_all w); exact (allObs (CSide m B)).mul_mem (flipTime_all _ (fits_all e)) (fits_all z)
private lemma left_plus : Q (X+Y) Z=Q X Z+Q Y Z:=by
 unfold crossForm; rw [flipTime_plus,add_mul,K.summed]; exact (allObs (CSide m B)).mul_mem (flipTime_all _ (fits_all e)) (fits_all z); exact (allObs (CSide m B)).mul_mem (flipTime_all _ (fits_all w)) (fits_all z)
omit z
private lemma right_scalar (c:ℂ) : Q X (c•Y)=c*Q X Y:=by
 unfold crossForm; rw [Algebra.mul_smul_comm]; exact K.scaled ((allObs (CSide m B)).mul_mem (flipTime_all _ (fits_all e)) (fits_all w)) c
private lemma left_scalar (c:ℂ) : Q (c•X) Y=star c * Q X Y:=by unfold crossForm; rw [flipTime_smul, Algebra.smul_mul_assoc]; exact K.scaled ((allObs (CSide m B)).mul_mem (flipTime_all _ (fits_all e)) (fits_all w)) (star c)
private lemma aligned_entry : star (Q Y X)= Q X Y:=by
  have he(Z : Evaluation Λ)(hZ:Z∈A₊) : (Q Z Z).im = 0 :=((Complex.le_def.mp (K.squares hZ)).2).symm
  have h1:=he _ e; have h2:=he _ w; have q:=he _ ((nonnegativeTime m B i).add_mem e w); have p:= (nonnegativeTime m B i).smul_mem w Complex.I; have g:=he _ ((nonnegativeTime m B i).add_mem e p)
  rw [K.left_plus i e w ((nonnegativeTime m B i).add_mem e w), K.right_plus i e e w, K.right_plus i w e w] at q
  rw [K.left_plus i e p ((nonnegativeTime m B i).add_mem e p), K.right_plus i e e p, K.right_plus i p e p, K.left_scalar i w e, K.left_scalar i w p, K.right_scalar i e w, K.right_scalar i w w] at g
  simp [h1,h2,Complex.mul_re, Complex.mul_im] at q g; apply Complex.ext<;> simp <;> linarith
omit e w
variable {I:Type*}[Fintype I]{T:I→Evaluation (CSide m B)}(h : ∀ j,T j∈ (nonnegativeTime m B i))
include h
lemma ref_matrix : (reflectionForm i f T).PosSemidef:=by
 classical
 apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; constructor
 · ext a b; exact K.aligned_entry i (h a) (h b) -- ext complex?
 intro x
 have ht:∀ a, x a • T a∈A₊:=fun j=>(nonnegativeTime m B i).smul_mem (h j) _
 let A:=∑ a,x a • T a; have ha:A∈A₊:= Subalgebra.sum_mem _ fun j _=>ht j
 have he : Q A A=∑ a,star (x a) * ∑ b, Q (T a) (T b)*x b:=by
   have hA : (fun Z:A₊=>Q A Z.val)= (fun Z=>∑ a, star (x a) * Q (T a) Z.val):=by
     funext Z; let L : A₊ →ₗ⋆[ℂ] ℂ :=
       { toFun :=fun V=> Q V.val Z.val
         map_add' := fun V W=> K.left_plus i V.property W.property Z.property
         map_smul' := fun c V=> K.left_scalar i V.property Z.property c }
     let y j:A₊:=⟨T j,h j⟩; have hx : A=((∑ j,x j • y j): A₊).val:=by rw [show ((∑ j,x j • y j):A₊).val=∑ j,(((x j • y j):A₊).val) from map_sum (nonnegativeTime m B i).val ..]; simp_rw [Subalgebra.coe_smul]; rfl
     rw [hx]; exact ((map_sum L ..).trans (sum_congr rfl fun k _=> L.map_smulₛₗ ..))
   have hB a : Q (T a) A=∑ b, Q (T a) (T b)*x b:=by
     let L : A₊→ₗ[ℂ]ℂ:=
       { toFun:=fun P=> Q (T a) P.val
         map_add':=fun P Q'=>K.right_plus i (h a) P.property Q'.property
         map_smul':=fun c P=>K.right_scalar i (h a) P.property c }
     let y j:A₊:=⟨T j,h j⟩; rw [show A=((∑ j,x j • y j):A₊).val by rw [show ((∑ j,x j • y j):A₊).val=∑ j,(((x j • y j):A₊).val) from map_sum (nonnegativeTime m B i).val ..]; simp_rw [Subalgebra.coe_smul]; rfl]; exact (map_sum L ..).trans (sum_congr rfl fun j _=>by rw [map_smul]; exact mul_comm ..)
   refine (congrFun hA ⟨A,ha⟩).trans ?_; simp_rw [hB]
 change 0 ≤ ∑ a,star (x a)*∑ b,Q (T a) (T b)*x b; rw [←he]; exact K.squares ha
omit K h
lemma passage {fₜ:ℕ→Evaluation Λ→ℂ} (p:∀ᶠ t in atTop,TestOK m B i (fₜ t)) (g:∀ X∈Γ,Tendsto (fun t=>fₜ t X) atTop (𝓝 (f X))) : TestOK m B i f:=by
 constructor
 · intro X Y u v; exact tendsto_nhds_unique_of_eventuallyEq (g _ ((allObs (CSide m B)).add_mem u v)) ((g _ u).add (g _ v)) (p.mono fun _ w=> w.summed u v)
 · intro X e c; exact tendsto_nhds_unique_of_eventuallyEq (g _ ((allObs (CSide m B)).smul_mem e c)) ((g _ e).const_mul _) (p.mono fun _ w=> w.scaled e c)
 intro X e; exact ge_of_tendsto (g _ ((allObs (CSide m B)).mul_mem (flipTime_all _ (fits_all e)) (fits_all e))) (p.mono fun _ w=> w.squares e)
end TestOK
end YM.CF.Window
