import YM.SU5.FiniteGaugeData.Tapestry.CrownState
import Mathlib.LinearAlgebra.Complex.Module
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
/-! # Actions on resolution polynomials -/
namespace YM.CF.Buffered.Afterglow.Tapestry.Altitude
open Function Filter Finset TensorProduct
open scoped BigOperators Classical ComplexConjugate
open PiTensorProduct
variable {A:Type*}[CommRing A][Algebra ℂ A]
variable {χ : ℂ→+*ℂ}(o: ℕ→ A→ₛₗ[χ] A)

def plumeTail(f:ℕ→A) : ℕ→ A:=fun i=> o i (f i)
lemma plank [DecidableEq ℕ](f:ℕ→A)(i:ℕ)(z:A) : plumeTail o (update f i z)=update (plumeTail o f) i (o i z):=by
 funext j; by_cases h:j=i
 · subst j; unfold plumeTail; simp [update_self]
 unfold plumeTail; simp [update_of_ne h]

def plumeAdd : Cloud A →+ Cloud A:=
  PiTensorProduct.liftAddHom (R:=ℂ) (s:=fun _:ℕ=>A) (fun (x:ℂ × (ℕ→A))=> χ x.1 • tprod ℂ (plumeTail o x.2))
    (fun r f i e=> by change χ r • tprod ℂ (plumeTail o f)=_; rw [(tprod ℂ).map_coord_zero i (show plumeTail o f i=0 from (by unfold plumeTail; rw [e,_root_.map_zero])),smul_zero])
    (fun f=> by change χ 0 • _=_; rw [_root_.map_zero,zero_smul])
    (fun {h} r f i x y=>by dsimp only; simp_rw [plank]; rw [_root_.map_add, (tprod ℂ).map_update_add, smul_add])
    (fun r r' x=>by dsimp only; rw [_root_.map_add,add_smul])
    (fun {h} r f i s=>by dsimp only; rw [plank, LinearMap.map_smulₛₗ]; change χ r • tprod ℂ (update (plumeTail o f) i (χ s • plumeTail o f i))=_; rw [ (tprod ℂ).map_update_smul, update_eq_self,smul_smul, _root_.map_mul,mul_comm (χ r) (χ s)] ) -- tune

lemma plumeAdd_coeff (r:ℂ)(f:ℕ→A): plumeAdd o (tprodCoeff ℂ r f)=χ r • tprod ℂ (plumeTail o f):=rfl

def plume : Cloud A→ₛₗ[χ] Cloud A where
 toFun:= plumeAdd o
 map_add':= _root_.map_add (plumeAdd o)
 map_smul' r x:= by
   induction x using PiTensorProduct.induction_on' with
   | tprodCoeff s f=> rw [smul_tprodCoeff', plumeAdd_coeff,plumeAdd_coeff, smul_eq_mul, _root_.map_mul,mul_smul]
   | add x y u v=> rw [smul_add,_root_.map_add,u,v,_root_.map_add,smul_add]

@[simp] lemma pluage (x:ℕ→A): plume o (tprod ℂ x)=tprod ℂ (plumeTail o x):= (plumeAdd_coeff o 1 x).trans (by rw [_root_.map_one,one_smul])

lemma plumeExtend {P Q:Set (ℕ→A)}(h: ∀ x∈P, plumeTail o x∈Q){x:Cloud A}(p:x∈heights P): plume o x∈ heights Q:= by
 apply boarded (P:=P) (M:=fun x=>_) ?_ ?_ ?_ ?_ p
 · intro f q; rw [pluage]; exact board (h f q)
 · rw [_root_.map_zero]; exact (heights Q).zero_mem
 · intro p q h v u w; rw [_root_.map_add]; exact (heights Q).add_mem u w
 intro r p u w; rw [LinearMap.map_smulₛₗ]; exact (heights Q).smul_mem _ w

variable (e : ∀ i, o i 1=1)(k: ∀ i x y, o i (x*y)=o i x * o i y)
include k
lemma plumeTimes (x y:Cloud A): plume o (x*y)=plume o x*plume o y:=by
  induction x using PiTensorProduct.induction_on with
  | add x y h t=> rw [add_mul,_root_.map_add,h,t,_root_.map_add,add_mul]
  | smul_tprod c f=>
    rw [Algebra.smul_mul_assoc,LinearMap.map_smulₛₗ,LinearMap.map_smulₛₗ,Algebra.smul_mul_assoc];apply congrArg
    induction y using PiTensorProduct.induction_on with
    | add x y u v=> rw [mul_add,_root_.map_add,u,v,_root_.map_add,mul_add]
    | smul_tprod p x=> rw [Algebra.mul_smul_comm,LinearMap.map_smulₛₗ,LinearMap.map_smulₛₗ, Algebra.mul_smul_comm]; simp_rw [tprod_mul_tprod,pluage]; rw [tprod_mul_tprod]; exact congrArg (fun v=> _ • tprod ℂ v) (funext fun i=> k i (f i) (x i))
omit k
include e
lemma plumeUnit : plume o 1=1:=by rw [PiTensorProduct.one_def,pluage]; exact congrArg (tprod ℂ) (funext e) -- RHS rewritten η
lemma plumeEnough {f:ℕ→ A}{n:ℕ}(p:Enough n f) : Enough n (plumeTail o f):= fun i h=>by unfold plumeTail; rw [p i h,e]
lemma plumeCut (n:ℕ) {x:Cloud A}(p:x∈shorter A n) : plume o x∈shorter A n:= plumeExtend o (P:={f|Enough n f}) (Q:={f|Enough n f}) (fun f p=> plumeEnough o e p) p
lemma plumePolynomial{x: Cloud A}(p:x∈Polynomials A): plume o x∈ Polynomials A:=by obtain ⟨n,p⟩:=curve.mp p; exact curve.mpr ⟨n,plumeCut o e n p⟩
omit e

lemma lipMap (F G:Cloud A →ₛₗ[χ] Cloud A)(p:∀ f:ℕ→ A,F (tprod ℂ f)=G (tprod ℂ f)) : F=G:=by
 refine LinearMap.ext fun x=>?_ ; induction x using PiTensorProduct.induction_on with
 | add x y h t=> rw [_root_.map_add,h,t,_root_.map_add]
 | smul_tprod r v=> rw [LinearMap.map_smulₛₗ,p,LinearMap.map_smulₛₗ]

lemma plumeTogether {ψ μ:ℂ→+*ℂ}[RingHomCompTriple ψ χ μ] (p:ℕ→ A→ₛₗ[ψ]A) : (plume o).comp (plume p) = plume (χ:=μ) (fun i=>(o i).comp (p i)):= -- binder μ comp not inferred on lhs
 lipMap _ _ fun f=>by rw [LinearMap.comp_apply,pluage,pluage,pluage]; rfl
@[simp] lemma plume_id : plume (fun _:ℕ=>LinearMap.id (M:=A) (R:=ℂ))=LinearMap.id := lipMap _ _ fun v=>pluage ..
lemma flare (R:ℕ→A→ₗ⋆[ℂ]A)(e:∀ i x,R i (R i x)=x) : Function.Involutive (plume R) := by
 let G:Cloud A→ₗ[ℂ]Cloud A:= (plume R).comp (plume R)
 have h:G=LinearMap.id:=by
   apply lipMap; intro f; unfold G; rw [LinearMap.comp_apply,pluage,pluage,LinearMap.id_apply]; exact congrArg (tprod ℂ) (funext fun i=> e i (f i))
 exact fun x=> show G x=x from by rw [h]; rfl

end YM.CF.Buffered.Afterglow.Tapestry.Altitude
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.flare
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.plumeTimes
