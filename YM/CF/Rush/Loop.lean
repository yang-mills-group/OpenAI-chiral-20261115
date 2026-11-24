import YM.CF.Rush.Cart
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N F:Side}(G:Ratio N F)
variable {a:Type*}[DecidableEq a][Fintype a]
lemma mark_prod (A B:Momentum→Op a): mark N A*mark N B=mark N fun p=> A p*B p:=by rw [mark,mark,jump_mul]; rfl
lemma mark_sub (A B:Momentum→Op a): mark N A-mark N B=mark N fun p=> A p-B p:= (jump_sub ..).symm
lemma mark_add (A B:Momentum→Op a): mark N A+mark N B=mark N fun p=> A p+B p:= (jump_add ..).symm
lemma mark_adj (A:Momentum→Op a): star (mark N A)=mark N fun p=> star (A p):=by rw [mark,jump_star]; rfl
lemma dropped (A B:Momentum→Op a)(h:∀ p,p∈realCube zone→p≠0→A p=B p): mark N A=mark N B:=by unfold mark; congr 1; exact funext fun k=>h _ (base_subset_realCube zone_pos (mel_h k)) (mel_away k)
lemma unity_m : mark N (fun _=> (1:Op a))=1:= jump_id
lemma deck (A: Momentum→Op a)(x k: Site N)(i j:a): ((overU N a).val*mark N A) (x,i) (k,j)= Fourier N x k * A (mel k) i j:=by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type]; rw [Finset.sum_eq_single k]
  · simp [mark,jump_apply,overU, Matrix.one_apply, mul_ite, ite_mul]
  · intro a _ h; simp [mark,jump_apply,h]
  simp

def blast : (Site N× St G.count) ≃ Site F×SpinIdx:= (Equiv.prodAssoc ..).symm.trans ((isle G).prodCongr (Equiv.refl SpinIdx))
def solo (A: Op (Site F×SpinIdx)): Op (Site N×St G.count):= A.submatrix (blast G) (blast G)
lemma solo_mul (A B):solo G (A*B)=solo G A * solo G B := (Matrix.submatrix_mul_equiv A B _ (blast G) _).symm -- inspect
lemma solo_add (A B): solo G (A+B)=solo G A+solo G B:=rfl
lemma solo_one : solo G 1=1:=by ext i j; simp [solo,Matrix.one_apply]
lemma solo_star (A): solo G (star A) = star (solo G A):=rfl
abbrev balloonG := mark N (trident G.count)
lemma b_unit : balloonG G ∈ unitary (Op (Site N×St G.count)) := jump_unitary _ _ (fun k=>pointed G.count _ (mel_h k).1)

def port (k:Site N)(l:Site G.count): ℂ:= (mode (aliasAt (mel k) l) (offset G.count)*normF N*(G.count.val:ℂ)^2)⁻¹
lemma basis_mode (ho:Odd G.count.val) (x:Site N×St G.count) (k l i) :
    ((overU N (St G.count)).val*balloonG G) x (k,l,i)=
    mode (aliasAt (mel k) l) (natural (blast G x).1)*(port G k l*(1:Op SpinIdx) (blast G x).2 i) :=by
  obtain ⟨x,r,b⟩:=x
  rw [deck]; change Fourier N _ _*trident G.count _ _ _=mode _ (natural (isle G (x,r)))*(port G _ _*_)
  rw [mode_isle G ho]; unfold trident port; change Fourier N x k*_ = _*(_*(1:Op SpinIdx) b i)
  simp only [aliasBlock,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,Fourier]; by_cases he:b=i
  · simp only [if_pos he,Matrix.one_apply, ite_true]; field_simp [normF_ne _]
  simp [he,Matrix.one_apply]

lemma pose (L:Side)(F:Site N→Stk L)(B:Op (Site N×St L))(x k l j) : (B* jump (Equiv.refl _) F) x (k,l,j)=∑ r:St L,B x (k,r)*F k r (l,j):=by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type]; rw [Finset.sum_eq_single k]; simp [jump_apply]; intro a _ h; simp [jump_apply,h]; simp
lemma loop_m (A: Momentum→Op SpinIdx)(f: Cover→Op SpinIdx)(h:Reads f A)(ho:Odd G.count.val):
   solo G (cart F f)= plates N (fun p=> trident G.count p*(stack G.count (fun l=> A (aliasAt p l)))*star (trident G.count p)):=by
  let P :=mark N fun p=> stack G.count fun l=> A (aliasAt p l); let U:=overU N (St G.count); let B:=balloonG G; let T:=U.val*B
  suffices he : solo G (cart F f)*T=T*P by
    rw [plates,twist_formula,show mark N (fun p=>_)= (B*P)*star B from (by unfold B P balloonG; rw [mark_adj,mark_prod,mark_prod])];
    have hh:U.val*(B*P*star B)= T*P*star B:=by unfold T B; simp only [mul_assoc]
    rw [hh,← he]
    unfold T; change _=_*star U.val
    rw [mul_assoc _ _ (star B),mul_assoc _ B,(b_unit G).2,mul_one,mul_assoc, U.property.2,mul_one]
  ext x ⟨k,l,i⟩
  let q:=aliasAt (mel k) l
  have hg : q∈baseCube:= alias_base (mel_h k) l ho
  let v(b: SpinIdx):= port G k l*(1:Op SpinIdx) b i; let X:=blast G x
  calc
    _ = (cart F f *ᵥ (fun y=>mode q (natural y.1)*v y.2)) X := by
      simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct]; conv_rhs=>rw [← Equiv.sum_comp (blast G)]
      exact sum_congr rfl (fun j _=> by rw [show T j (k,l,i)=_ from basis_mode G ho ..]; rfl)
    _ = mode q (natural X.1) * ((A q)*ᵥ v) X.2:=earns h hg (alias_fee G k l) v _ _
    _ = _ := by
      change _=(T*jump (Equiv.refl (Site N)) (fun k=>stack G.count (fun i=> A (aliasAt (mel k) i)))) x (k,l,i)
      rw [pose]; simp only [St,Fintype.sum_prod_type]
      rw [Finset.sum_eq_single l]; swap
      · intro a _ h; simp [s_app,h]
      swap
      · simp
      simp only [s_app,if_true]; simp_rw [T,B,U,basis_mode G ho]; -- compare sums
      simp [Matrix.mulVec,dotProduct,X,q,v,Matrix.one_apply,mul_ite,ite_mul]; ring
end YM.CF.Rush
