import YM.SU5.FiniteGaugeData.Tapestry.Belvedere
/-! Multiply even at contact at resolution n: no further lifting needed in the
 n-bill. Useful for n-varying boundary. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking
open Function Finset TensorProduct
open PiTensorProduct (tprod)
open scoped BigOperators Classical
variable {A : Type*} [CommRing A] [Algebra ℂ A] {E : ℕ→Type*} [∀ i,CommRing (E i)][∀ i,Algebra ℂ (E i)]
variable (D:Decking A E)(v:Pad A)

lemma last (x : Cloud A)(n:ℕ)(p:x∈shorter A n)(a:A) : D.crown v n (x*pinhole A n a)=D.crown v n x *D.perceive n a:=by
  apply boarded (M:=fun x=> D.crown v n (x*pinhole A n a)=D.crown v n x *D.perceive n a) (P:={f | Enough n f}) ?_ ?_ ?_ ?_ p
  · intro f (h : Enough n f)
    rw [pinhole_apply]; change D.crown v n (tprod ℂ f*tprod ℂ (update (1:ℕ→ A) n a))=_
    rw [PiTensorProduct.tprod_mul_tprod,D.reckon_paid n v (h.together (enough_slot n a)), D.reckon_paid n v h]
    cases n with
    | zero=> simp [finish]
    | succ n=>
      rw [finish,finish,D.finish_agrees n (g:=f) (fun i hi=> by simp [update_of_ne (show i ≠ n+1 by omega)])]
      simp [mul_assoc]
  · simp only [zero_mul,map_zero]
  · intro x y _ _ a b; rw [add_mul,map_add,map_add,add_mul,a,b]
  intro i x _ z; rw [Algebra.smul_mul_assoc,map_smul,map_smul,Algebra.smul_mul_assoc,z]
end YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Altitude.Decking.last
