import Zephyr.Chern.Fast
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice 


/-- The scalar Laurent algebra. -/
@[ext]
structure Silk where
  co : Cover → ℂ
  fast : Fast co

namespace Silk
variable (a b c : Silk)

private def v : Brill → ℂ := vista a.co

private lemma v_inj : Function.Injective v := by
  intro a b h
  apply Silk.ext; funext x
  rw [←recover a.fast x,←recover b.fast x, show vista a.co= vista b.co from h]

instance : Add Silk where add a b := ⟨a.co+b.co,a.fast.add b.fast⟩
instance : Mul Silk where mul a b := ⟨pile a.co b.co,a.fast.pile b.fast⟩
instance : Neg Silk where neg a := ⟨-a.co,a.fast.neg⟩
instance : Sub Silk where sub a b := a+ -b

private def con (z : ℂ) : Silk := ⟨echo z,fast_echo z⟩
private lemma v_con (z) (t) : v (con z) t=z := vista_echo z t

instance : Zero Silk := ⟨con 0⟩
instance : One Silk := ⟨con 1⟩
instance : NatCast Silk := ⟨fun n => con n⟩
instance : IntCast Silk := ⟨fun n => con n⟩
instance : SMul ℕ Silk := ⟨fun n a => con n * a⟩
instance : SMul ℤ Silk := ⟨fun n a => con n * a⟩

instance : Pow Silk ℕ where pow a n := Nat.rec (motive:=fun _ => Silk) (con 1) (fun _ b => b*a) n

private lemma v_add : v (a+b)=v a+v b := vista_add a.fast b.fast
private lemma v_neg : v (-a)= -v a := vista_neg _

private lemma v_mul : v (a*b)=v a*v b := vista_prod a.fast b.fast

instance : CommRing Silk := Function.Injective.commRing v v_inj
  (funext (v_con 0)) (funext (v_con 1)) v_add v_mul v_neg
  (fun x y => by rw [show x-y=x+ -y by rfl,v_add,v_neg,sub_eq_add_neg])
  (fun n x => by
    change v (con n * x) = _
    rw [v_mul, nsmul_eq_mul, show v (con n)= (n : Brill→ℂ) from funext (fun t=> by rw [v_con]; simp)])
  (fun n x => by
    change v (con n * x) = _
    rw [v_mul, zsmul_eq_mul, show v (con n)= (n : Brill→ℂ) from funext (fun t=> by rw [v_con]; simp)])
  (fun x n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact funext (v_con 1)
    | succ n ih =>
      change v (x^n * x) = _
      rw [v_mul, ih, pow_succ])
  (fun n => funext (fun t => by simpa using! v_con n t))
  (fun n => funext (fun t => by simpa using! v_con n t))

private def view : Silk →+* Brill → ℂ where
  toFun := v
  map_one' := funext (v_con 1)
  map_zero' := funext (v_con 0)
  map_add' := v_add
  map_mul' := v_mul

private def constants : ℂ →+* Silk where
  toFun := con
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := v_inj (funext fun t => by rw [v_add,Pi.add_apply,v_con,v_con,v_con])
  map_mul' x y := v_inj (funext fun t => by rw [v_mul,Pi.mul_apply,v_con,v_con,v_con])

instance : Algebra ℂ Silk := constants.toAlgebra

lemma co_add (x) : (a+b).co x=a.co x+b.co x := rfl
lemma co_mul (x) : (a*b).co x= ∑' y,a.co y*b.co (x-y) := rfl
lemma co_algebraMap (z : ℂ) : (algebraMap ℂ Silk z).co = echo z := rfl

lemma co_smul (z : ℂ) (x) : (z • a).co x=z*a.co x := by
  rw [Algebra.smul_def,co_mul,co_algebraMap, tsum_eq_single 0]
  · simp [echo]
  intro i h; simp [echo,h]

/-- Evaluation, on the periodic torus. -/
def E (t : Brill) : Silk →ₐ[ℂ] ℂ where
  __ := (Pi.evalRingHom (fun _ => ℂ) t).comp view
  commutes' z := v_con z t

lemma E_eq (t : Brill) : E t a = vista a.co t := rfl

lemma E_ext {f g : Silk} (h : ∀ t, E t f = E t g) : f = g := v_inj (funext h)

instance : Nontrivial Silk where
  exists_pair_ne := ⟨1,0,fun h => by have e:= congrArg (E 0) h; simp at e⟩

lemma E_cont : Continuous (fun t => E t a) := vista_cont a.fast

/-- Fourier coefficient linear functional. -/
def coeff (x : Cover) : Silk →ₗ[ℂ] ℂ where
  toFun a := a.co x
  map_add' _ _ := rfl
  map_smul' z b := co_smul b z x

lemma coeff_apply (x : Cover) (f : Silk) : coeff x f=f.co x := rfl

/-- Normalized average. -/
abbrev τ := coeff 0

open YM.Laurent MeasureTheory
lemma integral : ∫ t, E t a ∂globe Axis=τ a := by
  simpa only [neg_zero,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,mul_one]
    using! recover a.fast 0

end Silk
