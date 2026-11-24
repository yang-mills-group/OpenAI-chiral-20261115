import YM.CF.Emu.Fill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{M:Jill.Male}{R:ℝ}{d:Candle}
lemma dent(x y:Single N)(A:Stag N→ Peb):Dofu N A x y= if x.2=y.2 then ∑ k:Site N, Fourier N x.1.1 k*A (k,x.2) x.1.2 y.1.2*star (Fourier N y.1.1 k) else 0:=by
 change twist _ (arch A) x y=_; rw [twist_formula,Matrix.mul_apply]; -- wool
 rw [Fintype.sum_prod_type]; simp_rw [wool,Matrix.star_apply, coil]; -- inspect. Star matrix formula notation
 rw [Fintype.sum_prod_type]; by_cases h:x.2=y.2
 · rw [if_pos h]; apply sum_congr rfl; intro k _; rw [sum_eq_single y.1.2]; swap
   · intro l _ e; simp only [Ne.symm e,false_and,ite_false,star_zero,mul_zero,sum_const_zero]
   swap; · simp
   rw [sum_eq_single x.2]; simp only [true_and,h,eq_self,ite_true]; intro b _ e; simp only [Ne.symm e,ite_false,zero_mul]; simp -- tune
 rw [if_neg h]; apply sum_eq_zero; intro k _; apply sum_eq_zero; intro b _; apply sum_eq_zero; intro c _; split_ifs with v w <;> first|simp |grind
 exact False.elim (h (v.trans w.2.symm))
lemma rho_m (p:Momentum)(g: star p=p)(x y: Cover): mode p (x-y)=mode p x*star (mode p y):=by rw [sub_eq_add_neg,mode_shift]; nth_rw 4 [←g]; rw [mode_adjoint] -- tune
lemma sapling (s:Slide N d)(x y:Cover)(o:Site N)(k:Site N)(a:Wing): let i:=hub a o x; let t:=hub a o y; let A(X:Cover):=wind o X *star (newm d X a.x); star (A x)* A y*Fourier N i.1.1 k * star (Fourier N t.1.1 k)= ((N.val:ℂ)^4)⁻¹ * mode (tmap (Kea.angle s (k,a.x))) (x-y):=by
 intro i t A
 let B:= tmap (Kea.angle s (k,a.x)); let C:= Fourier N o k
 have he(p:Cover): star (A p)*Fourier N (o+wrap N p) k=C*mode B p:=by unfold A; rw [star_mul, star_star, show star (wind o p)=wind o p from fee_real _,mul_assoc]; exact further s o k _ p
 have h₁:=congrArg star (he y); unfold t i hub; change _* _* Fourier N _ _ * star (Fourier N _ _) =_
 rw [mul_right_comm (star (A x)), he x,mul_assoc (C*_), show A y* star (Fourier N (o+wrap N y) k)=star (C * mode B y) from ?_, star_mul]; swap; · rw [star_mul,star_star,mul_comm] at h₁; exact h₁
 have hz: C *star C= ((N.val:ℂ)^4)⁻¹:=by
    unfold C Fourier; simp only [Matrix.of_apply,star_div₀]; rw [div_mul_div_comm,mul_comm (frequency k o),frequency_unit]; unfold normF; simp only [star_pow,star_natCast,one_div]; ring -- tune
 rw [rho_m _ (tmap_physical _),←hz]; ring -- tune B def
lemma mist (s:Slide N d)(o:Site N)(x y:Cover)(a b:Wing)(A: Stag N→Peb)(R:ℝ): let U:= Dofu N A; let X:=hint o x a (Kea.tax d) 1; let Y:=hint o y b (Kea.tax d) 1; (R:ℂ)^3*inner ℂ X (acts U Y)= if a.x=b.x then bore (s.u a.x) R (x-y) (trackF s A a.x) a.a b.a else 0:=by
 intro U X Y; unfold X Y; rw [tax_f,tax_f,map_smul,inner_smul_left,inner_smul_right,basis_inner,basis_act]; by_cases h:a.x=b.x
 swap; · rw [if_neg h]; unfold U; rw [dent,if_neg (show (hub a o x).2≠(hub b o y).2 from h)]; simp
 rw [if_pos h]; unfold U; rw [dent,if_pos (show (hub a o x).2=(hub b o y).2 from h)]
 let X:=hub a o x; let Y:=hub b o y; unfold bore liv; rw [← BZ.ofReal_action, Matrix.smul_apply,Matrix.sum_apply];
 conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight (wrap N (s.z a.x))) (fun i=> (charK (s.u a.x) i (x-y) • trackF s A a.x i) a.a b.a)]
 rw [← h]; push_cast; simp_rw [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]; apply sum_congr rfl; intro i _; let G:Site N:=i+wrap N (s.z a.x); change _ = (R:ℂ)^3 /((N.val:ℂ)^4)*(charK (s.u a.x) G (x-y)* (A (rake s G a.x) a.a b.a)); rw [show rake s G a.x=(i,a.x) from Prod.ext (add_sub_cancel_right ..) rfl]; let W(z:Cover):= wind o z * star (newm d z a.x); let X:=Fourier N (o+wrap _ x) i; let Y:=Fourier N (o+wrap _ y) i; let K:=charK (s.u a.x) G (x-y); let T:= A (i,a.x) a.a b.a; have hz: star (W x)*W y*X*star Y=((N.val:ℂ)^4)⁻¹*K:=sapling s x y o i a; change _ * (star (W x)*(W y*(X*T*star Y)))=(R:ℂ)^3/_*(K*T); rw [div_eq_mul_inv]; linear_combination (R:ℂ)^3 * T * hz
end YM.CF.Emu
