import YM.CF.Scree.Brief

/-! Uniform polynomial growth in the *footprint block* b. -/
noncomputable section
namespace YM.CF.Zephyr

def Poly (f:ℕ→ℝ):Prop := ∃ C:ℝ, 0<C ∧ ∃ k:ℕ,∀ b, |f b| ≤ C*(b+1:ℝ)^k
theorem pol (c:ℝ):Poly (fun _ => c):=
 ⟨|c|+1, by positivity,0,fun b=>by rw [pow_zero,mul_one]; exact le_add_of_nonneg_right zero_le_one⟩

theorem blockPol : Poly (fun b=>↑b):=
 ⟨1,zero_lt_one,1,fun b=>by rw [pow_one,one_mul,abs_of_nonneg (Nat.cast_nonneg _)]; linarith⟩

variable {f g:ℕ→ℝ}
theorem Poly.add (u:Poly f)(v:Poly g): Poly (fun b=> f b+g b):=by
 obtain ⟨C,x,k,h⟩:=u
 obtain ⟨D,y,l,p⟩:=v
 refine ⟨C+D,add_pos x y,max k l,fun b=>(abs_add_le ..).trans ((add_le_add (h b) (p b)).trans ?_)⟩
 rw [add_mul]
 have z: (1:ℝ) ≤ b+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
 exact add_le_add
   (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ z (le_max_left ..)) x.le)
   (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ z (le_max_right ..)) y.le)

theorem Poly.mul (u:Poly f)(v:Poly g): Poly (fun b=> f b*g b):=by
 obtain ⟨C,x,k,h⟩:=u
 obtain ⟨D,y,l,p⟩:=v
 refine ⟨C*D,mul_pos x y,k+l,fun b=>?_⟩
 rw [abs_mul]
 refine (mul_le_mul (h b) (p b) (abs_nonneg _) (by positivity)).trans_eq ?_
 rw [pow_add]
 ring

theorem Poly.pow (u:Poly f)(k:ℕ): Poly (fun b=> (f b)^k):=by
 induction k with
 | zero => simpa only [pow_zero] using pol 1
 | succ k ih => simpa only [pow_succ] using ih.mul u

theorem Poly.maj (u:Poly f): ∃ C:ℝ, 0<C ∧ ∃ k:ℕ,∀ b, f b ≤ C*(b+1:ℝ)^k:=by
 obtain ⟨C,x,k,h⟩:=u; exact ⟨C,x,k,fun b=> (le_abs_self _).trans (h b)⟩

-- An optional shorthand for ground goals.
macro "zipcost" : tactic =>
 `(tactic| repeat' first | exact pol _ | exact blockPol | apply Poly.pow | apply Poly.add | apply Poly.mul)

example (c:ℝ)(k:ℕ) : Poly (fun b=> ((c+1)+2*(b+3:ℝ)^k)*c):=by zipcost

end YM.CF.Zephyr
