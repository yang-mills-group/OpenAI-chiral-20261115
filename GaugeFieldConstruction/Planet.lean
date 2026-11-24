import GaugeFieldConstruction.Oriental

/-!
# Orbit is the proper orthogonal subgroup. Use project A13 for full O(4).
  Don't infer passive commutation just by having sections into arbitrary Lie
  subalgebra. Need exact connected subgroup.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Matrix Function Set Filter
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology ContDiff
open Ortho (oneParameter)
open YM.Work.A13 (plane_givens)

def conjS (s : Ortho) (u : Rotors): Rotors:=⟨s.val*u.val*star s.val,by
  change star (s.val*u.val*star s.val)= -_
  simp only [star_mul,star_star,show star u.val= -u.val from u.property, neg_mul, ← mul_assoc,mul_neg]⟩
lemma conjugates (s : Ortho) (u : Rotors) (t : ℝ): s * oneParameter u t * s⁻¹ = oneParameter (conjS s u) t := by
  apply Subtype.ext
  change s.val * NormedSpace.exp (t • u.val) * star s.val = NormedSpace.exp (t • (s.val * u.val * star s.val))
  haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  let W : M4ˣ := ⟨s.val,star s.val,s.property.2,s.property.1⟩
  rw [show t • (s.val*u.val*star s.val)=s.val*(t • u.val)*star s.val by simp]
  exact (NormedSpace.exp_units_conj W _).symm
lemma controls (g : Ortho) (x) (p : x∈orbit): g*x*g⁻¹∈orbit := by
  apply Subgroup.closure_induction (p:=fun x _=>g*x*g⁻¹∈orbit) _ _ _ _ p
  · rintro _ ⟨b,t,rfl⟩; rw [conjugates]; exact paid _ _
  · simp
  · intro x y _ _ p q; rw [show g*(x*y)*g⁻¹=(g*x*g⁻¹)*(g*y*g⁻¹) by group]; apply orbit.mul_mem p q
  intro x _ p; rw [show g*x⁻¹*g⁻¹=(g*x*g⁻¹)⁻¹ by group]; apply orbit.inv_mem p
lemma units (u : Rotors) (x : ℝ): (oneParameter u x).val.det=1 := by
  let p:= oneParameter u (x/2)
  rw [show x=x/2+x/2 by ring,parameter_add]
  have h := congr_arg Matrix.det (Ortho.transp p); rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  change (p.val*p.val).det=_; rw [det_mul]; exact h
lemma detained {p : Ortho} (h:p∈ orbit): p.val.det=1 := by
  apply Subgroup.closure_induction (p:=fun p _=>p.val.det=1) _ _ _ _ h
  · rintro _ ⟨a,b,rfl⟩; exact units ..
  · simp
  · intro x y _ _ a b; change (x.val*y.val).det=_; rw [det_mul,a,b,one_mul]
  intro x _ h; change Matrix.det (star x.val)=1; rw [Matrix.star_eq_conjTranspose, det_conjTranspose,h]; rfl

abbrev Jj (i : Axis) := Signed.reflect i
abbrev Jp := Jj timeAxis
private theorem square (i) : Jj i * Jj i=1 := Ortho.ext _ _ fun x=> by
  rw [Ortho.move_mul]; ext j
  rw [Signed.mirrored,Ortho.move_one]; split_ifs <;> simp_all [Jj]
private lemma turning {i j : Axis} (p : i ≠ j) (x : E4) : Ortho.move (Signed.ortho (unsigned (Equiv.swap i j))) x i=x j := by rw [Signed.ortho_move]; simp [Signed.act,unsigned]
private lemma quarter (i j : Axis) (p:i≠j) : (unsigned (Equiv.swap i j)).ortho* Jj i = oneParameter (Ortho.plane i j) (Real.pi/2) := by
  apply Ortho.ext
  intro x; apply PiLp.ext; intro v
  obtain ⟨z,g,h⟩:= plane_givens p x (Real.pi/2)
  rw [Ortho.move_mul]
  by_cases hv:v=i
  · subst v; rw [z,turning p (Ortho.move (Jj i) x)]; simp [Jj,p,Ne.symm p]
  by_cases t:v=j
  · subst v; rw [Equiv.swap_comm,g,turning (Ne.symm p)]; simp [Jj]
  rw [h v hv t,Signed.ortho_move]; simp [Signed.act,unsigned,Equiv.swap_apply_of_ne_of_ne hv t,Jj,hv]
private lemma twice (i j : Axis) : Jj i * Jj j∈orbit := by
  by_cases p:i=j
  · rw [p, square]; simp
  have h : Jj i * Jj j=oneParameter (Ortho.plane i j) Real.pi := by
    apply Ortho.ext; intro x; ext v
    rw [Ortho.move_mul]; obtain ⟨g,h,s⟩:=plane_givens p x Real.pi
    by_cases r:v=i
    · subst v; simp [g,Jj,p]
    by_cases t:v=j
    · subst v; simp [h,Jj,p,Ne.symm p]
    rw [s v r t]; simp [Jj,r,t]
  rw [h]; exact paid _ _

private def Wing (s : Ortho) := s∈orbit ∨ s*Jp∈orbit
private lemma fly {s t} (p:Wing s) (q:Wing t): Wing (s*t) := by
  have h:= square timeAxis
  rcases p with p|p <;> rcases q with q|q
  · exact Or.inl (orbit.mul_mem p q)
  · apply Or.inr; rw [mul_assoc]; exact orbit.mul_mem p q
  · apply Or.inr
    have ht:= orbit.mul_mem p (controls Jp t q)
    rw [show s * Jp * (Jp*t*Jp⁻¹)=(s*t)*Jp by rw [show Jp⁻¹=Jp from inv_eq_of_mul_eq_one_right h]; simp only [mul_assoc]; rw [← mul_assoc Jp Jp,h]; simp [mul_assoc]] at ht; exact ht
  apply Or.inl
  have ht:= orbit.mul_mem p (controls Jp (t*Jp) q)
  rw [show s*Jp * (Jp*(t*Jp)*Jp⁻¹)=s*t by rw [show Jp⁻¹=Jp from inv_eq_of_mul_eq_one_right h]; simp only [mul_assoc]; rw [h,← mul_assoc Jp Jp,h]; simp] at ht; exact ht
private lemma way (s : Signed): Wing s.ortho:= by
  apply signed_induction (P:=fun g=>Wing g.ortho) _ _ _ s
  · intro p; induction p using Equiv.Perm.swap_induction_on with
    | one => rw [unsigned_one]; left; rw [show Signed.ortho 1=1 from Signed.inclusionO.map_one]; simp
    | swap_mul g i j p h=>
      rw [unsigned_mul, show Signed.ortho (_*_)=_ from Signed.inclusionO.map_mul _ _]
      apply fly _ h; apply Or.inr
      have ht : (unsigned (Equiv.swap i j)).ortho*Jj i ∈orbit := by rw [quarter i j p]; exact paid _ _
      have hu := orbit.mul_mem ht (twice i timeAxis); simp only [mul_assoc] at hu; rw [← mul_assoc (Jj i) (Jj i),square,one_mul] at hu; exact hu
  · intro i; exact Or.inr (twice i timeAxis)
  intro x y u v; rw [show (x*y).ortho=_ from Signed.inclusionO.map_mul _ _]; apply fly u v
lemma covers_all (s : Ortho) : s∈orbit ↔ s.val.det=1 := by
  refine ⟨detained,fun h=>?_⟩
  have he : s∈ YM.Bid.AxisGens := by rw [YM.Work.A13.answer]; trivial -- unfolds?
  suffices p:Wing s by
    cases p with
    | inl p=> exact p
    | inr p=> have H:=detained p; change (s.val*Jp.val).det=_ at H
              rw [det_mul,h,one_mul, show Jp.val.det= -1 by dsimp only [Jp,Jj,Signed.reflect]; rw [parity (Signed.mirror timeAxis)]; simp] at H; norm_num at H
  apply Subgroup.closure_induction (p:=fun x _=>Wing x) _ _ _ _ he
  · rintro r (⟨b,h⟩ | ⟨b,t,h⟩) <;> subst r
    · exact way b
    exact Or.inl (paid _ _)
  · exact Or.inl (Subgroup.one_mem _)
  · exact fun _ _ _ _ p q=> fly p q
  intro x v H; cases H with
  | inl H=> exact Or.inl (orbit.inv_mem H)
  | inr H=>
    have h:= controls Jp (x*Jp)⁻¹ (orbit.inv_mem H)
    rw [show Jp*(x*Jp)⁻¹*Jp⁻¹=x⁻¹*Jp by simp only [_root_.mul_inv_rev]; rw [← mul_assoc, mul_inv_cancel,one_mul, show Jp⁻¹=Jp from inv_eq_of_mul_eq_one_right (square timeAxis)]] at h
    exact Or.inr h
end YM.GaugeFieldConstruction.Stage
