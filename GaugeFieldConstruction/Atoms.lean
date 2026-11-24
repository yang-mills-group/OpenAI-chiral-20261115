import GaugeFieldConstruction.Planet

/-!
# Rotation of the argument of an active receipt
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Cauchy Row Phys Function Set Filter Matrix
open scoped Matrix Matrix.Norms.Frobenius Kronecker BigOperators Topology ContDiff
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

abbrev R4 (α : Type*) := Matrix α α ℝ
/- Keep both continuous (integrated) and infinitesimal active movements. -/
structure Cell (α : Type*) [Fintype α] [DecidableEq α] where
  active: Ortho →* R4 α
  pin : Rotors →ₗ[ℝ] R4 α
  cont (i j) : Continuous (fun A=>active A i j)
  o (u : Ortho): (active u).transpose = active u⁻¹
  skew (u : Rotors) : (pin u).transpose= -pin u
  live (u : Rotors) (i j):HasDerivAt (fun t=> active (Ortho.oneParameter u t) i j) (pin u i j) 0
  bracket (u v : Rotors): pin (tick u v)=pin u*pin v-pin v*pin u

namespace Cell

def Still (α : Type*) [Fintype α] [DecidableEq α] : Cell α where
  active:=1; pin:=0
  cont i j:= continuous_const
  o u:= by simp
  skew u:= by simp
  live u i j:= hasDerivAt_const _ _
  bracket u v:= by simp

def UnitV : Cell Axis where
  active:={toFun:=Subtype.val, map_mul':=fun _ _=> rfl, map_one':=rfl}; pin:= Ortho.skewSpace.subtype
  cont i j:= continuous_subtype_val.matrix_elem i j -- Frobenius scope??
  o u:= rfl
  skew u:= u.property
  live:=northR; bracket u v:=rfl

variable (P : Cell α) (Q : Cell β)
private def ducks : Rotors →ₗ[ℝ] R4 (α×β) where
  toFun A:= (P.pin A ⊗ₖ (1:R4 β)) + ((1:R4 α) ⊗ₖ Q.pin A)
  map_add' x y:=by ext a b; simp [add_mul,mul_add]; ring
  map_smul' z a:= by ext i j; simp; ring
private lemma drift (u x : R4 α) (v y:R4 β):
    (u⊗ₖ (1:R4 β)+(1:R4 α) ⊗ₖ v)*(x⊗ₖ (1:R4 β)+(1:R4 α) ⊗ₖ y)= (u*x) ⊗ₖ (1:R4 β)+(1:R4 α) ⊗ₖ (v*y)+u ⊗ₖ y+x ⊗ₖ v:= by
  rw [add_mul,mul_add,mul_add]; simp_rw [← Matrix.mul_kronecker_mul]; simp; abel

def wings : Cell (α×β) where
  active:={toFun u:=P.active u ⊗ₖ Q.active u, map_mul':=fun x y=>by rw [map_mul,map_mul,mul_kronecker_mul], map_one':=by simp}
  pin:=ducks P Q
  cont i j:= (P.cont i.1 j.1).mul (Q.cont i.2 j.2)
  o u:= by ext i j; simp [← P.o u,← Q.o u, transpose_apply]
  skew u:= by
    ext i j; change (ducks _ _ u).transpose i j=(-(ducks _ _ u)) i j; simp only [ducks,LinearMap.coe_mk, AddHom.coe_mk,transpose_add,Matrix.add_apply];
    change P.pin u j.1 i.1 * (1:R4 β) j.2 i.2+ (1:R4 α) j.1 i.1* Q.pin u j.2 i.2 = -(((P.pin u)⊗ₖ (1:R4 β)+(1:R4 α)⊗ₖ (Q.pin u)) i j)
    rw [← Matrix.transpose_apply (P.pin u),← Matrix.transpose_apply (Q.pin u),P.skew,Q.skew]; simp only [Matrix.kronecker_apply,Matrix.neg_apply,Matrix.add_apply]
    simp [Matrix.one_apply,eq_comm]; split_ifs <;> simp_all <;> ring -- adjust
  live u i j:= by
    refine ((P.live u i.1 j.1).mul (Q.live u i.2 j.2)).congr_deriv ?_
    rw [YM.Work.A13.oneParameter_zero,map_one,map_one]; rfl
  bracket u v:=by
    dsimp only [MonoidHom.coe_mk,OneHom.coe_mk,ducks, LinearMap.coe_mk, AddHom.coe_mk]; rw [P.bracket,Q.bracket,drift,drift]
    ext i j; simp [sub_mul, mul_sub]; ring

private def ds : Rotors→ₗ[ℝ] R4 (α ⊕ β) where
  toFun u:=Matrix.fromBlocks (P.pin u) 0 0 (Q.pin u)
  map_add' s t:=by ext (i|i) (j|j) <;> simp
  map_smul' s a:=by ext (i|i) (j|j) <;> simp

def sum : Cell (α⊕β) where
  active:= {
    toFun u:= Matrix.fromBlocks (P.active u) 0 0 (Q.active u)
    map_one':=by simp
    map_mul' u v:= by simp [Matrix.fromBlocks_multiply] }
  pin:=ds P Q
  cont i j:= by cases i <;> cases j <;> first|exact P.cont _ _|exact Q.cont _ _| exact continuous_const
  o u:= by change Matrix.transpose (Matrix.fromBlocks _ _ _ _) = Matrix.fromBlocks _ _ _ _; rw [Matrix.fromBlocks_transpose, P.o,Q.o]; rfl
  skew u:= by change Matrix.transpose (Matrix.fromBlocks _ _ _ _)= -(Matrix.fromBlocks _ _ _ _); rw [Matrix.fromBlocks_transpose, P.skew,Q.skew]; ext (i|i) (j|j) <;> simp
  live u i j:= by cases i <;> cases j <;> first|exact P.live u _ _| exact Q.live u _ _| exact hasDerivAt_const _ _
  bracket u v:= by simp [ds,P.bracket,Q.bracket, Matrix.fromBlocks_multiply]; ext (i|i) (j|j) <;> simp

/-- cost arrays of prescriptions (not component lowering). -/
def bill (B : R4 α) : Module.End ℂ (J α) := jet fun a=> ∑ i:α, ((B i a:ℝ):ℂ) • ket i

lemma entry (B:R4 α) (a b): bill B (ket a) b = ↑(B b a) := by rw [bill,on_ket]; simp [Finsupp.finsetSum_apply,ket,Finsupp.single_apply]
lemma bills1 (b : J α) : bill 1 b=b := by
  have h :bill (1:R4 α)=LinearMap.id:= ket_ext (fun i=>by ext1 j; rw [entry]; simp [ket,Matrix.one_apply,eq_comm, Finsupp.single_apply]; split_ifs <;> simp)
  rw [h]; rfl
lemma success (A B : R4 α): bill A*bill B=bill (A*B) := by
  apply ket_ext; intro x; rw [Module.End.mul_apply]
  ext1 i; nth_rw 2 [bill]; rw [on_ket,map_sum]; simp only [map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply, entry, smul_eq_mul]; rw [Matrix.mul_apply]; push_cast; exact Finset.sum_congr rfl fun _ _=>mul_comm ..
lemma cran (X:R4 α) (Y:R4 β) (a: J α) (b): bill (X ⊗ₖ Y) (times' a b)=times' (bill X a) (bill Y b) := by
  have e : bill (X ⊗ₖ Y)=Phys.strap (bill X) (bill Y) := crossing fun i j=>by
    rw [straps,takes]
    ext1 ⟨x,y⟩
    have ht (a : J α) (b : J β) : times' a b (x,y)=a x*b y := by
      let L:=Finsupp.lapply (R:=ℂ) (M:=ℂ) x; let R:= Finsupp.lapply (R:=ℂ) (M:=ℂ) y
      have H : Finsupp.lapply (x,y)=productRead L R := ket_ext (fun ⟨i,j⟩=>by rw [productRead,on_ket]; unfold L R; by_cases h:x=i <;> by_cases p:y=j <;> simp [ket,h,p,Finsupp.single_apply,eq_comm])
      change Finsupp.lapply (R:=ℂ) _ _=_; rw [H,read_times]; rfl
    rw [entry,ht,entry,entry]; change ((X x i * Y y j:ℝ):ℂ)=_; push_cast; rfl
  rw [e,straps]
lemma cruise (A B : R4 α) : bill (A+B)=bill A+bill B := ket_ext fun i=>by simp only [LinearMap.add_apply,bill,on_ket,Matrix.add_apply]; push_cast; simp [add_smul,Finset.sum_add_distrib]
lemma jewel (t : ℝ) (B : R4 α) : bill (t • B)=(↑t:ℂ) • bill B := ket_ext fun i=>by simp only [LinearMap.smul_apply,bill,on_ket, Finset.smul_sum, Matrix.smul_apply,smul_eq_mul, smul_smul]; push_cast; rfl

def beta (u : Rotors) := bill (P.pin u)
lemma optionB (u : Rotors) : beta (wings P Q) u= splitD (beta P u) (beta Q u) := by
  apply crossing; intro i j; change bill (_+_) _=_; rw [cruise]; simp only [LinearMap.add_apply, cran,bills1,split_legs]; rfl
lemma betaV (u : Rotors) (x) : beta UnitV u (ket x)= ∑ i:Axis,(u.val i x:ℂ) • ket i := on_ket ..

def leftU : J α →ₗ[ℂ] J (α ⊕ β) := jet fun i=> ket (Sum.inl i)
def rightU : J β →ₗ[ℂ] J (α ⊕ β):= jet fun i=>ket (Sum.inr i)
lemma input1 (u : Rotors) i: beta (sum P Q) u (ket (Sum.inl i))= leftU (beta P u (ket i)) := by
  simp only [beta,bill,on_ket, Fintype.sum_sum_type,map_sum,map_smul,leftU]; simp [sum,ds]
lemma input2 (u : Rotors) i: beta (sum P Q) u (ket (Sum.inr i))=rightU (beta Q u (ket i)) := by
  simp only [beta,bill,on_ket,Fintype.sum_sum_type,map_sum,map_smul,rightU]; simp [sum,ds]
end Cell
end YM.GaugeFieldConstruction.Stage
