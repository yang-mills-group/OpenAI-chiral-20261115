import Zephyr.Chern.Jet
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.CF Matrix Silk


open scoped Kronecker
variable (I:Type*) [Fintype I] [DecidableEq I]

def shade (u:Streams) : Coats (SpinIdx×I) :=
  ∑ k,u k • spun (Cg k ⊗ₖ (1:Op I))

def snow (u:Streams) : Coats (SpinIdx×I) :=
  (2:ℂ)⁻¹ • (1+shade I u)

variable {I}

def icolor (z:Op I) := spun ((1:Op SpinIdx) ⊗ₖ z)

def slide (t:Brill) (u:Streams) : Quint := fun k=> E t (u k)

lemma flash_act {J:Type*} [Fintype J] [DecidableEq J] (t:Brill) (v:Silk) (x:Coats J) :
    flash t (v • x)= E t v • flash t x :=
  Matrix.ext fun _ _=>map_mul (E t) _ _

lemma shadeF (t) (u) :
    flash t (shade I u)= wand (slide t u) ⊗ₖ (1:Op I) := by
  simp only [shade,map_sum,flash_act,flash_spun,wand_eq]
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [Matrix.sum_apply,kronecker_apply,Matrix.smul_apply,smul_eq_mul,
    slide,Finset.sum_mul,mul_assoc]

lemma colorF (t) (z:Op I) : flash t (icolor z)= (1:Op SpinIdx) ⊗ₖ z :=
  flash_spun ..

lemma flash_trace (t) (p : Coats I) : E t p.trace = (flash t p).trace := by
  rw [trace,map_sum];rfl

def dropD (a:Axis) (u:Streams) : Streams := fun k=>Silk.D a (u k)
lemma frame_succ_eq (f:Streams) (a:Axis) : frameM f a.succ = dropD a f := frame_succ ..

variable (I)

lemma Δshade (a:Axis)(u:Streams) : Δ a (shade I u)= shade I (dropD a u) := by
  have h (k:Five):
      Δ a (u k • spun (Cg k ⊗ₖ (1:Op I)))=dropD a u k • spun (Cg k ⊗ₖ (1:Op I)) := by
    ext x y
    rw [Δ_apply, Matrix.smul_apply,smul_eq_mul,D_mul,← Δ_apply,Δ_spun,
      Matrix.zero_apply,mul_zero,zero_add];rfl
  simp only [shade,map_sum,h]

lemma Δsnow (a:Axis) (u:Streams) :
    Δ a (snow I u)= (2:ℂ)⁻¹ • shade I (dropD a u) := by
  rw [snow,map_smul,map_add,Δ_one,zero_add,Δshade]

lemma frozen (u:Streams) : mirror (snow I u)= -shade I u := by
  rw [mirror, snow, ← add_smul, show (2:ℂ)⁻¹+2⁻¹=1 by norm_num,one_smul];abel

variable {I}
lemma icolor_constant (a) (z:Op I) : Δ a (icolor z)=0 := Δ_spun ..

lemma Δ_mingle (z: Op I) (u:Streams) (a:Axis) :
    Δ a (snow I u)*icolor z=icolor z * Δ a (snow I u) := by
  rw [Δsnow,Matrix.mul_smul,Matrix.smul_mul]
  apply flash_ext
  intro
  simp only [map_smul,map_mul,colorF,shadeF, ←mul_kronecker_mul,
    one_mul,mul_one]

private lemma gross_three (z:Op I)(u v w:Streams) :
    gross (shade I u * ((icolor z * icolor z)*(shade I v * shade I w)))=0 := by
  rw [gross_def]
  refine Eq.trans ?_ (map_zero τ)
  apply congrArg
  apply E_ext;intro
  simp only [flash_trace,map_zero,map_mul,shadeF,colorF,←mul_kronecker_mul,trace_kronecker,mul_one,one_mul,
    ←mul_assoc,wand_trip,zero_mul]

lemma gross_curly (z:Op I) (u:Streams) :
    gross (mirror (snow I u) * ((icolor z * icolor z)*curly (snow I u)))=0 := by
  rw [frozen,curly]
  simp only [bow,crossB,Δsnow,map_smul,Δshade,mul_add,mul_sub,neg_mul,
    Matrix.mul_smul,Matrix.smul_mul,map_add,map_sub,map_neg,gross_three,
    smul_zero,sub_self,add_zero,neg_zero]
