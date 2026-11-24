import GaugeFieldConstruction.MatterOrbit

/-! Supplier of (93) number of copies: Color to mixed Lie label.
  Step 2, move to complex algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Matter
open CF Function Set Matrix Finset
open scoped Topology Matrix Matrix.Norms.Frobenius Kronecker BigOperators
variable (x : C)

lemma hues (x y : C) (t : ℝ) : core (x+y)=core x+core y ∧
    core (t • x)=(t:ℂ) • core x := by
  constructor
  · apply Subtype.ext; exact H.map_add ..
  apply Subtype.ext; change H (t • x)= (t:ℂ) • H x; rw [map_smul, Complex.coe_smul]

def proj (x : sl) : V := (2:ℂ)⁻¹ • (x.val-star x.val)
lemma proj_ok (x : sl) : proj x ∈ G.lie := by
  apply CF.Thera.league.mpr
  change star (proj x) = -(proj x) ∧ trace (proj x)=0
  constructor
  · simp [proj,star_sub, Matrix.star_eq_conjTranspose, sub_smul]; module
  simp [proj, Matrix.star_eq_conjTranspose, (show Matrix.trace x.val=0 from x.property)]

def rho (x : sl) : C := G.projectColor (proj x)
lemma origin (x : sl) : H (rho x)=proj x :=
  show _ from G.colorMat_project_self (proj_ok x)
lemma burst (x : sl) : x=core (rho x) + Complex.I • core (rho (-Complex.I • x)) := by
  apply Subtype.ext
  change x.val=H _+ Complex.I • H _
  rw [origin,origin]; ext a b; simp [proj,Matrix.star_eq_conjTranspose]; ring_nf; simp; ring

theorem detects {f g : sl→ₗ[ℂ]U} (h : ∀ i, f (core i)=g (core i)) : f=g := by
  ext1 x; rw [burst x, map_add,map_add,map_smul,map_smul,h,h]

def painted (X : C →ₗ[ℝ] U) (x : sl) := X (rho x) + Complex.I • X (rho (-Complex.I • x))
private lemma add_rho (a b : sl) : rho (a+b)=rho a+rho b := by
  unfold rho; rw [← map_add]
  congr 1
  change proj _ = _; unfold proj; simp only [Submodule.coe_add,star_add,smul_add, smul_sub]; abel
private lemma lean_rho (x : sl) (a : ℝ) : rho ((a:ℂ) • x)=a • rho x := by
  unfold rho; rw [← map_smul]; congr 1
  change proj _ = a • proj x; rw [← Complex.coe_smul]
  ext i j; simp [proj,Matrix.star_eq_conjTranspose]; ring
lemma mix (X : C →ₗ[ℝ] U) (x y : sl) : painted X (x+y)=painted X x+painted X y := by
  unfold painted; rw [smul_add, add_rho, add_rho,map_add,map_add,smul_add]; abel
lemma trace_r (X : C →ₗ[ℝ] U) (x : sl) (a : ℝ) : painted X ((a:ℂ) • x)= (a:ℂ) • painted X x := by
  have h (x) : (a:ℂ) • x= a • (x:U) := by rw [Complex.coe_smul]
  unfold painted; rw [lean_rho, smul_comm (-Complex.I) (a:ℂ),lean_rho,map_smul,map_smul, ← h,← h]
  rw [smul_add,smul_comm Complex.I]

private lemma negColor (b : sl) : rho (-b)= -rho b := by
  have h := lean_rho b (-1)
  rw [show -b=(-1:ℂ) • b from (neg_one_smul ℂ b).symm]; simpa only [Complex.ofReal_neg, Complex.ofReal_one,neg_one_smul] using h
private lemma minusI (x : sl) : -Complex.I • (Complex.I • x)=x := by rw [smul_smul]; simp
lemma chilly (X : C→ₗ[ℝ]U) (x : sl) : painted X (Complex.I • x)= Complex.I • painted X x := by
  unfold painted; rw [minusI, smul_add,smul_smul, Complex.I_mul_I,neg_one_smul,show (-Complex.I) • x= -(Complex.I • x) from neg_smul Complex.I x,negColor,map_neg]
  abel

def extend (X : C→ₗ[ℝ] U) : sl →ₗ[ℂ] U where
  toFun := painted X; map_add' := mix X
  map_smul' c x:=by
    have he := Complex.re_add_im c; conv_lhs => rw [← he,add_smul,mix]
    change _ = c • _; conv_rhs=> rw [←he,add_smul]
    rw [mul_smul, trace_r,trace_r,chilly,mul_smul]

private lemma at_core (x : C) : rho (core x)=x := by
  apply G.colorMat_injective
  change H _=H x; rw [origin]; unfold proj; dsimp only [core]; rw [show star (H x)= -(H x) from G.colorMat_skew x]; module
private lemma at_hole (x : C) : rho (-Complex.I • core x)=0 := by
  apply G.colorMat_injective; change H _=H 0
  rw [map_zero,origin]; unfold proj
  simp only [Submodule.coe_smul,core,star_smul,show star (H x)= -(H x) from G.colorMat_skew x]
  simp
@[simp] lemma base (X : C→ₗ[ℝ] U) (x : C) : extend X (core x)=X x := by
  change painted X (core x)=_; unfold painted; rw [at_core,at_hole,map_zero]; simp

lemma rep_add (x y : V) : repX (x+y)=repX x+repX y := by
  ext i j; cases i <;> cases j <;> simp [repX,Join.both, gen_entry] <;> ring
lemma rep_s (u : ℂ) (x : V) : repX (u • x)=u • repX x := by
  ext i j; cases i <;> cases j <;> simp [repX,Join.both, gen_entry] <;> ring

def lie (a b : sl) : sl := ⟨a.val*b.val-b.val*a.val, by rw [payable,trace_sub,trace_mul_comm]; simp⟩
lemma lie_add (a b c) : lie (a+b) c=lie a c+lie b c ∧ lie c (a+b)=lie c a+ lie c b := by
  constructor <;> apply Subtype.ext <;> simp [lie,mul_add,add_mul] <;> abel
lemma lie_s (a b) (u : ℂ) : lie (u • a) b=u • lie a b ∧ lie b (u • a)=u • lie b a := by
  constructor <;> apply Subtype.ext <;> simp [lie, Matrix.smul_mul,Matrix.mul_smul,smul_sub]
lemma flashed (a b : C) : lie (core a) (core b)=core (G.ad a b) := Subtype.ext (G.colorMat_ad ..).symm

def Wcov (X : sl→ₗ[ℂ] U) : Prop := ∀ a b,X (lie a b)=repX a.val*X b-X b*repX a.val
lemma earned (X : C →ₗ[ℝ] U) (p : action X) : Wcov (extend X) := by
  let Y := extend X
  have ht (a b:C) : Y (lie (core a) (core b))=repX (H a)*Y (core b)-Y (core b)*repX (H a) := by
    unfold Y; rw [flashed,base,base]; exact point X p a b
  have he (a:C) (b:sl) : Y (lie (core a) b)=repX (H a)*Y b-Y b*repX (H a) := by
    rw [burst b,(lie_add ..).2,(lie_s ..).2]; simp only [map_add,map_smul,mul_add,add_mul,ht,Matrix.smul_mul,Matrix.mul_smul,smul_sub]; abel
  intro a b; rw [burst a,(lie_add ..).1,(lie_s ..).1]
  change Y _= _*Y _-Y _*_
  simp only [map_add,map_smul,he]
  simp only [Submodule.coe_smul,Submodule.coe_add, core,rep_add,rep_s,mul_add,
    add_mul, Matrix.smul_mul,Matrix.mul_smul,smul_sub]; abel
lemma earned_pure (v : U) (p : pure v) (b : sl) : v*repX b.val=repX b.val*v := by
  rw [burst b]
  simp only [Submodule.coe_smul,Submodule.coe_add,rep_s,rep_add,mul_add,add_mul,Matrix.smul_mul,Matrix.mul_smul,core]
  simp only [(centers v p _).symm]
end YM.GaugeFieldConstruction.Matter
