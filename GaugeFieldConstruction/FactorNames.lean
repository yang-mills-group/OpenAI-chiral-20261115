import GaugeFieldConstruction.Counts
import GaugeFieldConstruction.Labels

/-!
# Full generation weight matrices. Handle improper Signed (charge bit).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Matter
open Function Matrix CF
open scoped Matrix BigOperators
variable {p q : FlavorIndex → ℂ}

/-- charge-only conjugation on real Color -/
def cc_color (x : C) := G.projectColor (cc (H x))
lemma cc_ink (x : C) : H (cc_color x)=cc (H x) := by
  refine Gauge.colorMat_project_self G ?_
  have h := G.colorMat_mem x
  apply CF.Thera.league.mpr
  obtain ⟨a,b⟩:= CF.Thera.league.mp h
  change star (H x) = -(H x) at a
  change Matrix.trace (H x)=0 at b
  change star (cc (H x))= -(cc (H x)) ∧ Matrix.trace (cc (H x))=0
  simp [cc,a,b,star_neg] -- loop
  rw [show star (H x)ᵀ=(star (H x))ᵀ from rfl,a]; simp

lemma two_real (a b:ℂ) : cc (two a b)=two (star a) (star b) := by
  ext i j; cases i <;> cases j <;> simp [two,Join.both,Matrix.one_apply]
  all_goals split_ifs <;> simp_all
lemma two_transp (a b:ℂ) : (two a b).transpose=two a b := by
  ext i j; cases i <;> cases j <;> simp [two,Join.both, Matrix.one_apply,eq_comm]
lemma rep_cc (a : V) : repX (cc a)=cc (repX a) := by
  ext i j; cases i <;> cases j <;>
    simp [repX,Join.both,gen_entry,star_sub, Matrix.one_apply]
  split_ifs <;> simp_all [add_comm]
lemma rep_star (a : V) : repX (star a)=star (repX a) := by
  ext i j; cases i <;> cases j <;>
    simp [repX,Join.both,gen_entry,star_sub,Matrix.one_apply,eq_comm,mul_comm]
  split_ifs <;> simp_all [add_comm]
lemma rep_inv (x : C) : star (repX (H x)) = -(repX (H x)) := by
  rw [← rep_star, show star (H x)= -(H x) from G.colorMat_skew x,
    show -(H x)=(-1:ℂ) • H x from by simp, rep_s]; simp

def flip (p : FlavorIndex → ℂ) (i : FlavorIndex) := p (i.1,i.2.2,i.2.1)
lemma bra_star (W : Op Slot) (x y : Generation) : bra x y (cc W)=cc (bra x y W) := rfl
lemma bra_swap (W : Op Slot) (x y) : bra x y W.transpose=(bra y x W).transpose := rfl
lemma two_comm (a b : ℂ) (x : C) : two a b * repX (H x) = repX (H x) * two a b :=
  (centers _ ((pure_singular _).mpr ⟨_,_,rfl⟩) _).symm

theorem neutral_transpose (p : FlavorIndex → ℂ) : (coeffs p).transpose=coeffs (flip p) := by
  apply block_ext; intro x y; rw [bra_swap,pint,two_transp,pint]; rfl
theorem cost_transpose (p : FlavorIndex → ℂ) (x : C) : (costing p (cc_color x)).transpose= -costing (flip p) x := by
  apply block_ext; intro a b; rw [bra_swap,pint_c, map_neg,pint_c]
  change (two _ _*repX (H _)).transpose= -(two _ _*repX (H _))
  rw [cc_ink,rep_cc,Matrix.transpose_mul,two_transp,cc, transpose_transpose,rep_inv,
    neg_mul, two_comm]; rfl

theorem conjugate_neut (p) : cc (coeffs p)=coeffs (star ∘ p) := by
  apply block_ext; intro x y; rw [bra_star,pint,pint,two_real]; rfl
theorem conjugate_tint (p : FlavorIndex → ℂ) (x) : cc (costing p (cc_color x)) = costing (star ∘ p) x := by
  apply block_ext; intro a b
  rw [bra_star,pint_c,pint_c]; change cc (two _ _*repX (H _))=two _ _*repX (H _)
  rw [cc_mul,cc_ink,rep_cc,two_real]; simp only [Function.comp_apply, CF.cc_cc] -- tune

-- Linearity in generation weighting
lemma two_l (a b c d : ℂ) : two (a+b) (c+d)=two a c+two b d := by
  ext i j; cases i <;> cases j <;> simp [two,Join.both,add_mul]
lemma two_s (a b c : ℂ) : two (a • b) (a • c) = a • two b c := by
  ext i j; cases i <;> cases j <;> simp [two,Join.both,mul_assoc]

def jordan : (FlavorIndex → ℂ) →ₗ[ℂ] Op Slot where
  toFun:=coeffs
  map_add' a b:= block_ext fun i j=> by rw [map_add,pint,pint,pint]; exact two_l ..
  map_smul' a b := block_ext fun i j => by rw [map_smul,pint,pint]; exact two_s ..
def forge : (FlavorIndex → ℂ) →ₗ[ℂ] C→ₗ[ℝ]Op Slot where
  toFun:=costing
  map_add' a b:=LinearMap.ext fun x=>block_ext fun i j=> by
    rw [LinearMap.add_apply,map_add,pint_c,pint_c,pint_c]; change two (_ + _) (_ + _) * repX _ = _
    rw [two_l,add_mul]; rfl
  map_smul' a b:=LinearMap.ext fun x=>block_ext fun i j=>by
    change _ = bra i j (a • (costing b x)); rw [map_smul,pint_c,pint_c]; change two (a • _) (a • _)*repX _ = _
    rw [two_s,smul_mul_assoc]; rfl
end YM.GaugeFieldConstruction.Matter
