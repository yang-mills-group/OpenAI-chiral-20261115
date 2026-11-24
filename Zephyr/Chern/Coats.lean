import Zephyr.Chern.Cliff
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.CF Silk


abbrev Coats (I : Type*) := Matrix I I Silk

variable {ι : Type*}

-- Note Δ is by components. No choice of norm on ι.
def Δ (a : Axis) : Coats ι →ₗ[ℂ] Coats ι :=
  (D a).toLinearMap.mapMatrix

lemma Δ_apply (a) (x:Coats ι) (u v) : Δ a x u v=D a (x u v) := rfl

lemma Δ_symm (a b) (x:Coats ι) : Δ a (Δ b x)=Δ b (Δ a x) :=
  Matrix.ext (fun _ _=> D_symm ..)

/-- Laurent-coefficient matrix. -/
def seam (x : Cover) : Coats ι →ₗ[ℂ] Op ι :=
  (coeff x).mapMatrix

lemma seam_apply (x : Cover) (p:Coats ι) u v : seam x p u v=(p u v).co x := rfl

lemma seam_ext {p q:Coats ι} (h : ∀ x,seam x p=seam x q) : p=q :=
  Matrix.ext fun u v=>Silk.ext <| funext fun x=> congrFun (congrFun (h x) u) v

lemma seam_Δ (x:Cover) (a:Axis) (p:Coats ι) :
    seam x (Δ a p) = rune a x • seam x p := rfl

variable [Fintype ι]

def gross : Coats ι →ₗ[ℂ] ℂ := τ.comp (Matrix.traceLinearMap ..)

lemma gross_def (x:Coats ι) : gross x=τ x.trace := rfl

lemma gross_rot (x y:Coats ι) : gross (x*y)=gross (y*x) :=
  congrArg τ (Matrix.trace_mul_comm ..)

lemma gross_co (x:Coats ι) : gross x=(seam 0 x).trace := by
  rw [gross_def]
  change τ (∑ i,x i i) = _
  rw [map_sum];rfl

lemma Δ_gross (a:Axis) (x:Coats ι) : gross (Δ a x)=0 := by
  rw [gross_co,seam_Δ, Matrix.trace_smul]
  simp [rune]

lemma Δ_mul (a:Axis) (x y:Coats ι) : Δ a (x*y)=Δ a x*y+x*Δ a y := by
  ext i j
  simp only [Δ_apply,Matrix.mul_apply,map_sum,D_mul, Finset.sum_add_distrib]
  rw [add_comm, Matrix.add_apply];simp only [Matrix.mul_apply, Δ_apply]

lemma ibp (x y:Coats ι) (a:Axis) : gross (x*Δ a y)= -gross (Δ a x*y) := by
  exact add_eq_zero_iff_eq_neg.mp (by rw [add_comm, ← map_add, ←Δ_mul, Δ_gross])

lemma pack_entries (p q:Coats ι) (x:Cover) (i j:ι) :
    Summable (fun y=> (seam y p*seam (x-y) q) i j) := by
  simp only [Matrix.mul_apply]
  exact summable_sum (fun k _=> (p i k).fast.pack (q k j).fast x)

lemma seam_entries (p q:Coats ι) (x:Cover) (i j:ι) :
    seam x (p*q) i j = ∑' y,(seam y p*seam (x-y) q) i j := by
  change coeff x (∑ k,p i k*q k j)=_

  simp only [Matrix.mul_apply,map_sum,coeff_apply,co_mul,seam_apply]
  exact (Summable.tsum_finsetSum (fun k _=> (p i k).fast.pack (q k j).fast x)).symm

variable [DecidableEq ι]

lemma Δ_one (a:Axis) : Δ a (1:Coats ι)=0 := by
  have h:=Δ_mul a (1:Coats ι) 1
  rw [mul_one,mul_one,one_mul] at h
  simpa only [left_eq_add] using h

/-- as constant symbol -/
def spun : Op ι →ₐ[ℂ] Coats ι :=
  (Algebra.ofId ℂ Silk).mapMatrix

/-- evaluation on the torus -/
def flash (t:Brill) : Coats ι →ₐ[ℂ] Op ι :=
  (E t).mapMatrix

lemma flash_ext {x y:Coats ι} (p:∀ t,flash t x=flash t y) : x=y :=
  Matrix.ext fun _ _ => E_ext <| fun t=>congrFun (congrFun (p t) _) _

@[simp] lemma flash_spun (t) (x:Op ι) : flash t (spun x)=x :=
  Matrix.ext fun _ _=> (E t).commutes _

@[simp] lemma Δ_spun (a:Axis) (x:Op ι) : Δ a (spun x)=0 :=
  Matrix.ext fun _ _=> (D a).map_algebraMap _
