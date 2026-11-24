import Zephyr.Chern.Shade
import Zephyr.Chern.Orbit
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.CF.Fir YM.CF YM.CF.Jill Silk YM.Laurent Filter


open scoped Real Kronecker

lemma paint (j:ℕ) (M : Male) (p:Bloch.Momentum) :
    bar j M.val p=(2:ℂ)⁻¹ • (1+wand (signal j M p)) := by
  have e : grading * zen (skin j M.val p)=∑ a:Axis, skin j M.val p a • Cg a.succ := by
    rw [zen,Matrix.mul_sum]
    simp only [Matrix.mul_smul]
    rfl
  rw [wand_eq,Fin.sum_univ_succ,signal_head,Cg_0,bar,e]
  simp only [signal_tail]
  rw [smul_add,smul_add,Finset.smul_sum,add_assoc]
  congr 1
  · rw [one_div]
  congr 1
  · rw [smul_neg,←neg_smul,smul_smul]
    congr 1; ring
  exact Finset.sum_congr rfl fun a _=> by
    rw [smul_smul, ←mul_assoc, inv_mul_cancel₀ two_ne_zero,one_mul]

variable {j:ℕ}{r:Male→Streams}

theorem Looming.flash_snow (h:Looming j r) (M:Male) (I:Type*) [Fintype I] [DecidableEq I]
    (p:Bin) (e:Bound π p) :
    flash (radians p) (snow I (r M)) = bar j M.val (tmap p) ⊗ₖ (1:Op I) := by
  rw [snow,map_smul,map_add,map_one,shadeF,
    show slide (radians p) (r M)=signal j M (tmap p) from funext (h.plays M p e),
    paint,Matrix.smul_kronecker,Matrix.add_kronecker,Matrix.one_kronecker_one]

theorem width_tub (hj:1≤j) :
    (∃ b C:ℝ,0<b ∧ 0<C ∧ ∀ M:Male,∀ a c,Width b (C*1) fun x=> tub (bar j M.val) x a c) ∧
      ∀ M:Male, ∀ p∈Next.Free.baseCube, ∀ a c,Laurent.read (fun x=>tub (bar j M.val) x a c) p=bar j M.val p a c :=

  tub_bill (bent_budget true j hj (fun i:Male=>i.val) fun i=>i.prop)
    (fun _ _ hp _ he=>bar_overlap _ _ hp _ he)

theorem Looming.seam_snow (h:Looming j r) (hj:1≤j) (M:Male)
    (I:Type*) [Fintype I] [DecidableEq I] (x:Cover) :
    seam x (snow I (r M)) = tub (bar j M.val) x ⊗ₖ (1:Op I) := by
  ext ⟨a,d⟩ ⟨c,e⟩
  rw [Matrix.kronecker_apply,seam_apply]
  let f := fun y=> tub (bar j M.val) y a c
  obtain ⟨⟨b,C,hb,hC,w⟩,he⟩ := width_tub hj
  have hb1 (y): ‖f y‖≤‖((C*Real.exp (-b*size y):ℝ):ℂ)‖ := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC.le (Real.exp_pos _).le)]
    simpa only [mul_one] using of_width (w M a c) y
  have f1 : Fast f := fun k=> (fast_kernel C hb k).of_nonneg_of_le
    (fun _=>mul_nonneg (penPos ..).le (norm_nonneg _)) (fun _=>mul_le_mul_of_nonneg_left (hb1 _) (penPos ..).le)
  let g: Silk:=⟨f,f1⟩

  have t : snow I (r M) (a,d) (c,e)= (1:Op I) d e • g := by
    apply E_ext;intro s
    obtain ⟨p,hp,rfl⟩:=reach (t:=s)
    rw [map_smul,E_read g,smul_eq_mul,mul_comm]
    change flash (radians p) (snow I (r M)) (a,d) (c,e)=
      Laurent.read (fun x=>tub (bar j M.val) x a c) (tmap p)*_
    rw [h.flash_snow _ _ _ hp,Matrix.kronecker_apply,he M _ (b_base hp)]
  rw [t,co_smul,mul_comm]

lemma arrives_smul {I:Type*} {F:Filter I} {g:I→Silk} {v:Silk} (x:ℂ) (p : Arrives F g v) :
    Arrives F (fun i => x • g i) (x • v) := by
  simp only [Algebra.smul_def]
  exact (arrives_const ..).mul p

lemma arrives_snow {I : Type*} [Fintype I] [DecidableEq I]
    {κ : Type*} {F:Filter κ} {f:κ→Streams} {u:Streams}
    (e:∀ k,Arrives F (fun i=>f i k) (u k)) (a d) :
    Arrives F (fun i=>snow I (f i) a d) (snow I u a d) := by
  simp only [snow,shade,Matrix.smul_apply,Matrix.add_apply,Matrix.sum_apply]
  apply arrives_smul

  exact Arrives.add (arrives_const ..) (Arrives.sum _ (fun k=> (e k).mul (arrives_const ..)))
