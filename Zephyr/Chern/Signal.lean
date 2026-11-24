import Zephyr.Chern.Attire
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Filter Topology Silk YM.CF YM.CF.Fir YM.Next.Free YM.CF.Jill


open scoped Real

@[simp] lemma signal_head (j : ℕ) (M : Male) (p) :
    signal j M p 0= 1-2*shell j M.val p := rfl
@[simp] lemma signal_tail (j : ℕ) (M : Male) (p) (i:Axis) :
    signal j M p i.succ= 2*skin j M.val p i := rfl
@[simp] lemma tmap_zero : tmap 0=0 := rfl

lemma signal_round (j : ℕ) (M : Male) (p:Bin) (hp : Bound π p) :
    signal j M (tmap p) ⬝ᵥ signal j M (tmap p)=1 ∧
    (signal j M (tmap p) 0).im=0 ∧ -1≤(signal j M (tmap p) 0).re := by
  let h:= base_subset_realCube zone_pos (b_base hp)
  by_cases e : tmap p=0
  · rw [e,dotProduct,Fin.sum_univ_succ]; simp
  let g:=mixL j M.val (tmap p)
  have a : prodM g g=((∑ i,(g i).re^2:ℝ):ℂ) :=
    prodM_self _ (phys_mix j M.val M.property _ h.1)
  have k : 0≤∑ i,(g i).re^2 := Finset.sum_nonneg fun _ _=> sq_nonneg _

  have y : shell j M.val (tmap p)= (1+prodM g g)⁻¹ := shell_inv _ _ h e
  constructor
  · rw [dotProduct,Fin.sum_univ_succ,signal_head]
    simp_rw [signal_tail,skin_mix j M.val h,Pi.smul_apply,smul_eq_mul,y]
    have w := graphs_ne (phys_mix j M.val M.property _ h.1)
    let b:= (1+prodM g g)⁻¹
    change (1-2*b)*(1-2*b)+∑ i,2*(b*g i)*(2*(b*g i))=1
    conv_lhs =>
      enter [2,2,i]; rw [show 2*(b*g i)*(2*(b*g i))= 4*b^2*(g i*g i) by ring]
    rw [← Finset.mul_sum, ←prodM]
    have h1 : 1+prodM g g ≠0 := w
    unfold b;field_simp;ring
  rw [signal_head,y,a,← Complex.ofReal_one,←Complex.ofReal_add,←Complex.ofReal_inv]
  have he : (1+∑ i,(g i).re^2)⁻¹≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  let c := (1+∑ i,(g i).re^2)⁻¹
  change (((1:ℝ):ℂ) -2*c).im=0 ∧ -1≤(((1:ℝ):ℂ)-2*c).re
  change c≤1 at he
  simp
  linarith

lemma reach {t:Brill} : ∃ p, Bound π p ∧ radians p=t := by
  obtain ⟨p,e,h⟩:=rad_cover t
  exact ⟨p,(pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr (fun i=>by rw [Real.norm_eq_abs]; exact h i),e⟩

variable {j:ℕ} {r:Male→Streams}

lemma Looming.round (p : Looming j r) (i:Male) : Sphere (r i) ∧
    ∀ t,(E t (r i 0)).im=0 ∧ -1≤(E t (r i 0)).re := by
  constructor
  · apply E_ext; intro t
    obtain ⟨q,hq,rfl⟩:=reach (t:=t)
    simpa only [dotProduct,map_sum,map_mul,map_one,p.plays _ _ hq]
      using! (signal_round j i q hq).1
  intro t
  obtain ⟨q,hq,rfl⟩:=reach (t:=t)
  rw [p.plays _ _ hq]
  exact (signal_round j i q hq).2

lemma Looming.dip (p : Looming j r) (hj : 1≤j) (t:Brill) (h:t≠0) :
    ∃ a:ℝ,a<1 ∧ ∀ i, (E t (r i 0)).re ≤ a := by
  obtain ⟨q,hq,rfl⟩:=reach (t:=t)
  have g : 0<‖q‖ := norm_pos_iff.mpr (by rintro rfl;exact h rad_zero)

  obtain ⟨b,hb,H⟩:=Onyx.cane (A:=crop) (x:=RayH.x) (fun _=>rfl) RayH.cap RayH.M hj
  refine ⟨1-2*(b*‖q‖^2),sub_lt_self _ (by positivity), fun i=>?_⟩
  have y : b*‖q‖^2≤ _ := H ⟨i,q,hq,g⟩
  rw [p.plays _ _ hq,signal_head]
  suffices 1-2*(shell j i.val (tmap q)).re≤_ from by simpa
  linarith

lemma Looming.origin (p : Looming j r) (M:Male) :
    (E 0 (r M 0))=1 ∧ ∀ a:Axis, (E 0 (r M a.succ))=0 := by
  rw [←rad_zero]
  simp_rw [p.plays _ _ (show Bound π 0 by unfold Bound; simp [Real.pi_pos.le]),signal_head,
    signal_tail,tmap_zero,shell_origin,skin_origin]
  simp

/-- Use algebraic sphere condition instead of separate projection analysis
for the normal derivative. -/
lemma Looming.normal (p:Looming j r) (i : Male) (a : Axis) :
    E 0 (D a (r i 0))=0 := by
  have h := congrArg (fun v => E 0 (D a v)) (p.round i).1
  rw [dotProduct,Fin.sum_univ_succ] at h
  simp only [map_add,map_sum,D_mul,map_mul,Derivation.map_one_eq_zero,map_zero,
    (p.origin i).1,(p.origin i).2,mul_one,one_mul,mul_zero,zero_mul, Finset.sum_const,
    add_zero,smul_zero] at h
  exact mul_eq_zero.mp ((two_mul _).trans h)|>.resolve_left two_ne_zero
