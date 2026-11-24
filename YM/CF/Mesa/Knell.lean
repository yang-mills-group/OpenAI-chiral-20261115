import YM.CF.Mesa.Nadir
import YM.CF.Mesa.Atlas
/-! Radial cone estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric
open scoped Topology NNReal BigOperators InnerProductSpace
variable {E Y Z:Type*} [NormedAddCommGroup E][NormedAddCommGroup Y][NormedAddCommGroup Z][NormedSpace ℝ E][NormedSpace ℝ Y][NormedSpace ℝ Z]
def Story (s:Set E)(f:E→Y):Prop:=∃ K,LipschitzOnWith K f s
lemma cruising {s:Set E}(h:IsCompact s){f:E→Y}{g:Y→Z}(hf:Story s f) (hg:∀ x∈s,ContDiffAt ℝ 1 g (f x)): Story s (g ∘ f):=by
  obtain ⟨K,hK⟩:=hf
  obtain ⟨J,hJ⟩:= LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (h.image_of_continuousOn hK.continuousOn) (f:=g) (by
    rintro x ⟨y,q,rfl⟩; obtain ⟨M,t,h,hp⟩:= (hg y q).exists_lipschitzOnWith; exact ⟨_,t,mem_nhdsWithin_of_mem_nhds h,hp⟩)
  exact ⟨_,hJ.comp hK (mapsTo_image ..)⟩
lemma pairer {f:E→Y}{g:E→Z}{s:Set E}(h:Story s f)(t:Story s g): Story s (fun x=>(f x,g x)):=by
  obtain ⟨k,hk⟩:=h; obtain ⟨l,hl⟩:=t; exact ⟨_,hk.prodMk hl⟩

def rocket (x:E):E:=‖x‖⁻¹ • x
lemma pathX {x:E}(hx:x≠0) : rocket x ∈ Peri E := by
  simp only [rocket, mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
lemma unrocket (x:E) : ‖x‖ • rocket x=x:=by by_cases h:x=0; rw [h,norm_zero,zero_smul]; simp [rocket,smul_smul, h]
lemma rocket_pair {x y:E} (hx:x≠0)(hy:y≠0): ‖x‖*dist (rocket x) (rocket y) ≤ 2*dist x y := calc
  _ = ‖(x-y)+(‖y‖-‖x‖) • rocket y‖ := by
      rw [dist_eq_norm, ← Real.norm_of_nonneg (norm_nonneg x)] -- danger rewrite x norm inside left only
      simp only [Real.norm_eq_abs,abs_norm]
      rw [show ‖x‖ * ‖rocket x-rocket y‖=‖‖x‖ • (rocket x-rocket y)‖ by simp [norm_smul]]
      rw [smul_sub, unrocket, sub_smul,unrocket]; congr 1; abel
  _ ≤ ‖x-y‖+‖(‖y‖-‖x‖) • rocket y‖:= norm_add_le ..
  _ ≤ _:= by
    rw [norm_smul,show ‖rocket y‖=1 by simpa [Peri,mem_sphere] using pathX hy, Real.norm_eq_abs, mul_one, abs_sub_comm]
    rw [dist_eq_norm]; linarith [abs_norm_sub_norm_le x y]

def brisk (f:E→Y)(x:E):Y:=‖x‖ • f (rocket x)
lemma bristles {f:E→Y}{C K:ℝ≥0} (hc:∀ x∈ Peri E,‖f x‖≤C)(hK:LipschitzOnWith K f (Peri E)):LipschitzWith (2*K+C) (brisk f):=by
  have hg {x:E} (hx:x≠0) : dist (brisk f x) (brisk f 0) ≤ (↑(2*K+C):ℝ)*dist x 0 := by
    simp only [brisk,norm_zero,zero_smul,dist_zero_right,norm_smul, Real.norm_eq_abs,abs_norm]
    calc
      _ ≤ ‖x‖ * C := mul_le_mul_of_nonneg_left (hc _ (pathX hx)) (norm_nonneg _)
      _ ≤ _ := by push_cast; nlinarith [norm_nonneg x,K.coe_nonneg]
  apply LipschitzWith.of_dist_le_mul; intro x y
  by_cases hx:x=0
  · subst x; rw [dist_comm,dist_comm (0:E)]; by_cases h:y=0; simp [h]; exact hg h
  by_cases hy:y=0
  · subst y; exact hg hx
  calc
    _ = ‖‖x‖ • (f (rocket x)-f (rocket y))+(‖x‖-‖y‖) • f (rocket y)‖ := by rw [dist_eq_norm, sub_smul, smul_sub]; unfold brisk; congr 1; abel
    _ ≤ ‖‖x‖ • (f (rocket x)-f (rocket y))‖+‖(‖x‖-‖y‖) • f (rocket y)‖:= norm_add_le ..
    _ ≤ ‖x‖ * ((K:ℝ) * dist (rocket x) (rocket y))+dist x y*C:= by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_norm]
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (mul_le_mul ?_ (hc _ (pathX hy)) (norm_nonneg _) (dist_nonneg))
      · rw [← dist_eq_norm]; exact hK.dist_le_mul _ (pathX hx) _ (pathX hy)
      rw [dist_eq_norm]; exact abs_norm_sub_norm_le ..
    _ ≤ _ := by push_cast; nlinarith [mul_le_mul_of_nonneg_left (rocket_pair hx hy) K.coe_nonneg]

section
variable {n:Type*}[Fintype n] {d:ℕ}
def dome (p:Ket n)(f:Board d→Ket n)(x:Board d):Ket n:=(1-‖x‖) • (-p) + brisk f x
set_option maxHeartbeats 500000 in
lemma dome_st {p:Ket n}(hp:‖p‖=1){f:Board d→Ket n}{K:ℝ≥0}(h:LipschitzOnWith K f (Peri (Board d)))(H:MapsTo f (Peri (Board d)) (Peri (Ket n))) :Story (closedBall 0 1) (dome p f):=by
  have ht : LipschitzOnWith 1 (fun x:Board d=>‖x‖) (closedBall 0 1) := lipschitzWith_one_norm.lipschitzOnWith
  have hh := (bristles (C:=1) (fun x hx=> by simp only [NNReal.coe_one]; refine le_of_eq ?_; simpa [Peri,mem_sphere] using H hx) h).lipschitzOnWith (s:=closedBall 0 1)
  let g (v:ℝ × Ket n) := (1-v.1) • (-p)+v.2
  have hG (v:ℝ × Ket n) : ContDiffAt ℝ 1 g v:=( (contDiffAt_const.sub contDiffAt_fst).smul contDiffAt_const).add contDiffAt_snd
  have he:= cruising (isCompact_closedBall (0:Board d) 1) (g:=g)
    (pairer (f:=fun x:Board d=>‖x‖) (g:=brisk f) ⟨1,ht⟩ ⟨_,hh⟩) (fun x hx=>hG _)
  exact he

lemma cone_pos {p:Ket n}(hp:‖p‖=1){v:Ket n}(hv:‖v‖=1)(hx:p≠v){r:ℝ}(hr:0<r)(h:r≤1)(a:ℝ)(ha:0≤a): (1-r) • (-p)+r • v≠ a • p:=by
  intro he
  let T:=a+(1-r)
  have hh:0≤T:=by dsimp [T]; linarith
  have hk : r • v = T • p:=by dsimp only [T]; rw [add_smul]; rw [smul_neg] at he; rw [← he]; abel
  have hT:=congr_arg norm hk; rw [norm_smul,norm_smul,hp,hv,Real.norm_eq_abs,abs_of_pos hr,Real.norm_eq_abs,abs_of_nonneg hh,mul_one,mul_one] at hT
  rw [← hT] at hk
  apply hx; calc
    p=r⁻¹ • (r • p):=by rw [smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
    _=v:=by rw [←hk,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
lemma launched {p:Ket n}(hp:‖p‖=1){f:Board d→Ket n}(H:MapsTo f (Peri (Board d)) (Peri (Ket n)))(g:p∉ f '' Peri (Board d)) {x:Board d}(h:x∈closedBall 0 1):
    dome p f x ≠ 0 ∧ rocket (dome p f x) ∈ Peri (Ket n) ∧ p ≠ rocket (dome p f x) := by
  have he (a:ℝ)(ha:0≤a): dome p f x ≠ a • p:=by
    by_cases hx:x=0
    · simp only [hx,dome,brisk, norm_zero,sub_zero,one_smul,zero_smul,add_zero]; intro ho
      rw [← one_smul ℝ p, neg_eq_iff_add_eq_zero] at ho
      have hh:a+1≠0:=by linarith
      apply hh; rw [show a+1=1+a by ring]; apply (smul_eq_zero.mp (show (1+a) • p=0 from ?_)).resolve_right
      · exact norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero)
      rw [add_smul]; simpa [add_comm] using ho
    exact cone_pos hp (by simpa [Peri,mem_sphere] using H (pathX hx)) (fun hg=>g ⟨_,pathX hx,hg.symm⟩) (norm_pos_iff.mpr hx) (by simpa using h) a ha
  have hx : dome p f x ≠ 0 := by simpa using he 0 le_rfl
  refine ⟨hx,pathX hx,fun v=>he ‖dome p f x‖ (norm_nonneg _) (?_)⟩; calc
    _ = _:= (unrocket (dome p f x)).symm
    _ = _:=by rw [←v]
end
end YM.CF.Mesa
