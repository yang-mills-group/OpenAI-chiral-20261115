import GaugeFieldConstruction.Triads
/-!
# Double to single slot. Compact contour argument, change its size
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Complex Cauchy Row Wick Phys Function Set Filter YM.Analysis MeasureTheory
open YM.Maxwell.Free (dilate_integral collar gradient_part shell_cost)
open YM.Maxwell (grad)
open scoped Topology ContDiff BigOperators
variable {x y : E4} {χ : E4→ℝ} {J : Jobs}

def reach (x y : E4) := x+(2:ℝ) • (y-x)
def nearX (x y:E4) := x+(1/2:ℝ) • (y-x)
lemma touch (x) : nearX x ∘ reach x=id := by ext1 i; simp [Function.comp_def, nearX, reach,smul_smul]
lemma free (x) : reach x ∘ nearX x=id := by ext1 i; simp [Function.comp_def, nearX,reach,smul_smul]
lemma visit (x : E4) : HasCompactSupport χ → HasCompactSupport (χ ∘ nearX x) := by
  intro h
  apply IsCompact.of_isClosed_subset (h.image (show Continuous (reach x) by unfold reach; fun_prop)) (isClosed_tsupport _)
  apply closure_minimal _ (h.image (show Continuous (reach x) by unfold reach; fun_prop) |>.isClosed)
  intro i hi; exact ⟨nearX x i,subset_closure hi, congr_fun (free x) i⟩ -- tweak
lemma near_cost (p : Cost χ) : Cost (χ ∘ nearX x) := ⟨p.health.comp (by unfold nearX; fun_prop), visit x p.compact⟩
lemma neighborhood (p : χ =ᶠ[𝓝 x] fun _=>1) : χ ∘ nearX x=ᶠ[𝓝 x] fun _=>1 := p.comp_tendsto (show Tendsto (nearX x) (𝓝 x) (𝓝 x) from by simpa [nearX] using (show Continuous (nearX x) by unfold nearX; fun_prop).continuousAt (x:=x) |>.tendsto) -- tweak
lemma scale_g (p : Cost χ) (i) (x y : E4) : grad i (χ ∘ nearX x) (reach x y)=(1/2:ℝ)*grad i χ y := by
  have H z : HasFDerivAt (nearX x) ((1/2:ℝ) • ContinuousLinearMap.id ℝ E4) z := (((hasFDerivAt_id z).sub_const x).const_smul (1/2:ℝ)).const_add x
  unfold grad D; rw [fderiv_comp (reach x y) (p.health.differentiable (by simp) _) (H _|>.differentiableAt), (H _).fderiv, show nearX x (reach x y)=y from congr_fun (touch x) y]; simp

lemma new_path {ψ : E4→ℝ} (p : Cost χ) (q : Cost ψ) (h : χ =ᶠ[𝓝 x] ψ) (hx : χ =ᶠ[𝓝 x] fun _=>1)
    (K :∀ i (z : E4), z ≠ x → ContDiffAt ℝ ∞ (J i) z) (v :∀ z : E4, z≠x→sumD J z=0) : Flux χ J=Flux ψ J := by
  let F:=χ-ψ; have ht : Cost F:=⟨p.health.sub q.health,p.compact.sub q.compact⟩
  have hw : x∉ tsupport F := notMem_tsupport_iff_eventuallyEq.mpr (by filter_upwards [h] with y hy; exact sub_eq_zero.mpr hy)
  have he:= concentric ht (J:=J) (fun i z hz=> K i z (fun e=>hw (e ▸ hz))) (fun z hz=>v z (fun e=>hw (e ▸ hz)))
  have gp i z: grad i F z=grad i χ z-grad i ψ z:=YM.Maxwell.Bare.grad_sub p.health.contDiffAt q.health.contDiffAt _
  have gs {χ : E4→ℝ} (p:Cost χ) (h : χ =ᶠ[𝓝 x] fun _=> 1) i: Integrable (fun y=>grad i χ y • J i y):= shell_cost p.health p.compact (fun y hy=> (K i y (fun e=> collar h (e ▸ hy))).continuousAt) i
  have hf : Flux F J=Flux χ J- Flux ψ J := by
    simp_rw [flux_sum,gp,sub_smul]; simp_rw [integral_sub (gs p hx _) (gs q (h.symm.trans hx) _), Finset.sum_sub_distrib]
  rw [hf] at he; exact sub_eq_zero.mp he

lemma silence (u : ℝ) (p : Cost χ) (h : χ =ᶠ[𝓝 x] fun _=>1) (hu : 8*u≠1)
    (H : ∀ i y,y≠x→ContDiffAt ℝ ∞ (J i) y) (hp : ∀ y:E4,y≠x→sumD J y=0)
    (f : ∀ i (y:E4),y≠x→ J i (reach x y)=u • J i y) : Flux χ J=0 := by
  let F:= χ ∘ nearX x
  have ht : Flux F J=(8*u) • Flux χ J := by
    rw [flux_sum,flux_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _
    have hk : (∫ y:E4, grad i F y • J i y)=(2:ℝ)^4 • ∫ y:E4, grad i F (reach x y) • J i (reach x y) := by
      rw [dilate_integral (fun y=> grad i F y • J i y) (x-(2:ℝ) • x) 2 (by norm_num)]
      simp_rw [reach,smul_sub, sub_add_eq_add_sub, ← add_sub_assoc]
    rw [hk, ← integral_smul, ← integral_smul]; apply integral_congr_ae; refine Eventually.of_forall fun y=> ?_
    change _ • (grad i F _ • J i _) = (8*u) • (grad i χ y • J i y)
    rw [show grad i F (reach x y)=_ from scale_g p i x y]; by_cases d:y=x
    · subst y; rw [image_eq_zero_of_notMem_tsupport (show x∉tsupport (grad i χ) from fun H=> collar h (gradient_part χ i H))]; simp
    rw [f i y d]; simp only [smul_smul]; congr 1; ring
  have he:= new_path (ψ:=F) p (near_cost p) (h.trans (neighborhood h).symm) h H hp
  rw [ht] at he; let a:=Flux χ J
  have hp : (1-(8*u)) • a=0 := by rw [sub_smul,one_smul,sub_eq_zero]; exact he
  exact (smul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hu.symm)
end YM.GaugeFieldConstruction.Flux.One
