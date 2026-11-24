import YM.CF.Mew.Terms
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Roots
open Function Set Metric Mew MeasureTheory Filter Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E F N :Type*}[Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
variable [NormedCommRing N][NormedAlgebra ℂ N][CompleteSpace N]
variable {f g u v:Key I→E}{a b a' b': Key I→N}{s t:List I}
lemma perm_ζ (p:River f)(i j:I) :EqOn (cutI (cutI f i) j) (cutI (cutI f j) i) (hill I):=by
 by_cases g:i=j; subst i; exact fun _ _=>rfl
 intro z v; unfold cutI
 let F(x y:ℝ):= (homeB x)⁻¹ • ((homeB y)⁻¹ • f (update (update z j (homeB x)) i (homeB y)))
 let U(x:ℝ×ℝ):=update (update z j (homeB x.1)) i (homeB x.2)
 have h(x y:ℝ):F x y=(homeB y)⁻¹ • ((homeB x)⁻¹ • f (update (update z i (homeB y)) j (homeB x))):=by unfold F; rw [update_comm (Ne.symm g),smul_comm] -- orientation
 have he:Continuous U:= (continuous_update (A:=fun _:I=>ℂ) i).comp (((under_r j z).comp ((continuous_circleMap _ _).comp continuous_fst)).prodMk ((continuous_circleMap ..).comp continuous_snd))
 have ht(x:ℝ×ℝ):U x∈hill I:= fill_I (fill_I v _ (homeC _)) _ (homeC _)
 have hx:Continuous fun x=>(homeB x)⁻¹:= (continuous_circleMap ..).inv₀ (fun x=> norm_ne_zero_iff.mp (by rw [home_q]; norm_num))
 have hp:Continuous (uncurry F):= (hx.comp continuous_fst).smul ((hx.comp continuous_snd).smul (p.shore.comp_continuous he ht))
 obtain ⟨C,b,w⟩:=p.budget; let μ:= sky.prod sky
 have hu:Integrable (uncurry F) μ:=(integrable_const (μ:=μ) (c:=C)).mono' hp.aestronglyMeasurable (ae_of_all _ fun i=>by change ‖F i.1 i.2‖≤_; simp_rw [F,norm_smul,norm_inv,home_q,inv_one,one_mul]; exact w _ (ht _))
 simp_rw [←MeasureTheory.integral_smul]
 change (∫ x, (∫ y,F x y∂sky)∂sky)=_
 rw [integral_integral_swap hu]; simp_rw [h]
lemma move_ζ (p:t.Perm s)(h:River f): EqOn (lance f t) (lance f s) (hill I):=by
 induction p generalizing f with
 | nil=> exact fun _ _=>rfl
 | cons i _ ih=> exact ih (h.flow i)
 | swap i j l=> exact lace_C l (perm_ζ h j i)
 | trans p q ih kh=> exact (ih h).trans (kh h)
lemma orbit_ζ (p:River f)(q:t.Nodup) : gemI f t.toFinset= tipI f t:=by
 refine move_ζ ?_ p roots
 apply List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup ..) q; simp [Cue]
end YM.CF.Roots
