import GaugeFieldConstruction.AidaQc
/-!
# Fubini for thinner contour. Move independently, cancel y jacobian and compact staff.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Salam
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Metric
open scoped Topology BigOperators ContDiff Classical
variable {n : ℕ} {b : Bulb}{p : Test (n+1)}{a:Bulb} (h:Works b p 0)(q:RespectQc p a)
variable {e:ℝ}(v:0<e){i j:Axis}{m:ℕ}{L:Axis→ E4→ℝ}{K:Payroll (n+1)}(p':RespectQc p (dockScaleQc e v))(r:TwistQc K m L) (R:Points (n+2)→ℂ) (c:PlaqueQc R)
variable (F:∀ y:E4,AnnulusQc e y→∀ x∈tsupport p,LensQc y x∈conf (n+2))
abbrev ArmentQc (L:Axis→E4→ℝ)(i j:Axis):E4→ℝ:= fun y=> L j y * D (basis i) DokiQc.f y
lemma LevelQc (x:E4)(h:AnnulusQc 1 x)(z:ℝ)(q:0<z): AnnulusQc z (z • x):=by
 have he:‖z • x‖=z* ‖x‖:=by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg q.le]
 constructor
 · rw [he]; exact lt_mul_of_one_lt_right q h.low
 rw [he,mul_comm 2]; exact mul_lt_mul_of_pos_left (by simpa using h.high) q
noncomputable def SoapQc (i j:Axis)(L:Axis→E4→ℝ)(p: Test (n+1))(e:ℝ)(R:Points (n+2)→ℂ)(t:E4×Points (n+1)): ℂ:= ArmentQc L i j t.1 • (p t.2*R (LensQc (e • t.1) t.2))
include c v F r in
lemma SoapTasteQc (i j:Axis): Integrable (SoapQc i j L p e R):=by
 let T:=tsupport p; let U:=tsupport (ArmentQc L i j); let w:= U ×ˢ T; let l:=fun t:E4×Points (n+1)=> LensQc (e • t.1) t.2; have hl:Continuous l:= lensContinuousQc.comp ((continuous_fst.const_smul e).prodMk continuous_snd)
 have hB: U ⊆ run (DokiQc.LED i):= tsupport_mul_subset_right
 have htU:IsCompact U:= (show IsCompact _ from (DokiQc.LED i).c).of_isClosed_subset (isClosed_tsupport _) hB
 obtain ⟨A,ha,a⟩:=c.tiled _ ((htU.prod p.hasCompactSupport).image hl) (image_subset_iff.mpr fun ⟨t,x⟩ w=> F _ (LevelQc _ (faultQc ((cone _ _) (hB w.1))) _ v) _ w.2)
 let f(t:E4×Points (n+1)):= ArmentQc L i j t.1; let g(t:E4×Points (n+1)):=p t.2
 have h0:Continuous (ArmentQc L i j):=(r.expense j).mul (b_sm DokiQc.f DokiQc.d _).continuous; have hf:Continuous f:= h0.comp continuous_fst; have hg:Continuous g:= p.continuous.comp continuous_snd
 let V:E4×Points (n+1)→ℝ:= fun t=> ‖f t‖* ‖g t‖
 have hV:HasCompactSupport V:= by
    refine HasCompactSupport.intro (htU.prod p.hasCompactSupport) ?_; intro t v; by_cases h:t.1∉U; · have h:f t=0:=image_eq_zero_of_notMem_tsupport (f:=ArmentQc L i j) h; unfold V; rw [h]; simp
    have h':g t=0:=image_eq_zero_of_notMem_tsupport (f:=p) (show t.2∉T from fun k=>v ⟨Classical.not_not.mp h,k⟩); unfold V; rw[h']; simp
 refine (((hf.norm.mul hg.norm).integrable_of_hasCompactSupport hV).mul_const A).mono' (hf.measurable.smul (hg.measurable.mul (c.bright.comp hl.measurable))).aestronglyMeasurable (Eventually.of_forall fun t=>?_); change ‖f t • (g t*R (l t))‖ ≤ V t*A; unfold V; rw [norm_smul, norm_mul (g t) (R (l t)),←mul_assoc]
 by_cases h:t∈w; · exact mul_le_mul_of_nonneg_left (a _ (mem_image_of_mem _ h)) (by positivity)
 by_cases h':t.1∈U
 · have h:g t=0:=image_eq_zero_of_notMem_tsupport (f:=p) (show t.2∉T from fun k=> h ⟨h',k⟩); simp [h]
 have h:f t=0:=image_eq_zero_of_notMem_tsupport (f:=ArmentQc L i j) h'; simp [h]
include c v F r in
lemma ShopsIntQc (i j:Axis): Integrable (fun x:E4=> ArmentQc L i j x • PieceQc R p (e • x)):=by
 have hi : Integrable (fun x:E4=> ∫ y:Points (n+1),SoapQc i j L p e R (x,y)):= (SoapTasteQc v r R c F i j).integral_prod_left
 refine hi.congr (Eventually.of_forall fun x=>?_); unfold SoapQc PieceQc; simp only
 rw [integral_smul]
lemma measuredQc : MeasurePreserving ((fuse (n:=n)).symm) volume volume:= by
 have he: MeasurePreserving (fuse (n:=n)) volume volume:= (WithLp.volume_preserving_ofLp _ _).comp Points.peel.measurePreserving
 exact he.symm (e:=fuse.toHomeomorph.toMeasurableEquiv)
include c v F r
lemma DonorsQc : Test.applyTo (YoungQc h p' K i j) R= (e^(3+m)) • ∫ y:E4, ArmentQc L i j y • PieceQc R p (e • y):=by
 let t:= YoungQc h p' K i j; let f(x:Points (n+2)):= t x*R x; let G:E4×Points (n+1)→ℂ:= f ∘ fuse.symm
 have hf:Integrable f := BondCostQc t R c; have hG:Integrable G:= measuredQc.integrable_comp_of_integrable hf
 have he(x:Points (n+1)): (∫ z:E4,G (z,x))=e^(3+m) • ∫ y:E4, SoapQc i j L p e R (y,x):=by
    let H(z:E4):= f (LensQc z x)
    have h1:(∫ z:E4,H z)= ∫ z:E4,G (z,x):=integral_add_left_eq_self (fun z:E4=>G (z,x)) (head x) -- tune
    rw[←h1]
    have H4:Module.finrank ℝ E4=4:=by simp [Axis,E4]
    have ht := Measure.integral_comp_smul_of_nonneg volume H e (hR:=v.le)
    have hy:H ∘ (fun z:E4=> e • z)=fun y=> (e⁻¹*e^m) • SoapQc i j L p e R (y,x):=funext fun y=>by
       unfold H f t SoapQc ArmentQc; simp only [Function.comp_apply]; rw[TallonQc h v p' r,smul_mul_assoc,smul_mul_assoc] -- tune
    change (∫ x,(H ∘ fun z:E4=>e • z) x)=_ at ht; rw[hy, integral_smul,H4] at ht
    nth_rw 1 [show (∫ z:E4,H z)=e^4 • ( (e^4)⁻¹ • ∫ z:E4,H z) from (smul_inv_smul₀ (by positivity) _).symm]; rw[←ht,smul_smul, show e^4*(e⁻¹*e^m) = e^(3+m) from (by field_simp; ring)] -- tune
 change (∫ z:Points (n+2),f z)= _
 have ht:=SoapTasteQc v r R c F i j
 rw [← measuredQc.integral_comp (fuse.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding) f]; change (∫ t:E4×Points (n+1),G t ∂(volume.prod volume))= _; rw[integral_prod_symm G hG]; simp_rw [he]; rw [integral_smul,←integral_prod_symm _ ht, integral_prod _ ht]; congr 1; apply integral_congr_ae; apply Eventually.of_forall; intro x; unfold SoapQc PieceQc; simp only; rw[integral_smul] -- tune
#print axioms SoapTasteQc
#print axioms ShopsIntQc
#print axioms DonorsQc
end YM.GaugeFieldConstruction.Fathom.Salam
