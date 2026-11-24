import YM.CF.Souk.Dune
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort Finset
variable {z E': Fish ι → Fish τ} {Y H : Fish τ→ℝ}
abbrev costU(x:Fish τ):ℝ:= ∑ i, |x i|
structure FloorZ (Y:Fish τ→ℝ)(C:ℝ):Prop where
 stiff:ContDiffAt ℝ 2 Y 0
 offer(i:Fin 1→τ): |Uniform.entry Y 0 i| ≤ C
 charge (i: Fin 2→τ):|Uniform.entry Y 0 i| ≤ C
lemma FloorZ.set (h:FloorZ Y C)(x:Fish τ): |fderiv ℝ Y 0 x| ≤ costU x*C:=by
 let U:=fderiv ℝ Y 0; have ht(i:τ): |U (bolt i)| ≤ C:=by
    have hh:=h.offer ![i]; unfold Uniform.entry at hh; rw [iteratedFDeriv_one_apply] at hh; exact hh
 nth_rw 1 [← Uniform.combine x]; rw [map_sum]; simp_rw [map_smul,smul_eq_mul]; apply (abs_sum_le_sum_abs ..).trans; unfold costU; rw [Finset.sum_mul]; exact Finset.sum_le_sum fun i _=> by rw [abs_mul]; gcongr; exact ht i
abbrev tierU(Y:Fish τ→ℝ)(x z: Fish τ):= fderiv ℝ (fderiv ℝ Y) 0 x z
lemma FloorZ.cover(h:FloorZ Y C)(x z:Fish τ):|tierU Y x z| ≤ costU x * (costU z*C):=by
 have he i j :|tierU Y (bolt i) (bolt j)|≤ C:=by have ht:=h.charge ![i,j]; unfold Uniform.entry at ht; rw [iteratedFDeriv_two_apply] at ht; exact ht
 have hw(i:τ):|tierU Y (bolt i) z| ≤ costU z*C:=by
    unfold tierU; nth_rw 1 [← Uniform.combine z]; rw [map_sum]; unfold costU; rw [Finset.sum_mul]; refine (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j _=>?_); rw [map_smul,smul_eq_mul,abs_mul]; exact mul_le_mul_of_nonneg_left (he i j) (abs_nonneg _)
 unfold tierU; nth_rw 1 [← Uniform.combine x]; rw [map_sum, _root_.sum_apply]; unfold costU; rw [Finset.sum_mul]; apply (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum _); intro i hi; rw [map_smul,_root_.smul_apply, smul_eq_mul,abs_mul]; exact mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
lemma tierX(F:E→ B)(v u:E)(h: ContDiffAt ℝ 2 F 0): fderiv ℝ (fderiv ℝ F) 0 v u=fderiv ℝ (fun x=> fderiv ℝ F x u) 0 v:=by
 erw [(((h.fderiv_right (m:=1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const u 0)).fderiv]; simp
lemma tierC(h:ContDiffAt ℝ 2 Y 0)(hv:ContDiffAt ℝ 2 z 0)(hm:z 0=0)(q:Fin 2→ι):
 let x:=Uniform.entry z 0 q; let u(a:ι):=Uniform.entry z 0 (fun _ : Fin 1=>a)
 Uniform.entry (Y ∘ z) 0 q= fderiv ℝ Y 0 x+tierU Y (u (q 0)) (u (q 1)):=by
 intro x u
 have ht:ContDiffAt ℝ 2 Y (z 0):=hm.symm ▸ h; let F:=fderiv ℝ (fderiv ℝ Y); let v:= bolt (q 0); let w:= bolt (q 1); let P:=fderiv ℝ z; let U:=fun y:Fish ι=> fderiv ℝ Y (z y) (P y w)
 have he:(fun y=> fderiv ℝ (Y ∘ z) y w)=ᶠ[𝓝 0] U:=by
    filter_upwards [hv.eventually (by simp),hv.continuousAt.eventually (ht.eventually (by simp))] with y hy hh; rw [fderiv_comp y (hh.differentiableAt (by norm_num)) (hy.differentiableAt (by norm_num))]; rfl
 let m:=(fderiv ℝ Y) ∘ z; let y:=fun y=>P y w
 have hY : HasFDerivAt m _ 0 := ((ht.fderiv_right (m:=1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt.comp 0 (hv.differentiableAt (by norm_num)).hasFDerivAt
 have hh : HasFDerivAt y _ 0:= (((hv.fderiv_right (m:=1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const w 0))
 unfold Uniform.entry x u; simp_rw [Uniform.entry,iteratedFDeriv_two_apply,iteratedFDeriv_one_apply]; rw [tierX _ _ _ (ht.comp 0 hv), he.fderiv_eq,show fderiv ℝ U 0=_ from (hY.clm_apply hh).fderiv]; simp [tierU,y,m,P,v,w,hm]
lemma roll_E(h:FloorZ Y C)(hm:z 0=0)(hu:E' 0=0)(hv:ContDiffAt ℝ 2 z 0)(he:ContDiffAt ℝ 2 E' 0)
 (hc:0 ≤ C)(hd:∀ i:ι,costU (Uniform.entry z 0 (fun _ : Fin 1=>i))≤ Q ∧ costU (Uniform.entry E' 0 (fun _ : Fin 1=>i))≤ Q)
 (hT:∀ (i:ℕ), i<2→∀ (q:Fin (i+1)→ι), costU (Uniform.entry (z-E') 0 q)≤ t)
 (q:Fin 2→ι): |Uniform.entry (Y ∘ z) 0 q-Uniform.entry (Y ∘ E') 0 q| ≤ t*C +2*t*(Q*C) :=by
 let u(x:Fish ι→Fish τ)(i:ι):= Uniform.entry x 0 (fun _ : Fin 1=> i)
 let L:=fderiv ℝ Y 0; let v:=Uniform.entry z 0 q; let w:= Uniform.entry E' 0 q
 have hh j(hj:j ≤ 2)(q:Fin j→ι): Uniform.entry (z-E') 0 q=Uniform.entry z 0 q-Uniform.entry E' 0 q:=by unfold Uniform.entry; rw [iteratedFDeriv_sub_apply (hv.of_le (by norm_cast)) (he.of_le (by norm_cast))]; rfl
 rw [tierC h.stiff hv hm,tierC h.stiff he hu]; dsimp only -- tune
 let a:= q 0; let b:= q 1; let x:= u z a; let y:=u z b; let k:=u E' a; let j:=u E' b; have hp : (L v+tierU Y x y)-(L w+tierU Y k j) = L (v-w)+(tierU Y (x-k) y+tierU Y k (y-j)):=by unfold tierU; rw [map_sub,map_sub,map_sub,_root_.sub_apply]; abel
 have hL(i:ι): costU (u z i-u E' i)≤t:=by unfold u; rw [← hh 1 (by decide)]; exact hT 0 (by omega) _
 have hnn(y:Fish τ):0≤costU y:=Finset.sum_nonneg fun _ _=>abs_nonneg _; have hG:0≤Q:=(hnn _).trans (hd a).1
 rw [hp]
 apply (abs_add_le ..).trans
 have hz:costU (v-w) ≤t:=by unfold v w; rw [← hh 2 (by decide)]; apply hT 1 (by decide)
 exact add_le_add ((h.set _).trans (mul_le_mul_of_nonneg_right hz hc)) ((abs_add_le ..).trans ((add_le_add ((h.cover _ y).trans (mul_le_mul (hL a) (mul_le_mul_of_nonneg_right (hd b).1 hc) (mul_nonneg (hnn _) hc) ((hnn _).trans hz))) ((h.cover k _).trans (mul_le_mul (hd a).2 (mul_le_mul_of_nonneg_right (hL b) hc) (mul_nonneg (hnn _) hc) hG))).trans_eq (by ring)))
lemma rise(h:FloorZ Y C)(hm:z 0=0)(hv:ContDiffAt ℝ 2 z 0) (ht:0≤C)(hp:0≤Q) (hf:∀ (i:ℕ), i<2→∀ j:Fin (i+1)→ι,costU (Uniform.entry z 0 j) ≤ Q)(q:Fin 2→ι):|Uniform.entry (Y∘z) 0 q| ≤ Q*C+Q*(Q*C):=by
 rw [tierC h.stiff hv hm]; exact (abs_add_le ..).trans (add_le_add ((h.set _).trans (mul_le_mul_of_nonneg_right (hf 1 (by decide) q) ht)) ((h.cover _ _).trans (mul_le_mul (hf 0 (by decide) _) (mul_le_mul_of_nonneg_right (hf 0 (by decide) _) ht) (mul_nonneg (Finset.sum_nonneg fun _ _=> abs_nonneg _) ht) hp))) -- corners
end YM.CF.Souk
