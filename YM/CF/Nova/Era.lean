import YM.CF.Nova.Boot
import YM.CF.Vale.Sail
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Nova
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc Pic MeasureTheory Wilson
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace
variable {m L B N:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a l r t w η τ:ℝ}{P:Grasp Y B e}{H:Pearl P}(D:Span H K b v c l r n)(p:n≤ (CSide m B).val)
open scoped Matrix.Norms.Frobenius in
lemma boundedFrame:∃ C:ℝ,0<C∧∀ u:E,∀ i j, ‖fund u i j-(1: Op SU.F) i j‖ ≤ C * SU.group.chord u:=by
 refine ⟨Real.sqrt SU.group.repDim,SU.group.colorScale_pos,fun u i j=>?_⟩; unfold Gauge.chord; rw [mul_div_cancel₀ _ (show Real.sqrt (↑SU.group.repDim:ℝ) ≠ 0 from SU.group.colorScale_pos.ne')]; -- tune
 let A:=fund u-1; change ‖A i j‖ ≤ ‖A‖; apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1; rw [Gauge.frob_sq]
 have he: (A*star A).trace.re= ∑ i:SU.F,∑ j:SU.F,‖A i j‖^2:=by unfold Matrix.trace; simp only [Complex.re_sum,Matrix.diag_apply,Matrix.mul_apply]; apply sum_congr rfl; intro i _; exact sum_congr rfl fun j _=> inner_self_eq_norm_sq (𝕜:=ℂ) (A i j) -- tune
 rw [he]; exact le_trans (single_le_sum (f:=fun j=> ‖A i j‖^2) (fun j _=>sq_nonneg _) (mem_univ _)) (single_le_sum (f:=fun i=>∑ j, ‖A i j‖^2) (fun i _=> sum_nonneg fun _ _=>sq_nonneg _) (mem_univ _))
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma snow_b : ∃ C:ℝ,0<C∧∀ N:Side,∀ u:Bkg N,∀ x:ℝ,RG.flags x u=∅→PlaqBound firstF u (C*x):=by
 obtain ⟨C,h,H⟩:=boundedFrame
 refine ⟨5*C,mul_pos (by norm_num) h,fun n U x g i a b h'=>?_⟩
 have hp(a b:Axis)(p:a<b):SU.group.chord (travel U i (square a b))≤ x:=by
   let P:Face (Per n):= ⟨i,(a,b),p⟩; exact WilsonStartup.healthy_chord P _ (by simp [RG.Healthy,g])
 let y:=travel U i (square a b); have ht: SU.group.chord y ≤ x:=by
   rcases lt_or_gt_of_ne h' with t|t; exact hp _ _ t
   rw [show y=(travel U i (square b a))⁻¹ from ?_,Gauge.chord_inv]; exact hp _ _ t
   nth_rw 1 [←travel_reverse (square b a)]; rw [square_stop]; rfl
 have he:0≤C*x:=mul_nonneg h.le ((SU.group.chord_nonneg _).trans ht)
 change ‖fund y-1‖ ≤ _; refine (cost_D (E:=SU.F) _ (fun i j=> (H y i j).trans (mul_le_mul_of_nonneg_left ht h.le)) he).trans_eq (by simp [F]; ring)
-- measure-preserving one-form center translation
lemma welt_p (t:Hat): MeasurePreserving (fun u:Bkg N=>welt u t) (prior group N) (prior group N):=by
 refine measurePreserving_pi (ι:=Edge (Site N)) (f:=fun i v=> wob N (fun a:Axis=>central^(t a).val) i * v) _ _ (fun i=>?_); simpa using (SU.group.preserve_two_sided (wob N (fun a=>central^(t a).val) i) 1)
def wEquiv (N:Side)(t:Hat): Bkg N≃ᵐBkg N:= (Homeomorph.mulLeft (wob N fun a=>central^(t a).val)).toMeasurableEquiv
lemma wE(t:Hat)(p:Bkg N):wEquiv N t p=welt p t:=rfl
lemma flags_t(u: Bkg N)(a:ℝ)(t:Hat): RG.flags a (welt u t)= RG.flags a u:=by ext; rw [RG.flags_spec,RG.flags_spec]; simp_rw [faceValue,square_c] -- tun
open Reef Vale RG WilsonStartup -- namespace
lemma basic_c(u:Config SU.group N)(t:Hat)(b:Clip): basicP b (welt u t)=basicP b u:=by unfold basicP Vale.ren energy WilsonStartup.residual faceValue; simp_rw [ echo_t,square_c] -- order
open scoped Matrix.Norms.Frobenius in
lemma ren_c(b:Clip): Continuous (fun i: Config SU.group N=> basicP b i):=by
 have hp: Continuous (fun i:Config SU.group N=> ren b i):=Continuous.sub energy_cont (continuous_finsetSum _ (fun t _=>continuous_const.mul (by
    change Continuous fun x=>residual SU.group t x
    simp_rw [WilsonStartup.residual,← Quad.surplus_actual]; exact Quad.surplusMat_diff (G:=SU.group)|>.continuous.comp (SU.group.continuous_mat.comp (continuous_travel ..)))))
 exact (hp.add (hp.comp (f:= Reef.echo) (continuous_pi fun j=>Reef.icyC.comp (continuous_apply j)))).div_const _
def Calm(G:Gauge)(n: Side)(x:ℝ):Set (Config G n):= {u|flags x u=∅}
lemma calm_m(G:Gauge)(n:Side)(x:ℝ): MeasurableSet (Calm G n x):= flags_measurable_eq x ∅ -- tune
lemma calm_p(G:Gauge)(n:Side)(x:ℝ)(p:0<x):Calm G n x ∈𝓝 (1:Config G n):=by
 unfold Calm
 have he(a:Face (Per n)) : ∀ᶠ u:Config G n in 𝓝 1,G.chord (faceValue u a)≤x:=by
    apply ((G.continuous_chord.comp (continuous_travel _ _)).tendsto 1).eventually (ge_mem_nhds ?_); change G.chord (faceValue (1:Config G n) a)<_; simpa only [WilsonStartup.face_one,Gauge.chord_one] using p
 filter_upwards [eventually_all.mpr he] with i t; ext x; rw [flags_spec]; simp [not_lt_of_ge,t] -- tune le
end YM.CF.Nova
