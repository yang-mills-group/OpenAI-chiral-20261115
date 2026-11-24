import GaugeFieldConstruction.CottonLimeL
import GaugeFieldConstruction.StyriaRel.YM.Work.C23
import GaugeFieldConstruction.StyriaRel.YM.Work.C22
import GaugeFieldConstruction.StyriaRel.YM.Heat.Duration
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Boundary.Ferry
open YM.Boundary Work Work.C15
open Function MeasureTheory Filter Set Distribution Probe Complex Spectral
open scoped Topology InnerProductSpace Classical ContDiff NNReal ENNReal ComplexOrder
variable {G:Gauge}{L:Register G}{S T:Table L}{n:ℕ}
variable {C:LRoom T timeAxis}
-- every positive cluster covered by ample plane profiles. cone statement on the ACTUAL Gram.
lemma cone_shine {W:Surface S}{F: Waves S}{J:StarOp S}(d:F.during W)(h:Bid.cones W)(r:F.Region T)(p:F.Breathes)(b:F.Bounds)(B:Small S C)(U:Bid.Hull B F J)(v:Fin n→S.Union)(t:ℝ≥0)(x:Heights n)(a:Small.ample t x)(q:Points n): C.flow.ℚmeasure.region Mink.coneᶜ (B.shot t n v x q)=0 :=by
 have ht:=Work.C22.ample_room a
 have he:=Work.C22.roomPositive ht
 apply (C.flow.unit.suffices_tests _ C.flow.joint _ Mink.closed_cone _).mpr; intro f hf hw
 simp_rw [←C23.shot_shift B t n v x q _ a,U.join n n v v t t x x he he a a]
 have hp(s:E4):Bid.bothP q (q+points (fun _=>s))=Bid.bothP q q+skirt n s:=by
    ext1 i; refine Fin.addCases (fun i=>?_) (fun i=>?_) i
    · simp [Bid.bothP]
    · simp only [Bid.bothP, PiLp.add_apply, points_apply, Fin.append_right]; simp
 simp_rw [hp]; exact ferry_free d h r p b _ _ (C22.eastBoth ht ht) _ f hw _
variable {H:Hilbert}
open OS OS.Semigroup
variable (D:OS.Semigroup H timeAxis)
local notation "Τ" x:max=> D.ℚmeasure.diagonal x
lemma fern_damps (x:H)(q:ℝ≥0)(h:D.ℚmeasure.region Mink.coneᶜ x=0): D.ℚmeasure.region Mink.coneᶜ (D.E q x)=0:=by
 apply (D.ℚmeasure.null_pair Mink.closed_cone.isOpen_compl.measurableSet _).1; rw[D.damp]
 exact MeasureTheory.withDensity_absolutelyContinuous _ _ ((D.ℚmeasure.null_pair Mink.closed_cone.isOpen_compl.measurableSet _).2 h)
lemma fern_ground (x:H)(h:D.ℚmeasure.region Mink.coneᶜ x=0):D.ℚmeasure.region Mink.coneᶜ (D.orth x)=0:= tendsto_nhds_unique ((D.ℚmeasure.region _).continuous.continuousAt.tendsto.comp (D.emerges x)) (tendsto_const_nhds.congr' (Eventually.of_forall (fun i=>(fern_damps D x i h).symm)))
lemma fern_time (x:H)(h:x∈D.ground): ∀ᵐ y ∂(Τ x), YM.time y=0 :=by
 have hh₀:= D.heat 0 x (z:=0) (show _ by simp [Paley.high]); have hh:= D.heat 0 x (z:=Complex.I) (show _ by simp [Paley.high])
 have he: D.J 0 x x Complex.I= D.J 0 x x 0:=by simp [OS.Semigroup.J,OS.Semigroup.ray,(D.fixed _).mp h]
 rw [hh,hh₀] at he
 simp only [Probe.plane_zero,one_mul,mul_assoc,I_mul_I, mul_neg, mul_one,mul_zero, ←Complex.ofReal_neg, ←Complex.ofReal_exp] at he
 let F(y:E4):= Real.exp (-YM.time y)
 have ht : Integrable F (Τ x):=by
    apply (integrable_const (μ:=(Τ x)) (1:ℝ)).mono (show Continuous F by unfold F; fun_prop).aestronglyMeasurable
    filter_upwards [D.bright x] with i hi; change ‖Real.exp (-YM.time i)‖≤ ‖(1:ℝ)‖; simp [time,hi]
 have H: ∀ᵐ y ∂(Τ x), 0 ≤ 1-F y:= (D.bright x).mono fun i hi=> by simp [F,time,hi,sub_nonneg]
 have z:(fun y=>1-F y)=ᵐ[(Τ x)] (0 : E4→ℝ):=by
    apply (integral_eq_zero_iff_of_nonneg_ae H ((integrable_const (1:ℝ)).sub ht)).1
    rw [integral_sub (integrable_const _) ht]
    apply sub_eq_zero.2
    apply Complex.ofReal_injective; rw [←integral_complex_ofReal,←integral_complex_ofReal]; simpa [YM.time,F] using he.symm
 filter_upwards [z] with i hi; exact neg_eq_zero.mp (Real.exp_injective ((sub_eq_zero.mp (show 1-F i=0 from hi)).symm.trans Real.exp_zero.symm))
lemma seeds_free (x:H)(g:D.ℚmeasure.region Mink.coneᶜ x=0)(v:E4): D.unit.translation v (D.orth x)=D.orth x:=by
 let y:=D.orth x; set u:=D.unit.translation v y
 have he:∀ᵐ p ∂(Τ y), p = 0:=by
    have hp:∀ᵐ p ∂(Τ y), p ∈ Mink.cone:= ae_iff.mpr ((D.ℚmeasure.null_pair Mink.closed_cone.isOpen_compl.measurableSet _).mpr (fern_ground D x g))
    filter_upwards [hp,fern_time D y (Submodule.starProjection_apply_mem _ _)] with p hp hw
    apply Mink.ext_by
    · apply norm_eq_zero.mp _ |>.trans (map_zero Mink.restL).symm
      exact le_antisymm (hp.trans hw.le) (norm_nonneg _)
    rw [hw,Mink.clock_zero]
 have ht:inner ℂ y u=inner ℂ y y :=by
    calc
       _ = charFun (Τ y) v := (D.joint y v).symm
       _ = charFun (Τ y) 0:=by rw[charFun_apply,charFun_apply]; refine integral_congr_ae ?_; filter_upwards [he] with p hp; rw[hp]; simp
       _ = _ :=by rw [D.joint,D.unit.origin]; rfl
 apply (dist_eq_zero).1
 change dist u y=0
 rw [dist_comm]; apply eq_zero_of_pow_eq_zero (n:=2); rw [dist_eq_norm,norm_sub_sq (𝕜:=ℂ),ht,inner_self_eq_norm_sq,D.unit.unitary]; ring
#print axioms cone_shine
#print axioms seeds_free
end YM.NSF.Boundary.Ferry
end
