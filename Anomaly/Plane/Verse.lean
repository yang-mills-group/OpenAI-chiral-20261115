import YM.SU5.Circuit.Quartet
/-!
Adapter for moving pairing with vectors uniform in the receipt; orientation
reflected payer uses same W. Separate capital for clipped grains.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Regis.Head.Brecht.Pier
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] {ι:Type*} [Fintype ι] (x y z w:E) {k:ℝ}
local notation "μ" =>stdGaussian E
abbrev A(x:E)(v:E):ℝ:= inner ℝ x v
abbrev mats (x y:E)(v:E):ℝ:= A x v*A y v
lemma mats_bold (x y:E): MemLp (mats x y) 2 μ:=by
 rw [show mats x y = (1/4:ℝ) • ((mats (x+y) (x+y))-(mats (x-y) (x-y))) from ?_]; swap; · funext; simp only [mats,Pi.smul_apply,Pi.sub_apply,A,inner_add_left,inner_sub_left,smul_eq_mul]; ring
 have hp(x:E): MemLp (mats x x) 2 μ:=by simpa only [mats,A,pow_two] using coats x 2
 exact (((hp _).sub (hp _)).const_smul _)
local notation "Φ" x:max y:max z:max w:max =>(mats_bold x y).integrable_mul (mats_bold z w)
abbrev pairing:= ∫ v,mats x y v * mats z w v∂μ
lemma double_plus (v:E): pairing (x+y) v z w=pairing x v z w+pairing y v z w:=by
 let P(x v':E):=mats x v v'*mats z w v'; unfold pairing; change ∫ i,P _ i∂μ=_; have he(i:E):P (x+y) i=P x i+P y i:=by unfold P mats A; rw [inner_add_left]; ring
 simp_rw [he]; exact integral_add (Φ x v z w) (Φ y v z w) -- tune lhs defeq P? lhs form integral_add elaborates from Φ w implicit uses V ?_
lemma dualize: pairing x y z w=pairing z w x y:=by unfold pairing; apply integral_congr_ae; exact Eventually.of_forall fun i=> mul_comm ..
lemma across: pairing x y z w= pairing y x z w:=by unfold pairing; apply integral_congr_ae; refine Eventually.of_forall fun i=>congrArg (· *_) (mul_comm ..)
lemma gear:pairing x x z z=A x x*A z z+2*(A x z)^2:=by unfold pairing mats A; simp_rw [←pow_two,duet,real_inner_self_eq_norm_sq]
lemma roam:pairing x y z z=A x y*A z z+2*A x z*A y z:=by
 have he:= gear (x+y) z; unfold A at he ⊢
 rw [double_plus,_root_.YM.Regis.Head.Brecht.Pier.across x, double_plus, across y (x+y),double_plus,across y x,gear,gear] at he
 simp_rw [inner_add_left,inner_add_right,real_inner_comm x y,A] at he; linarith only [he]
lemma canticle:pairing x y z w=A x y*A z w+A x z*A y w+A x w*A y z:=by
 have he:= roam x y (z+w); rw [dualize,double_plus,across z,double_plus,across w (z+w),double_plus,across w z,dualize z z, dualize w w, dualize z w,roam,roam] at he
 simp_rw [A,inner_add_left,inner_add_right,real_inner_comm z w] at he; unfold A; linarith only [he]
end YM.Regis.Head.Brecht.Pier
