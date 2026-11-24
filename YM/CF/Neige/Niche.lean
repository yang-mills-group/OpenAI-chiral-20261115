import YM.CF.Neige.Brick
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
abbrev Shelf (α:Type):= Matrix α α ℝ
def punt (A:Shelf α):Shelf α:= (1/2:ℝ) • -A+(3/8:ℝ) • A^2
def port (A:Shelf α):= 1+ punt A
def relic(A:Shelf α):= port A*(1+A)*port A-1
lemma punt_sym {A:Shelf α}(h:A.IsSymm): (punt A).IsSymm:=by unfold punt; exact Matrix.IsSymm.add (h.neg.smul _) ((h.pow 2).smul _)
lemma plat {A:Shelf α}(h:A.IsSymm): (port A).IsSymm:=by unfold port; exact (show (1:Shelf α).IsSymm from Matrix.isSymm_one).add (punt_sym h)
lemma report (A:Shelf α): relic A=(5/8:ℝ) • A^3 + (-15/64:ℝ) • A^4+(9/64:ℝ) • A^5:=by
 unfold relic port punt
 simp only [Matrix.add_mul,Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,Matrix.smul_mul, Matrix.mul_smul,Matrix.neg_mul,Matrix.mul_neg]
 rw [← show A^2=A*A from pow_two _,show A^2*A=A^3 from rfl,show A*A^2=A^3 from (pow_succ' A 2).symm,show A^3*A=A^4 from (pow_succ A 3).symm, show A^2*A^2=A^4 from (pow_add A 2 2).symm,show A^3*A^2=A^5 from (pow_add A 3 2).symm]; ext i j; simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.neg_apply,smul_eq_mul]; ring
abbrev Protected (k:ℕ) (A:E→ Shelf α)(x:E)(t:ℝ):= Allows k (fun y=>paintO (A y)) x t
variable {A B X:E→Shelf α}{x₀:E}
lemma fuseN (h:Protected n A x₀ C)(hp:Protected n B x₀ K): Protected n (fun y=> A y*B y) x₀ (2^n*C*K):=by
 apply (fiction h hp).germ; exact Eventually.of_forall fun y=> (paint_mul ..).symm
lemma attach (h:Protected n A x₀ C)(hp:Protected n B x₀ K):Protected n (fun y=> A y+B y) x₀ (C+K):=(h.add hp).germ (Eventually.of_forall fun y=> (map_add paintO _ _).symm)
lemma subsid (h:Protected n A x₀ C)(hp:Protected n B x₀ K):Protected n (fun y=>A y-B y) x₀ (C+K):= (subtract_p h hp).germ (Eventually.of_forall fun y=> (map_sub paintO _ _).symm)
lemma climb (h:Protected n A x₀ C)(k:ℕ): Protected n (fun y=> A y^k) x₀ ((2^n*C)^k):=by induction k with
 | zero=> simp only [pow_zero]; exact allows_const _ (by rw [paint_one]; exact ContinuousLinearMap.norm_id_le)
 | succ i ih=> exact (((fuseN ih h).mono (le_of_eq (by rw [pow_succ]; ring))).germ (Eventually.of_forall fun y=> by simp only [pow_succ])) -- tune type inference
lemma wrap_r (h:Protected n A x₀ C)(s:ℝ):Protected n (fun y=> s • A y) x₀ (|s| * C):=(h.smul s).germ (Eventually.of_forall fun y=> (map_smul paintO _ _).symm)
lemma low_invP (A:Shelf α)(h: ‖paintO (τ:=α) (A-1)‖≤1/2):IsUnit A.det ∧ ‖paintO (τ:=α) A⁻¹‖≤2:=by
 let P:=paintO (A-1); have he(v: Fish α):‖v‖≤2*‖paintO A v‖:=by
    have hp : v=paintO A v - P v:= by unfold P; rw [map_sub,_root_.sub_apply,paint_one]; exact (sub_sub_cancel ..).symm
    have ht := norm_sub_le (paintO A v) (P v); rw [← hp] at ht
    linarith only [ht,(P.le_opNorm v).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))]
 have hA : IsUnit A:= Matrix.mulVec_injective_iff_isUnit.mp (fun i j hh=>by
    apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; apply (he (i-j)).trans; rw [map_sub,show paintO A i=paintO A j from hh,sub_self,norm_zero,mul_zero])
 have ht: IsUnit A.det:= (Matrix.isUnit_iff_isUnit_det ..).mp hA
 refine ⟨ht,ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v=>?_⟩
 apply (he _).trans_eq; rw [show paintO A (paintO A⁻¹ v)=v from ?_]; rw [← ContinuousLinearMap.comp_apply,← paint_mul, Matrix.mul_nonsing_inv _ ht, paint_one]; rfl
end YM.CF.Neige
