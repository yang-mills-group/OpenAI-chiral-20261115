import GaugeFieldConstruction.TaurineMars
set_option autoImplicit false
set_option synthInstance.maxSize 10050
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff FourierTransform InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S: City} {P:Axis→Across} {L:Sheds S P} {C: Supplies L} {u:ℕ→Carat}
variable (p:Ticket u C) (Y:AreaQc S)
variable {n:ℕ} (k:Fin n) (a:Axis)
variable (F:Fin n→ΧiMars)
lemma LocMars : Dash.Loc (WallMars Y F):= fun y=> BondCostQc _ _ (Y.reg ..)
include p
lemma BurnMars (m:ℕ):Dash.Hidden k a m (WallMars Y F) :=by
 induction m generalizing n with
 | zero => exact Dash.begins _ _ _ (LocMars Y F)
 | succ m ih =>
    intro f
    let kf (f:Test n):Points n→ℂ:=fun x=>f x*WallMars Y F x
    let Q (i:Points n):=Probe.q*|i k a|
    have hQ (i: Points n):0≤ Q i:= mul_nonneg Probe.qpos.le (abs_nonneg _)
    let A(p':Test n):= ∃ C:ℝ,∀ i:Points n, Q i^(m+1)* ‖𝓕 (kf p') i‖ ≤ C
    refine patchMars A ?_ ?_ ?_ f
    · refine ⟨0,fun i=>?_⟩; rw [show kf 0=0 from funext fun x=>show (0:ℂ)*_=0 from zero_mul _, Dash.scanned]; simp -- tune
    · rintro s t ⟨c,w⟩ ⟨l,v⟩; refine ⟨c+l,fun i=>?_⟩
      have T:𝓕 (kf (s+t)) i= 𝓕 (kf s) i + 𝓕 (kf t) i:=by
        rw[show kf (s+t)= kf s+kf t from funext fun x=> add_mul ..]; exact congr_fun (VectorFourier.fourierIntegral_add Real.continuous_fourierChar (by change Continuous fun p : Points n × Points n => inner ℝ p.1 p.2; fun_prop) (LocMars Y F s) (LocMars Y F t)) i
      rw[T]; exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (pow_nonneg (hQ i) _)).trans ((le_of_eq (mul_add ..)).trans (add_le_add (w i) (v i)))
    intro x hx
    obtain ⟨b,hy,hv⟩:= needMars x hx k
    refine ⟨{y|lit b (y k) ∧ ∀ i,i≠k→ y i∉run b},HoursMars x k b hy hv,fun t ht=>?_⟩
    let o : Works b t k:= ⟨fun y h=>(ht h).1,fun y h=>(ht h).2⟩
    let J(i:Points n)(j:Axis):=𝓕 (fun y=> lace t (LED b j) (o.cared j) y* WallMars Y (Fathom.add (p.J j a) F) y) (Points.cons 0 i)
    have pV (j:Axis): ∃ C:ℝ,∀ i, Q i^m * ‖J i j‖≤ C:=by
        obtain ⟨W,hW⟩:= ih k.succ (Fathom.add (p.J j a) F) (lace t (LED b j) (o.cared j)); exact ⟨_, fun i=>hW (Points.cons 0 i)⟩
    choose G hG using pV; obtain ⟨W,hW⟩:= ih k F (Dash.down t k a)
    refine ⟨W+∑ j:Axis,G j,fun i=>?_⟩
    let T:=𝓕 (kf t) i; let c:=𝓕 (kf (Dash.down t k a)) i
    have H: Q i * ‖T‖≤ ‖c‖ + ∑ j:Axis, ‖J i j‖:=by
       have h: (I*↑Probe.q*↑(i k a))*T=c+∑ j:Axis,J i j:= PlasmaMars p Y k a F i t b o
       apply le_trans ?_ ((norm_add_le c _).trans (add_le_add_right (norm_sum_le ..) _)); rw [←h]; unfold Q; simp only[norm_mul,norm_I,norm_real,abs_of_nonneg Probe.qpos.le, Real.norm_eq_abs,one_mul]; exact le_rfl
    unfold T at H; rw[pow_succ,mul_assoc]; refine (mul_le_mul_of_nonneg_left H (pow_nonneg (hQ i) _)).trans ?_; rw[mul_add,Finset.mul_sum]; exact add_le_add (hW _) (Finset.sum_le_sum fun j _=>hG j i)
lemma springMars :∃ g:Points n→ℂ,ContDiffOn ℝ ∞ g (conf n)∧ EqOn g (WallMars Y F) (generic n):= Dash.aggregate (LocMars Y F) (fun v k a => BurnMars p Y k a F v) (fun x hx=> ((Y.reg ..).warm _ hx).continuousWithinAt)
#print axioms springMars
end YM.GaugeFieldConstruction.Ember.Volumetric
