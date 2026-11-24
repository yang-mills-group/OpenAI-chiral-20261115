import YM.SU5.FiniteGaugeData.Crest.Alps
/-! # Propagation attempt. periodized temporal pulse budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Laplacian
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "ω"=> 2 * Real.pi

def screen := Set.Ioc (-Real.pi) Real.pi
lemma paneM : MeasurableSet screen:=measurableSet_Ioc
abbrev pluse (n:ℤ)(f:ℝ→ℂ) := ∫ t in screen,surge n t*f t
lemma screen_fin : IsFiniteMeasure ((volume:Measure ℝ).restrict screen):= inferInstanceAs (IsFiniteMeasure ((volume:Measure ℝ).restrict (Ioc (-Real.pi) Real.pi)))
attribute [local instance] screen_fin
lemma pluse_integrable {f:ℝ→ℂ}(h: IntegrableOn f screen) (n:ℤ): IntegrableOn (fun t=>surge n t*f t) screen := h.bdd_mul (by unfold surge; fun_prop) (Eventually.of_forall fun i=>(surge_norm ..).le) -- explicit .1?
lemma pluse_add (n:ℤ){f g:ℝ→ℂ}(p:IntegrableOn f screen)(q:IntegrableOn g screen):pluse n (fun t=> f t+g t)=pluse n f+pluse n g:=by
 unfold pluse; simp_rw [mul_add]; exact integral_add (pluse_integrable p n) (pluse_integrable q n)
lemma pluse_const (n:ℤ){f:ℝ→ℂ}(z:ℂ):pluse n (fun t=> z*f t)= z*pluse n f:=by unfold pluse; simp_rw [mul_left_comm (surge _ _)]; rw [integral_const_mul]
lemma pluse_after (n k:ℤ)(f:ℝ→ℂ): pluse n (fun t=> surge k t*f t)=pluse (n+k) f :=by unfold pluse; simp_rw [Int.cast_add,surge_left,mul_assoc]
lemma wrap_surge (n l:ℤ)(t:ℝ): surge n (t+ω*(l:ℝ))=surge n t:=by
 rw [surge_right, show surge (n:ℝ) (ω*l)=Complex.exp (((n*l:ℤ):ℂ)*(2*(Real.pi:ℂ)*Complex.I)) from ?_, Complex.exp_int_mul,Complex.exp_two_pi_mul_I,one_zpow,mul_one]
 unfold surge; congr 1 <;> push_cast <;> ring

def sheetInt (n:ℤ):= Set.Ioc (-Real.pi+ω*n) (Real.pi+ω*n)
lemma adjacent (i:ℤ) : π + ω*(i:ℝ)= -π+ω*((i+1:ℤ):ℝ):=by push_cast; ring
lemma sheet_pair : Pairwise (Disjoint on sheetInt):=by
 intro i j hp
 have he(i j:ℤ)(g:i<j):Disjoint (sheetInt i) (sheetInt j):=by
    refine Set.disjoint_left.mpr (fun x hx hu=> (lt_of_lt_of_le hu.1 hx.2).not_ge ?_)
    rw [adjacent]; gcongr; omega
 rcases lt_or_gt_of_ne hp with h|h; exact he i j h; exact (he j i h).symm
lemma sheet_cover : (⋃ n:ℤ,sheetInt n)=Set.univ:=by
 refine Set.eq_univ_of_forall fun x=>?_
 let w:ℝ:=ω
 have hw:0<w:=by unfold w; positivity
 let n:ℤ:=Int.ceil ((x-π)/w)
 have hi: x≤π+w*n:=by have h0:= (div_le_iff₀ hw).1 (show _ ≤ (n:ℝ) from Int.le_ceil _); linarith
 have hh: (n:ℝ)-1 < (x-π)/w:= by have ht : (n:ℝ) < (x-π)/w+1 := Int.ceil_lt_add_one _; linarith
 have hl:= (lt_div_iff₀ hw).mp hh
 refine Set.mem_iUnion.mpr ⟨n,?_,hi⟩; unfold w at *; linarith

lemma circlePulse (n w:ℤ) (f:ℝ→ℂ) : pluse n (fun t=> f (t+ω*w))= ∫ t in sheetInt w,surge n t*f t:=by
 have hp: (π:ℝ)≥ -π:= by linarith [pi_pos]
 unfold pluse screen sheetInt; calc
    _= (∫ t in -π..π,surge (n:ℝ) (t+ω*w)*f (t+ω*w)):=by rw [intervalIntegral.integral_of_le hp]; simp_rw [wrap_surge]
    _=_:= (intervalIntegral.integral_comp_add_right (fun t:ℝ=>surge n t*f t) _).trans (intervalIntegral.integral_of_le (add_le_add_left hp _)) -- name/sign
lemma timefold (n:ℤ)(f:ℝ→ℂ)(h:Integrable f):HasSum (fun i:ℤ=> pluse n (fun t=> f (t+ω*i))) (integrated f n):=by
 simp_rw [circlePulse]; unfold integrated; nth_rw 1 [← setIntegral_univ (f:=(fun t:ℝ=>surge n t*f t)), ←sheet_cover] -- wrong binder matches setIntegral maybe
 exact hasSum_integral_iUnion (fun i=>measurableSet_Ioc) sheet_pair (surged (n:ℝ) h).integrableOn
end YM.CF.Crest.Sleet
