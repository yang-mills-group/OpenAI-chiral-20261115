import GaugeFieldConstruction.KeurMars
import GaugeFieldConstruction.ChamonixMars
import GaugeFieldConstruction.CopterMars
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
local notation "Q"=>TerraMars p Y
-- ∫ F test append identity
lemma CapPumpMars (v:Fin (n+1)→ΧiMars)(b:Bulb)(k:Fin n)(x:Points n)(h: BreatherMars b k x)(i a:Axis)(l:List (Points n)) :
 PoolDMars l (RyeMars (Q v) (Payroll.ticket i) b a i) x=∫ y:E4, (LED b a).f y • (PoolDMars (trailMars l) (Q v) (Points.cons y x)):=by
 refine (CordDMars _ _ _ h a i (Q v) (TerraSm p Y v) l).trans ?_; unfold WrapMars; simp_rw [coatMars]
lemma costPumpMars (v :Fin (n+1)→ΧiMars)(k:Fin n)(a i:Axis)(w:List (Points n))(h:CaporMars (PoolDMars (trailMars w) (TerraMars p Y v))):
    ∃ C:ℝ,∃ m:ℕ,0≤C ∧ ∀ r:ℝ,∀ hr:0<r,r ≤ 1 → ∀ x:Points n, spaced r x → ‖PoolDMars w (RyeMars (Q v) (Payroll.ticket i) (leafMars (x k) r hr) a i) x‖≤ C*r⁻¹^m :=by
 obtain ⟨A,m,e₁,H⟩:=h
 have hτ:=thinMars_pos; let τ:=ThinMars
 let u':=LeafC a*A*τ⁻¹^m
 refine ⟨u',m+1,mul_nonneg (mul_nonneg (Leaf_posMars _) e₁) (pow_nonneg (inv_nonneg.mpr hτ.le) _),fun r hr hev x g=>?_⟩
 let b:=leafMars (x k) r hr; let U:=(LED b a).f; let C:= A*(τ*r)⁻¹^m; let h:=ThemeMars r hr x g k
 have hC:0≤C:= mul_nonneg e₁ (pow_nonneg (inv_nonneg.mpr (mul_nonneg hτ.le hr.le)) m)
 have bI:Integrable U:= (LED b a).d.continuous.integrable_of_hasCompactSupport (LED b a).c
 rw [CapPumpMars p Y v b k x h]
 refine le_trans (b:= ∫ y:E4,‖U y‖*C) (norm_integral_le_of_norm_le (bI.norm.mul_const _) (Eventually.of_forall (fun y=>?_))) ?_
 · change ‖U y • _‖≤ _; rw[norm_smul]; by_cases c : y∈ run (LED b a)
   · have hp:=H (ThinMars*r) (mul_pos hτ hr) (by apply (mul_le_of_le_one_left hr.le (ThinMars_limit.trans (show (1:ℝ)/8 ≤ 1 by norm_num))).trans hev) (Points.cons y x) (theme_addMars r hr x g k y (cone _ _ c))
     exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)
   rw [show U y=0 from image_eq_zero_of_notMem_tsupport c];simp
 rw [integral_mul_const]; refine (mul_le_mul_of_nonneg_right (LeafMintMars r hr hev _ a) hC).trans (le_of_eq ?_); unfold C u'; rw[mul_inv_rev,mul_pow]; ring
-- replace actual to smooth extension global base estimate
lemma CodedNearMars (r:ℝ)(x:Points n)(h:spaced r x)(s:ℝ)(v:s<r):∀ᶠ y in 𝓝 x,spaced s y:=by
 rw [show (fun y:Points n=>spaced s y)=(fun y=>∀i j,i ≠ j → s ≤ cubedist (y i) (y j)) from rfl]; refine eventually_all.mpr fun i=>eventually_all.mpr (fun j=>?_)
 by_cases p:i=j
 · exact Eventually.of_forall fun _ e=>(e p).elim
 have hv:s<cubedist (x i) (x j):= v.trans_le (h _ _ p)
 have he:IsOpen {y:Points n|s<cubedist (y i) (y j)}:=isOpen_lt continuous_const (continuous_cubedist.comp (show Continuous fun y:Points n=>(y i,y j) from by fun_prop))
 exact (he.eventually_mem (show x∈_ from hv)).mono fun i hi _=> (show s<_ from hi).le
lemma seedPepMars (h: CaporMars (WallMars Y F)):CaporMars (Q F):=by
 obtain ⟨A,m,ht,H⟩:=h; refine ⟨A*2^m,m,mul_nonneg ht (by positivity),fun r hr hc x hx=>?_⟩
 obtain ⟨g,hg,hx'⟩:=mem_closure_iff_seq_limit.mp (Dash.full n x)
 change ∀ k:ℕ,g k∈generic n at hg
 apply le_of_tendsto (((TerraAt p Y F x (spaced_conf hr hx)).continuousAt.norm).tendsto.comp hx')
 filter_upwards[hx'.eventually (CodedNearMars r x hx (r/2) (by linarith))] with i hi; change ‖Q F (g i)‖ ≤ _
 rw [TerraWide p Y F (hg i)]; refine (H (r/2) (by linarith) (by linarith) _ hi).trans (Eq.le ?_)
 rw [show (r/2)⁻¹ = 2*r⁻¹ from by ring,mul_pow,mul_assoc] -- tune atom ring
abbrev PaceMars (l:List (CurlMars n)):=l.map FingerMars
def cutFingerMars (i:CurlMars n):CurlMars (n+1):= (i.1.succ,i.2)
lemma PinTrailMars (l:List (CurlMars n)):trailMars (PaceMars l)=PaceMars (l.map cutFingerMars):=by
 induction l with
 | nil => rfl
 | cons a v hv=>
    simp only[trailMars,PaceMars,List.map_cons]; unfold trailMars PaceMars at hv; rw [hv]; congr 1; apply PiLp.ext; intro p; refine Fin.cases ?_ (fun j=>?_) p <;> simp [cutFingerMars, FingerMars,direction,PiLp.single_apply,Points.cons,Pi.single_apply,eq_comm] -- tune
variable (hCap:∀ (n:ℕ)(F:Fin n→ΧiMars),CaporMars (WallMars Y F))
include hCap
lemma CeilingCapsMars(m:ℕ)(w:List (CurlMars n))(e:w.length=m):CaporMars (PoolDMars (PaceMars w) (Q F)):=by
 induction m generalizing n with
 | zero=> rw[List.length_eq_zero_iff.mp e]; exact seedPepMars p Y F (hCap ..)
 | succ m ih=>
    induction w using List.reverseRecOn with
    | nil => simp at e
    | append_singleton v i ih'=>
       clear ih'; simp only[List.length_append,List.length_singleton] at e
       obtain ⟨i,j⟩:=i
       simp only [PaceMars,List.map_append,List.map_cons,List.map_nil,pool_appendMars,poolHeadMars]
       let W:=PaceMars v
       let X:=fun a:Axis=>Fathom.add (p.J a j) F
       have ho a: CaporMars (PoolDMars (trailMars W) (Q (X a))):=by
          unfold W; rw [PinTrailMars]; exact ih _ _ (by simp; omega)
       choose A t hA Hp using fun a=> costPumpMars p Y (X a) i a j W (ho a)
       let K:=Finset.univ.sup t
       refine ⟨∑ a,A a,K,Finset.sum_nonneg (fun i _=>hA i), fun r hr hev x g=>?_⟩
       change ‖PoolDMars W (Analysis.D (direction i j) (Q F)) x‖≤_
       let b:=leafMars (x i) r hr; let S: Set (Points n):= {x|BreatherMars b i x}; let U a := RyeMars (Q (X a)) (Payroll.ticket j) b a j
       have he:IsOpen S:=BreathingMars ..; have hv: x∈ S:=ThemeMars r hr x g i
       have ht:D (direction i j) (Q F)=ᶠ[𝓝 x] (fun x=>∑ a:Axis,U a x):= (he.eventually_mem hv).mono (fun u h=>EnrobeMars p Y i F u b h j)
       rw [show PoolDMars W _ x=PoolDMars W (fun x=>∑ a:Axis,U a x) x from (pool_germMars _ _ _ _ ht).self_of_nhds, pool_sumMars W _ U _ he (fun a _=>PodDPMars (Q (X a)) (TerraSm p Y (X a)) b i a j _) x hv]
       apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; exact Finset.sum_le_sum (fun u h=> (Hp u r hr hev x g).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hev) (Finset.le_sup (f:=t) h)) (hA u))) -- TerraSm args tune
lemma volumeCapsMars (l:List (CurlMars n))(m:ℕ):CaporMars (iteratedFDeriv ℝ m (PoolDMars (PaceMars l) (Q F))) :=by
 refine frameCapMars _ (fun i=>?_)
 let v:=List.ofFn i
 obtain ⟨A,t,hA,H⟩:= CeilingCapsMars p Y F hCap _ (v++l) rfl
 refine ⟨A,t,hA, fun r u U x h=>?_⟩
 have he : ContDiffOn ℝ ∞ (PoolDMars (PaceMars l) (Q F)) (conf n):= fun x hx=> (poolSmMars _ _ _ (TerraAt _ _ F x hx)).contDiffWithinAt
 have hi : v.map FingerMars=List.ofFn (FingerMars ∘ i) := List.map_ofFn ..
 refine le_trans ?_ (H r u U x h); unfold PaceMars; rw[List.map_append,pool_appendMars,hi]; exact le_of_eq (congr_arg norm (pool_payMars _ _ _ (conf_open _) he _ (spaced_conf u h)).symm)
#print axioms CeilingCapsMars
#print axioms volumeCapsMars
end YM.GaugeFieldConstruction.Ember.Volumetric
