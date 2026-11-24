import GaugeFieldConstruction.Gander
import YM.CF.Tale.Leaf
import YM.CF.Siete.Fiance
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset SU Fock Lat Spire Scroll MeasureTheory Skye Scree Cube RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
open MultiNext.SignedSource Lyre Banjo Analysis Pressure
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n m:Side}{k p j:ℕ}{B:BudgetPoint}{X:Support (More n)}{o:Seat n}{E D F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup D][NormedSpace ℝ D]{C ε r u Q:ℝ}
open Next Next.Fluctuations Precision Tree
variable {S:StepData (More m) (More n)}{T:Tube group S}{Y:Tree.Forest S.ratio}{x t t₁:ℝ}{J:S.Choices}
lemma baton_gap {f:E→ tangD m}{g:E→tangD n}{y:E}{b:E→Prop}(h:Guide E b y f k u)(p:Guide E b y g k t₁)(hh:Tour T Y x J k r C)(ht:temp x ≤ u)(hu:u≤1)(hf:u≤r)(kC:0≤C)  (hy:t₁ ≤u)(hr:2≤k) :
 let Z:=display T Y x J true ∘ fun i=>(f i,g i)
 ContDiffAt ℝ (k:ℕ∞ω) Z y ∧ ∀ i≤k,∀ v:Fin i→E,(∀ j,b (v j))→ ‖iteratedFDeriv ℝ i Z y v-Heir.route T (iteratedFDeriv ℝ i f y v)‖≤clinicFee k C*u^2+t₁:=by
 intro Z; let V(i):=(f i,g i); have hd: Guide E b y V k u:=h.duo (p.rise hy); let F:=display T Y x J true; have hz:=hh.costs true; let Φ:=mainStroke T Y true
 have he: ContDiffAt ℝ (k:ℕ∞ω) Z y:= ((hz.uniform (V y) (hd.size.trans hf)).smooth).comp (f:=V) _ hd.1
 refine ⟨he,fun i hi v hv=>?_⟩
 let w:=iteratedFDeriv ℝ i V y v; let D:=iteratedFDeriv ℝ i Z y v
 let x':=Heir.route T (iteratedFDeriv ℝ i f y v); let Y':=iteratedFDeriv ℝ i g y v
 have hx': ‖D-Φ w‖≤clinicFee k C *u^2:=by
    have hj:=(handle hz ht kC hu hf hd hr).2 i hi v hv; rw [show (display T Y x J true-⇑(mainStroke T Y true)) ∘ V= Z-(Φ∘ V) from rfl, iteratedFDeriv_sub_apply (he.of_le (Nat.cast_le.mpr hi)) ((Φ.contDiff.contDiffAt.comp y hd.1).of_le (Nat.cast_le.mpr hi)), Φ.iteratedFDeriv_comp_left hd.1 (Nat.cast_le.mpr hi)] at hj; exact hj
 have hl: Φ w=x'+Y':=by unfold w V; rw [iteratedFDeriv_prodMk h.1 p.1 (Nat.cast_le.mpr hi)]; rfl
 have h':‖D-x'‖ ≤clinicFee k C*u^2+t₁:=by rw [hl] at hx'; exact (norm_sub_le_norm_sub_add_norm_sub D (x'+Y') x').trans (add_le_add hx' (by rw [add_sub_cancel_left]; exact p.2 i hi v hv))
 exact h'
lemma sphere_pin (o:Seat m)(r:ℕ): sphereQ (1:Pane m) o r 1 =ᶠ[𝓝 0] Tale.curt r o := by
 have h(e:Bond (More m)):∀ᶠ p:tangD m in 𝓝 0,SU.group.plog (SU.group.mat (SU.group.lieExp (p e)))=p e:= ((continuous_apply e).tendsto (0:tangD m)).eventually SU.group.plog_left -- tune
 filter_upwards [eventually_all.mpr h] with v h; ext1 i; rw [Tale.curtP]; simp only [sphereQ,Function.comp_apply,crop,Lattice.gauge,increment,Pi.one_apply,mul_one,one_mul,inv_one]; rw [h i] -- tune
section thick
open YM.FlightFlux CF.TableF CF.TableF.Axon Banjo
variable {a d:ℝ}
lemma StrongE_sack (X:Hub n)(U V:tangD n)(h:0 ≤ d)(v:StrongE B X a d V)(p: ‖U-V‖≤d^4*B.threshold) : StrongE B X (a+1) d U:=by
 obtain ⟨F,H,T⟩:=v; let Y:= fun i:Fin 4=> if i=3 then F i + (U-V) else F i; refine ⟨Y,?_,fun i=>?_⟩
 · unfold Y; rw [Fin.sum_univ_four]; simp only [show ¬((0:Fin 4)=3) from by decide,show ¬((1:Fin 4)=3) from by decide,show ¬((2:Fin 4)=3) from by decide, ↓reduceIte]; rw [H,Fin.sum_univ_four]; abel
 have ht : a*d^(i.val+1) ≤ (a+1)*d^(i.val+1):= by gcongr; linarith -- tune no goals risk
 by_cases u:i=3
 · subst i; refine ⟨ ⟨(T _).1.1.trans ht, fun j=>?_⟩,fun h=>by change 3<3 at h; omega ⟩; simp only [Y,if_true,Pi.add_apply]; apply (norm_add_le ..).trans
   apply (add_le_add ((T _).1.2 j) ((norm_le_pi_norm (U-V) j).trans p)).trans
   let s:ℝ:=Lyre.width B X.val.1 j; have hh:B.threshold ≤ s:= le_mul_of_one_le_right B.threshold_pos.le (one_le_pow₀ (by simp)) -- tune
   change a*d^4*s+ _ ≤ (a+1)*d^4*s; nlinarith only [mul_le_mul_of_nonneg_left hh (pow_nonneg h 4)]
 have hb:=T i; rw [show Y i= F i from if_neg u]; refine ⟨⟨hb.1.1.trans ht,fun j=>?_⟩,fun v=>?_⟩
 · refine (hb.1.2 j).trans (mul_le_mul_of_nonneg_right ht ?_); unfold Lyre.width; have hx:=B.threshold_pos; positivity
 obtain ⟨f,hv,e,u⟩:=hb.2 v; exact ⟨f,⟨hv.1,fun j=>(hv.2 j).trans (mul_le_mul_of_nonneg_right ht B.threshold_pos.le)⟩,e,fun j k=>(u j k).trans (mul_le_mul_of_nonneg_right ht B.threshold_pos.le)⟩
lemma StrongE_mon (X:Hub n)(U:tangD n)(h:0 ≤ d)(v:StrongE B X a d U) (p:a ≤ C) : StrongE B X C d U:=by
 obtain ⟨F,H,T⟩:=v; refine ⟨F,H,fun i=>?_⟩; have ht := mul_le_mul_of_nonneg_right p (pow_nonneg h (i.val+1)); refine ⟨⟨(T i).1.1.trans ht,fun j=>?_⟩,fun v=>?_⟩
 · refine ((T i).1.2 j).trans (mul_le_mul_of_nonneg_right ht ?_); unfold Lyre.width; have hx:=B.threshold_pos; positivity
 obtain ⟨f,hv,e,u⟩:=(T i).2 v; exact ⟨f,⟨hv.1,fun j=>(hv.2 j).trans (mul_le_mul_of_nonneg_right ht B.threshold_pos.le)⟩,e,fun j k=>(u j k).trans (mul_le_mul_of_nonneg_right ht B.threshold_pos.le)⟩
end thick
end YM.CF.Siete
end
