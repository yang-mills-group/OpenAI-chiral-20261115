import YM.SU5.Reconstruction.LinkMeasures.SealGauge
import YM.SU5.Reconstruction.LinkMeasures.MorningRoom
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open _root_.YM.PaymentCamera
/-! # Genuine finite polynomials in matrix entries can pay *singular* probe prices at fixed epoch -/
variable (S:Finset Cover)(Λ:Preparation)(l:ℕ)
local notation "X" => ScoreBook S
local notation "W" => Swatch S
local notation "Φ" => Manifest S
local notation "μs" => actual S Λ l
variable (K: Calibration)
noncomputable def fromManifest : Manifest S →ₗ[ℂ] Listener S where
 toFun f := ⟨f,f.continuous.measurable,‖f‖,f.norm_coe_le_norm⟩
 map_add' f h:=rfl
 map_smul' z f:=rfl
noncomputable def mentor : Manifest S→ₗ[ℂ] Pigment S:= (seatFaith S).toLinearMap.comp (fromManifest S)
lemma mentor_read (f:Manifest S)(x:X): (accession S (mentor S f)).val x=f x:= congrFun (congrArg (fun v:Listener S=> v.val) ((seatFaith S).symm_apply_apply (fromManifest S f))) x
lemma mentor_bill(f:Manifest S): PaymentCamera.seat (actual S Λ l) 1 (accession S (mentor S f))=ContinuousMap.toLp 1 (actual S Λ l) ℂ f := Lp.ext ((( (accession S (mentor S f)).cost μs 1).coeFn_toLp).trans ((show (accession S (mentor S f)).val =ᵐ[μs] (fun x=> f x) from Eventually.of_forall (mentor_read S f)).trans (ContinuousMap.coeFn_toLp (𝕜:=ℂ) μs f).symm))
noncomputable def literalM: Submodule ℂ (Pigment S):= (glancing S).map (mentor S)
noncomputable def literal : Submodule ℂ (Swatch S) := Submodule.pi Set.univ fun _=> literalM S
lemma mentor_const (f: Manifest S): (accession S (mentor S f)).val=(fun x=> f x):= funext (mentor_read S f)
noncomputable def item (i:Evens S): W→ₗ[ℂ] Listener S:=(seatFaith S).symm.toLinearMap.comp (LinearMap.proj i)
lemma item_is(i:Evens S)(f:Swatch S): item S i f=accession S (f i):=rfl
lemma item_clear (i:Evens S)(f:W)(h:f∈ literal S): Continuous (item S i f).val:= by rw [item_is]; obtain ⟨g,t,b⟩:= (show ∃g:Manifest S,g∈glancing S∧ mentor S g=f i from h i (Set.mem_univ _)); rw [←b,mentor_const]; exact g.continuous
lemma frankly (f:Listener S) (e:ℝ)(p:0<e): ∃ a:Pigment S, a∈ literalM S ∧ bill μs (accession S a-f) ≤ e :=by
 let R : Manifest S→L[ℂ] Lp ℂ 1 μs:= ContinuousMap.toLp 1 μs ℂ; let Q:= glancing S
 have h:DenseRange R:= ContinuousMap.toLp_denseRange _ _ _ (by simp)
 have ht:DenseRange (fun x:Q=> R x.val):=h.comp (seal_density S|>.denseRange_val) R.continuous -- name?
 obtain ⟨x,v⟩:= Metric.denseRange_iff.mp ht (PaymentCamera.seat μs 1 f) e p
 refine ⟨mentor S x.val,⟨x.val,x.property,rfl⟩,?_⟩; unfold PaymentCamera.bill; rw [map_sub, mentor_bill,←dist_eq_norm,dist_comm]; exact v.le

noncomputable def sideGauge (i:Evens S): W→L[ℂ] Lp ℂ 1 (actual S Λ l):= by
 let Z:= (PaymentCamera.seat μs 1).comp (item S i); refine Z.mkContinuous ((μs).real Set.univ) fun f=>?_ ; change bill μs (accession S (f i)) ≤ _; rw [bill_eq]; refine (integral_mono ?_ (integrable_const ‖f‖) ?_).trans_eq ?_
 · exact ((Test.finances μs (accession S (f i)))).norm
 · exact fun x=> (daubLe S (f i) (decode S x)).trans (norm_le_pi_norm ..)
 rw [integral_const,smul_eq_mul]
lemma widget(i:Evens S)(f:W): bill μs (accession S (f i))= ‖sideGauge S Λ l i f‖:=rfl
lemma widget'(i:Evens S)(f: W): bill μs (item S i f)= ‖sideGauge S Λ l i f‖:=rfl
noncomputable def qty (f:W):ℝ:= ∑ i:Evens S, PaymentCamera.bill μs (accession S (f i))
local notation "q" => qty S Λ l
lemma element_paid (f:W)(i:Evens S) : bill μs (accession S (f i))≤ q f:= single_le_sum (f:=fun i=> bill μs (accession S (f i))) (fun i _=> bill_nonneg ..) (Finset.mem_univ _) -- f·
lemma stays_nonneg (f:W): 0 ≤ qty S Λ l f:= Finset.sum_nonneg (fun _ _=> bill_nonneg ..)
lemma billable (f:W)(ε:ℝ)(h:0<ε):∃ a:W,a∈ literal S ∧ qty S Λ l (a-f) ≤ ε:=by
 let b:ℝ:=spread S; have hx:0≤b:= Nat.cast_nonneg _; let d:= ε/(b+1); have hd:0<d:=by unfold d; positivity
 choose x u t using fun i:Evens S=> frankly S Λ l (accession S (f i)) d hd
 refine ⟨x,fun i _=> u i,(sum_le_sum (g:=fun _=>d) (fun i _=>?_)).trans ?_⟩
 · rw [Pi.sub_apply,show accession S (x i - f i)=accession S (x i)-accession S (f i) from rfl]; exact t i
 rw [Finset.sum_const,nsmul_eq_mul,card_univ]; change b*d≤ ε; have he:(b+1)*d=ε:=mul_div_cancel₀ ε (by positivity); nlinarith
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.billable
#print axioms YM.CF.Buffered.Afterglow.Satori.widget
