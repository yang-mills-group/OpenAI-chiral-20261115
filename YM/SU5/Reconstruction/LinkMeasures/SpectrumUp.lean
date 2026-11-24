import YM.SU5.Reconstruction.LinkMeasures.AxisSense
import YM.SU5.Reconstruction.PolarArchives.Console
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 680000
set_option synthInstance.maxHeartbeats 60000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satori
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Tapestry
open Tower Tower.SatinVerification PaymentCamera
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    (V:Universal Y H i k I E)(G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (S:Finset Cover)(s:ℕ)(w:Evens S)
local notation "μS" => actual S Λ l
local notation "W" => wingspan Λ l S
local notation "Bx" => PhaseChoice.transfer Y H G S s
local notation "Tx" => singer S w
local notation "rᵢ" i1:max => i (G.rows i1)
local notation "rₖ" i1:max => k (G.columns i1)

open Tower.Vacancy Tower.Selected Tower.FirstWindows PaymentCamera
local notation "q★" => Satori.qty S Λ l
open Tower.FirstWindows.PolarArchives Tower.Tilted Tower.Tilted.Ramp Tower.FirstWindows.WindRose Tower.PhaseChoice
variable (P:Tower.Tilted.Ramp)(gap:ℝ≥0)
/-!
# True root point matrix estimator. No assumption of countably many Swatch values; pointwise program in essential-range sense and REAL pose price. -/
local notation "τ" => Swatch W
local notation "t★" => singleTicket Y H G S s
variable (A:Evens S→ ScoreBook S→ Swatch (wingspan Λ l S))
noncomputable def standRange (S:Finset Cover) (Λ:Preparation) (l:ℕ) (A:Evens S→ ScoreBook S→ Swatch (wingspan Λ l S)) := ⋃ w:Evens S,PaymentCamera.frequents (actual S Λ l) (A w)
-- ask only on the essential point values in next rung's frame, for positive source S.
-- `Submodule.span` is finite combinations
noncomputable def Minuet :Prop:=∀ x∈ Submodule.span ℂ (standRange S Λ l A), 0≤optic Y H V (wingspan Λ l S) (s+1) P x x
noncomputable def Certificates (S:Finset Cover)(s:ℕ)(A:Evens S→ ScoreBook S→ Swatch (wingspan Λ l S)):Prop:= ∀ x:Evens S, Present (actual S Λ l) (singleTicket Y H G S s x) (A x)
variable (p: PhaseChoice.SupportedPhysically Λ l s S (Acres P gap))(u:Certificates Y H G S s A)
-- general closedness w/ complex order from physical receipt itself
omit p u in
lemma optic_closed : IsClosed {x:Swatch S|0≤ optic Y H V S s P x x}:= isClosed_le continuous_const (show Continuous (fun x:Swatch S=> optic Y H V S s P x x) from ((optic_c Y H V S s P).comp (f:=fun x=>(x,x)) (continuous_id.prodMk continuous_id))) -- hb
local notation "L" => optic Y H V W (s+1) P
include p u
lemma swing_point : Minuet Y H V S s P A ↔ ∀ x:Swatch S,0≤ optic Y H V S s P x x :=by
 let Z:= standRange S Λ l A
 constructor
 · intro t x; rw [optic_up Y H V G S s P gap p, transfer_all]; apply closure_minimal (s:= ((Submodule.span ℂ Z):Set τ)) (t:={x:τ| 0≤ L x x}) t (optic_closed Y H V W (s+1) P); apply Submodule.sum_mem (sky Z); intro i z; exact Present.from_span (E:=Swatch W) (actual S Λ l) (singleTicket Y H G S s i) (M:=sky Z) (u i) (Submodule.span ℂ Z).isClosed_topologicalClosure (fun a t=>sky_in Z (Set.mem_iUnion.mpr ⟨i,t⟩)) _
 intro h x hx; let T:Submodule ℂ τ:= (Bx).range
 have hm:T≤ T.topologicalClosure := subset_closure; have hb: ((T.topologicalClosure:Set τ)) ⊆ {x:τ|0≤ L x x}:= by
    refine closure_minimal ?_ (optic_closed Y H V W (s+1) P); rintro _ ⟨x,rfl⟩; change 0≤ L (Bx x) (Bx x); exact (optic_up Y H V G S s P gap p x x) ▸ h x
 apply hb; apply Submodule.span_le.mpr ?_ hx -- may infer
 rintro v k; obtain ⟨i,k'⟩:=Set.mem_iUnion.mp k; refine closure_minimal (t:= (T.topologicalClosure:Set τ)) ?_ (T.isClosed_topologicalClosure) (Present.point_cost (E:=Swatch W) (actual S Λ l) (singleTicket Y H G S s i) (u i) _ k'); rintro _ ⟨x,z,rfl⟩; exact hm ⟨singer S i x,rfl⟩

omit p u
noncomputable def Membrane: Prop:= ∀ (S:Finset Cover)(s:ℕ), PhaseChoice.SupportedPhysically Λ l s S (Acres P gap) →∃ A, Certificates Y H G S s A ∧ Minuet Y H V S s P A
lemma membrane_legal : Membrane Y H V G P gap ↔ Rectitude Y H V G P gap:=by
 rw [←loops_root,←want_iff Y H V G P gap]; constructor
 · intro t S s p; obtain ⟨A,u,h⟩:= t S s p; exact (swing_point Y H V G S s P gap A p u).mp h -- argument order
 intro t S s p; choose A u using fun x:Evens S=> individually_bank Y H V G S s x; have v: Certificates Y H G S s A:=fun i=>(u i).1.publicly; exact ⟨A,v,(swing_point Y H V G S s P gap A p v).mpr (t S s p)⟩
lemma fromRoot_to_all (h:Rectitude Y H V G P gap)(p:PhaseChoice.SupportedPhysically Λ l s S (Acres P gap))(u:Certificates Y H G S s A) : Minuet Y H V S s P A:= (swing_point Y H V G S s P gap A p u).mpr (((want_iff Y H V G P gap).mpr ((loops_root Y H V G P gap).2 h)) _ _ p)

-- Also ask purely via literal-polynomial physical sharp pair in one Wilson frame and real graph.
noncomputable def ExactPaint : Prop:= ∀ (S:Finset Cover) (s:ℕ), PhaseChoice.SupportedPhysically Λ l s S (Acres P gap) →∀ f:Swatch S, f∈ literal S → Neutral K (render S K f) →∀ ε:ℝ,0<ε→∃ᶠ r in atTop,-ε≤ (sharp Y H s (i (G.rows r)) (k (G.columns r)) ((P.cuspF K (render S K f))* render S K f)).re
local notation "Q★" => optic Y H V S s P
lemma optic_real (x:Swatch S): 0 ≤ Q★ x x ↔ 0≤ (Q★ x x).re := by rw [Complex.le_def]; apply and_iff_left_of_imp; intro _; have h:=congrArg Complex.im (optic_mirror Y H V S s P x x); change _= -((Q★ x x).im) at h; change 0 = _; linarith
private lemma erased (f:Swatch S): Tendsto (fun v:ℕ=> (sharp Y H s (i (G.rows v)) (k (G.columns v)) ((P.cuspF K (render S K f))* render S K f)).re) atTop (𝓝 ((optic Y H V S s P f f).re)):=by let T:Dome (tent Y H):= windTilt P K (badge K S f)*badge K S f; exact Complex.continuous_re.continuousAt.tendsto.comp (final_limit Y H G s T.val ((marque ..).1 T.property))
private lemma guide {f:ℕ→ℝ}{x:ℝ} (h:Tendsto f atTop (𝓝 x)): 0≤x ↔ ∀ ε:ℝ,0<ε→ ∃ᶠ r in atTop, -ε ≤ f r:=by
 constructor; exact fun p ε v=> ((h.eventually (lt_mem_nhds (lt_of_lt_of_le (neg_lt_zero.mpr v) p))).mono fun i t=>le_of_lt t).frequently
 intro p; by_contra! he; obtain ⟨t,vv,T⟩:= exists_between he; exact (show ∃ᶠ u in atTop,t≤ f u from by simpa using p (-t) (neg_pos.mpr T)) ((h.eventually (gt_mem_nhds vv)).mono (fun i p=> not_le.mpr p)) -- wrong order
lemma pay_when : ExactPaint Y H G P gap ↔ Rectitude Y H V G P gap:=by
 rw [←loops_root]
 constructor
 · exact fun h S s p x u v=> (optic_real Y H V S s P x).mpr ((guide (erased Y H V G S s P x)).mpr (h S s p x u v))
 exact fun h S s p x u v=> (guide (erased Y H V G S s P x)).mp ((optic_real Y H V S s P x).mp (h S s p x u v))
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.membrane_legal
#print axioms YM.CF.Buffered.Afterglow.Satori.pay_when
