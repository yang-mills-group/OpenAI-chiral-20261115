import YM.SU5.FiniteGaugeData.Hierarchy.Folio
/-! # ReadCLM dictionary. Still the actual signed ratio. Level s cost constants
uniform in period at the tail (`Satin.library`), not in s.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S
local notation "Zᵣ" i:max k:max s:max => partitionZ (Tᵣ i k s) Λ.U (Wₐ i s)
local notation "ν" => (side Y i s)
local notation "M" => (Tᵣ i k s)
local notation "Z" => (Wₐ i s)
local notation "Σ₀"=>sharp Y h s

abbrev MarkGate (s i k:ℕ):Prop:=(Y.voyage i).kick≤ k ∧ s≤Y.uv k

variable (p:MarkGate Y s i k)
lemma markGate_o (p:Offered Y S s i k): MarkGate Y s i k ∧ MarkGate Y (s+1) i k:=⟨⟨p.calendar,p.age.le⟩,p.calendar,p.age⟩
include p in
lemma vac_valid : (Zᵣ i k s) ≠ 0 := (Y.each_level i k s p.1 p.2).valid

include p in
lemma mark_legit (f:Catalog S) : Integrable (fun x=> letterRead (((sold Y h s i) (composeQ Kₜ S f)) (drawn (Wₐ i s) x)) (denZ (Tᵣ i k s) Λ.U (Wₐ i s) x)) (city ν) := mark_integrable ((Y.voyage i).ownership s).paid.bill (sold_affair Y h S s i (compose_t S Kₜ f)).env (Marks.can_read _ _ _ _ (Y.each_level i k s p.1 p.2))
include p in
def meterRead : Catalog S →ₗ[ℂ] ℂ where
  toFun f := (Σ₀) i k (composeQ Kₜ S f)
  map_add' x y := by
    simp_rw [map_add,sold_sharp,map_add]; unfold Journey.compass; rw [mark_add _ _ _ (Marks.can_read _ _ _ _ (Y.each_level i k s p.1 p.2)),add_div]
    · exact ((Y.voyage i).ownership s).paid.bill
    · exact (sold_affair Y h S s i (compose_t S Kₜ _)).env
    exact (sold_affair Y h S s i (compose_t S Kₜ _)).env
  map_smul' a x := by rw [map_smul,RingHom.id_apply,smul_eq_mul]; simp_rw [sold_sharp,map_smul]; unfold Journey.compass; rw [mark_smul,mul_div_assoc]
private lemma bigger : ∃ X:ℝ,∀ f:Catalog S, ‖meterRead Y h S s i k p f‖ ≤ X*‖f‖:=by
  let h:= Y.each_level i k s p.1 p.2 -- shadow
  let n:= sites (N₁ i s)
  refine ⟨Real.exp (Y.debt s*n) * duration S,fun f=>?_⟩
  change ‖sharp Y _ s i k _‖ ≤ _
  rw [sold_sharp]; change ‖Marks.ratio Λ.V Λ.U M Z (fun x=> sold Y _ s i (composeQ _ S f) (drawn (Wₐ i s) x))‖ ≤ _
  apply le_trans (Marks.upper (b:=Y.debt s) _ _ _ _ _ h (fun t=> sold_q_bound Y _ S s i f _)) (le_of_eq (by unfold n; ring))

def MeterRead := (meterRead Y h S s i k p).mkContinuous (Classical.choose (bigger Y h S s i k p)) (Classical.choose_spec (bigger Y h S s i k p))
open scoped Classical
def mkForm : Catalog S →L[ℂ] ℂ := if p:MarkGate Y s i k then MeterRead Y h S s i k p else 0

include p
lemma mk_read (f:Catalog S) : mkForm Y h S s i k f=sharp Y h s i k (composeQ Kₜ S f) := by rw [mkForm,dif_pos p]; rfl

omit p
-- includes off-bill (`0`) cases without identification
lemma bounded : ∃ X:ℝ,0≤X∧∀ᶠ k:ℕ in atTop, ∀ i, ‖mkForm Y h S s i k‖ ≤ X:=by
  obtain ⟨A,x,u⟩:= Satin.library Y h S s; let C:=A*duration S; refine ⟨C,mul_nonneg x.le (duration_pos S).le, u.mono fun k p i=>?_⟩; apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg x.le (duration_pos S).le); intro f
  by_cases g:MarkGate Y s i k; swap; · rw [mkForm,dif_neg g]; change ‖(0:ℂ)‖ ≤ _; rw [norm_zero]; exact mul_nonneg (mul_nonneg x.le (duration_pos S).le) (norm_nonneg _)
  rw [mk_read Y h S s i k g,sold_sharp,mul_assoc]; exact p i g.1 _ (sold_affair Y h S s i (compose_t S Kₜ f)) _ (sold_q_bound Y h S s i f)

def readCost : ℝ:= (bounded Y h S s).choose -- def section variables from return type? include
lemma readCost_nn : 0≤ readCost Y h S s:= (bounded Y h S s).choose_spec.1
lemma reads_within : ∀ᶠ k:ℕ in atTop,∀ i, ‖mkForm Y h S s i k‖ ≤ readCost Y h S s:= (bounded Y h S s).choose_spec.2

variable {x y:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}(V:Universal Y h x y I E)
include V
lemma gate_often :∀ᶠ k:ℕ in atTop, MarkGate Y s i (y k):= ((V.pick.grow_k.tendsto_atTop.eventually_ge_atTop _) |>.and ((Y.uv_grows.comp V.pick.grow_k).tendsto_atTop.eventually_ge_atTop s))

lemma internal_eq (f: Family Kₜ) (p:TestFamily Kₜ true f) : V.pick.field Y h s f i= I s f i := tendsto_nhds_unique ((V.pick.booked Y h s p).2.inner i) ((V.together s f p).inner i)
lemma mood_eq (f:Family Kₜ)(p:TestFamily Kₜ true f) : V.pick.audience Y h s f = E s f := tendsto_nhds_unique_of_eventuallyEq (V.pick.booked Y h s p).2.periods (V.together s f p).periods (Eventually.of_forall fun i=> internal_eq Y h s (x i) V f p)

omit V in
lemma compose_test (K:Calibration)(S:Finset Cover)(f:Catalog S): TestFamily K true (composeQ K S f) := ⟨⟨_,compose_t S K f⟩,fun _=>by contradiction⟩

def vowel : Catalog S →ₗ[ℂ] ℂ where
  toFun f:= I s (composeQ Kₜ S f) i
  map_add' f g := by rw [map_add,← internal_eq Y h s i V _ ((compose_test Kₜ S f).add (compose_test Kₜ S g)), V.pick.field_add Y h s (compose_test Kₜ S f) (compose_test Kₜ S g), Pi.add_apply, internal_eq Y h s i V _ (compose_test Kₜ S f),internal_eq Y h s i V _ (compose_test Kₜ S g)]
  map_smul' a f := by rw [RingHom.id_apply,map_smul,← internal_eq Y h s i V _ ((compose_test Kₜ S f).scale a), V.pick.field_smul Y h s a (compose_test Kₜ S f), Pi.smul_apply, internal_eq Y h s i V _ (compose_test Kₜ S f)]

def tune : Catalog S →ₗ[ℂ] ℂ where
  toFun f:= E s (composeQ Kₜ S f)
  map_add' f g := by rw [map_add,← mood_eq Y h s V _ ((compose_test Kₜ S f).add (compose_test Kₜ S g)),V.pick.addA Y h s (compose_test Kₜ S f) (compose_test Kₜ S g),mood_eq Y h s V _ (compose_test Kₜ S f),mood_eq Y h s V _ (compose_test Kₜ S g)]
  map_smul' a f := by rw [RingHom.id_apply,map_smul,← mood_eq Y h s V _ ((compose_test Kₜ S f).scale a),V.pick.smulA Y h s _ (compose_test Kₜ S f),mood_eq Y h s V _ (compose_test Kₜ S f),smul_eq_mul]

lemma inner_lim (f:Catalog S) : Tendsto (fun k=>mkForm Y h S s i (y k) f) atTop (𝓝 (vowel Y h S s i V f)) := ((V.together s _ (compose_test Kₜ S f)).inner i).congr' ((gate_often Y h s i V).mono fun _ t=> (mk_read Y h S s i _ t f).symm)
lemma ir_lim (f:Catalog S) : Tendsto (fun i=> vowel Y h S s (x i) V f) atTop (𝓝 (tune Y h S s V f)):= (V.together s _ (compose_test Kₜ S f)).periods

lemma path_lim (k:ℕ→ℕ) (e: eligiblePath Y x y k)(f:Catalog S): Tendsto (fun i=>mkForm Y h S s (x i) (y (k i)) f) atTop (𝓝 (tune Y h S s V f)):= ((V.together s _ (compose_test Kₜ S f)).paths k e).congr' ((eligible_offer Y h S s V k e).mono fun _ p=> (mk_read Y h S s _ _ ⟨p.calendar,p.age.le⟩ f).symm)
lemma income_Q (f:Catalog S): ‖vowel Y h S s i V f‖ ≤ readCost Y h S s* ‖f‖:= le_of_tendsto (inner_lim Y h S s i V f).norm ((V.pick.grow_k.tendsto_atTop.eventually (reads_within Y h S s)).mono fun k p=> (mkForm Y h S s i (y k)).le_of_opNorm_le (p i) _)
lemma income_P (f:Catalog S): ‖tune Y h S s V f‖ ≤ readCost Y h S s* ‖f‖:= le_of_tendsto (ir_lim Y h S s V f).norm (Eventually.of_forall fun i=> income_Q Y h S s (x i) V f)

def urn := (vowel Y h S s i V).mkContinuous (readCost Y h S s) (income_Q Y h S s i V)
def singer := (tune Y h S s V).mkContinuous (readCost Y h S s) (income_P Y h S s V)
lemma income_v : ‖urn Y h S s i V‖ ≤ readCost Y h S s:= LinearMap.mkContinuous_norm_le _ (readCost_nn ..) _
lemma income_w : ‖singer Y h S s V‖ ≤ readCost Y h S s:= LinearMap.mkContinuous_norm_le _ (readCost_nn ..) _
lemma urn_eval (f: Catalog S): urn Y h S s i V f= I s (composeQ Kₜ S f) i:= rfl
lemma singer_eval (f:Catalog S): singer Y h S s V f= E s (composeQ Kₜ S f):=rfl

-- Aim convergences in the local operator norm for early Solvent? boutique states only eventually m, threshold geometry actually Tipping needed next. don't claim all Solvent without reproving.
lemma boutique_urn : ∀ᶠ i:ℕ in atTop,Tendsto (fun k=> mkForm Y h S s i (y k)) atTop (𝓝 (urn Y h S s i V)):=by
  obtain ⟨n,hp⟩:= (roomy_sides S Kₜ).exists
  filter_upwards [(boutique Y h V S s).1] with i p
  refine (Metric.tendsto_nhds («α»:=Catalog S→L[ℂ] ℂ)).mpr fun e u=>?_
  let A:=duration S
  have he:0<A:= duration_pos _; filter_upwards [p (e/2/A) (by positivity),gate_often Y h s i V] with k f a
  rw [dist_eq_norm (mkForm Y h S s i (y k)) (urn Y h S s i V)] -- type hint
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm (show 0≤e/2 by linarith) ?_) (by linarith)
  intro x p
  rw [_root_.sub_apply,mk_read Y h S s i _ a,urn_eval]; exact le_trans (f _ (compose_t S Kₜ x) n (roomy_hosp S hp) A (fun v=> by simpa only [p,mul_one] using compose_price S Kₜ x n v)) (div_mul_cancel₀ _ he.ne').le

lemma boutique_P (e:ℝ)(u:0<e) : ∀ᶠ r:ℕ in atTop,
    ‖urn Y h S s (x r) V-singer Y h S s V‖ ≤ e ∧ ∀ k,legacy Y (x r) (y k) → MarkGate Y s (x r) (y k) ∧ ‖mkForm Y h S s (x r) (y k)-singer Y h S s V‖ ≤ e:=by
  obtain ⟨n,hp⟩:= (roomy_sides S Kₜ).exists
  have he:= duration_pos S; filter_upwards [(boutique Y h V S s).2 (e/duration S) (by positivity), often_offer Y h S s V] with i p t
  have f(z:Catalog S)(P:‖z‖=1):= p (composeQ _ S z) (compose_t S Kₜ z) n (roomy_hosp S hp) (duration S) (fun v=> by simpa only [P,mul_one] using compose_price S Kₜ z n v)
  refine ⟨ContinuousLinearMap.opNorm_le_of_unit_norm u.le (fun z v=>le_trans (f z v).1 (div_mul_cancel₀ _ he.ne').le),fun k a=> ?_⟩
  let y:= (t k a).age.le
  refine ⟨⟨(t k a).calendar,y⟩,ContinuousLinearMap.opNorm_le_of_unit_norm u.le (fun z v=> ?_)⟩; rw [_root_.sub_apply,mk_read _ _ S s _ _ ⟨(t k a).calendar,y⟩]; exact le_trans ((f z v).2 k a) (div_mul_cancel₀ _ he.ne').le
#print axioms urn
#print axioms boutique_P
end YM.CF.Buffered.Afterglow.Hierarchy
