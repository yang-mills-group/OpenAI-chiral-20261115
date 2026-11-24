import YM.SU5.FiniteGaugeData.Concord.Recast
/-!
# Stage limit functionals and consistency

Local boundedness, even uniform convergence in the dual norm relative to the local Palette over
all lower and upper tests, UV for all sufficiently large periods then period and along any
admitted path, with the SAME limits and history. More crucially: the UV and IR
limits *agree with successive observing step limits*. The auxiliary partner and calibration W are
not inputs. This compatibility is for linear readout of a mark through the actual stencil; not
asserting that `issue` is a monomorphism or a homomorphism on overlapping operators (multiplication
or adjoint in some other reconstruction would need PROOF).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s:ℕ) {i k p u v:ℕ→ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K"=> tent Y H
local notation "xCost"=> (local_cost Y H s S).choose
local notation "Ω"=> ConeFilter Y i k
variable (V:Universal Y H i k F E)(W:Traced Y H i k F E P)
section dual
-- only use this clipped workbench when the price gate is paid. In particular the Matinee Price
-- on operators doesn't itself establish this gate. But it holds at every sufficiently high cutoff,
-- uniformly once that row's course bill is paid.
abbrev Music (S:Finset Cover):= Palette S →L[ℂ] ℂ

def Ready (i k:ℕ):Prop:= PairIdx Y s i k ∧ ∀ f:Palette S, ‖sharply Y H i s k S f‖ ≤ (local_cost Y H s S).choose*‖f‖

def critic (i k:ℕ) : Music S:=
  if h:Ready Y H S s i k then
   let z:Palette S→ₗ[ℂ] ℂ:= ⟨⟨sharply Y H i s k S, sharply_add Y H S h.1.1 h.1.2.le⟩,fun a f=>sharply_scale Y H S a f⟩
   z.mkContinuous xCost h.2
  else 0
lemma onPitch {i k:ℕ}(p: Ready Y H S s i k)(x: Palette S): critic Y H S s i k x=sharply Y H i s k S x:=by unfold critic; rw [dif_pos p]; rfl

lemma xcost : 0 ≤ (local_cost Y H s S).choose := (local_cost Y H s S).choose_spec.1
lemma critics (i k:ℕ) : ‖critic Y H S s i k‖ ≤ (local_cost Y H s S).choose:=by
  unfold critic; split; next h=>exact LinearMap.mkContinuous_norm_le _ (xcost ..) _
  exact ContinuousLinearMap.opNorm_zero.trans_le (xcost ..)
local notation "Z"=> critic Y H S s
include V
lemma ready_row (n:ℕ) : ∀ᶠ j in atTop,Ready Y H S s n (k j):=by
  filter_upwards [row_use V.pick s n, V.pick.grow_k.tendsto_atTop.eventually (local_cost Y H s S).choose_spec.2] with j t h using ⟨t,(h n t.1).2⟩
lemma ready_cone : ∀ᶠ t in ConeFilter Y i k,Ready Y H S s (i t.1) (k t.2):=by
  filter_upwards [timely_visit V.pick s, (V.pick.grow_k.tendsto_atTop.comp (ConeFilter.late_right V.pick.grow_i V.pick.grow_k)).eventually (local_cost Y H s S).choose_spec.2] with j t h using ⟨t,(h (i j.1) t.1).2⟩
lemma row_ear (n:ℕ)(f:Palette S) : Tendsto (fun j=> critic Y H S s n (k j) f) atTop (𝓝 (F s (pigment S K f) n)):=
  ((V.together s _ ⟨⟨S,pigment_test ..⟩,fun h=> by contradiction⟩).inner n).congr'
    ((ready_row Y H S s V n).mono fun _ p=> (sharply_s ..).symm.trans (onPitch Y H S s p f).symm)
lemma by_periods (f:Palette S) : Tendsto (F s (pigment S K f) ∘ i) atTop (𝓝 (E s (pigment S K f))) :=
  (V.together s _ ⟨⟨S,pigment_test ..⟩,fun h=> by contradiction⟩).periods
lemma by_path (f:Palette S) : Tendsto (fun t:ℕ × ℕ=> (critic Y H S s (i t.1) (k t.2)) f) (ConeFilter Y i k) (𝓝 (E s (pigment S K f))) := by
  have he:= V.together s (pigment S K f) ⟨⟨S,pigment_test ..⟩,fun h=> by contradiction⟩
  exact Tendsto.congr' ((ready_cone Y H S s V).mono (fun n h=> ((onPitch Y H S s h f).trans (sharply_s ..)).symm))
    ((ConeFilter.tendsto_iff_paths (Y:=Y) (i:=i) V.pick.grow_k (f:=fun t=> sharp Y H s (i t.1) (k t.2) (pigment S K f))).mpr he.paths)
private theorem current_funds (n:ℕ)(f:Palette S): ‖F s (pigment S K f) n‖ ≤ (local_cost Y H s S).choose * ‖f‖:=
  le_of_tendsto (row_ear Y H S s V n f).norm (Eventually.of_forall (fun j=> (critic Y H S s n (k j)).le_of_opNorm_le (critics Y H S s n (k j)) _))

def gaugeEar (n:ℕ) : Music S:=
  let f:Palette S→ₗ[ℂ] ℂ:= ⟨⟨fun x=> F s (pigment S K x) n, fun x y=>by
     let z:= row_ear Y H S s V n
     exact tendsto_nhds_unique (z (x+y)) (((z x).add (z y)).congr (fun j=> (map_add (critic Y H S s n (k j)) x y).symm))⟩, fun a x=> by
     let z:= row_ear Y H S s V n
     exact tendsto_nhds_unique (z (a • x)) (((z x).const_mul a).congr (fun j=>(map_smul (critic Y H S s n (k j)) a x).symm))⟩
  f.mkContinuous (local_cost Y H s S).choose (current_funds Y H S s V n)

lemma fiscal (n:ℕ): ‖gaugeEar Y H S s V n‖ ≤ (local_cost Y H s S).choose:= ContinuousLinearMap.opNorm_le_bound (gaugeEar Y H S s V n) (xcost ..) (current_funds Y H S s V n)
lemma gaugeEar_eq (n:ℕ)(f:Palette S) : gaugeEar Y H S s V n f= F s (pigment S K f) n:=rfl

def finale : Music S:=
 let f:Palette S→ₗ[ℂ] ℂ:=
  { toFun:= fun x=> E s (pigment S K x)
    map_add' := fun x y=> tendsto_nhds_unique (by_periods Y H S s V (x+y)) (((by_periods Y H S s V x).add (by_periods Y H S s V y)).congr (fun j=>(map_add (gaugeEar Y H S s V (i j)) x y).symm))
    map_smul' := fun a x=> tendsto_nhds_unique (by_periods Y H S s V (a • x)) (((by_periods Y H S s V x).const_mul a).congr (fun j=> (map_smul (gaugeEar Y H S s V (i j)) a x).symm)) }
 f.mkContinuous (local_cost Y H s S).choose (fun x=>le_of_tendsto (by_periods Y H S s V x).norm (Eventually.of_forall fun j=> current_funds Y H S s V (i j) x))

lemma finale_cap: ‖finale Y H S s V‖ ≤ (local_cost Y H s S).choose:= ContinuousLinearMap.opNorm_le_bound (finale Y H S s V) (xcost ..) (fun x=> le_of_tendsto (by_periods Y H S s V x).norm (Eventually.of_forall fun j=> current_funds Y H S s V (i j) x))
lemma finale_eq (f:Palette S): finale Y H S s V f= E s (pigment S K f):=rfl

lemma first_row : ∀ᶠ n:ℕ in atTop,Tendsto (fun j=> (critic Y H S s n (k j))) atTop (𝓝 (gaugeEar Y H S s V n)):=by
  filter_upwards [(boutique Y H V S s).1] with n t
  refine (Metric.tendsto_nhds (a:=gaugeEar Y H S s V n)).mpr fun ε e=> ?_
  have ht : 0 < count S + 1:= by linarith [count_nonneg S]
  let u:= ε/2/(count S+1); have hu: 0 < u := div_pos (half_pos e) ht
  obtain ⟨m,m'⟩:= (suitable S K).exists
  filter_upwards [t _ hu,ready_row Y H S s V n] with j v p
  apply lt_of_le_of_lt _ (half_lt_self e)
  rw [dist_eq_norm (E:=Music S)]; refine ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos e|>.le) (fun x t=>?_)
  change ‖critic _ _ _ _ _ _ _- _‖ ≤ _; rw [onPitch Y H S s p,sharply_s]; rw [←div_mul_cancel₀ (ε/2) ht.ne']
  exact v _ (pigment_test ..) m m' _ (fun z=> (pigment_bound ..).trans (by rw [t,mul_one]; linarith))

omit V
include W
local notation "U"=> W.own
lemma meshed :
    ∀ᶠ n in atTop, dist (gaugeEar Y H S s W.own (i n)) (finale Y H S s W.own) ≤ Meter n*count S ∧
      ∀ t:ℕ,legacy Y (i n) (k t)→ Ready Y H S s (i n) (k t)∧ dist (critic Y H S s (i n) (k t)) (finale Y H S s W.own) ≤ Meter n*count S:=by
  filter_upwards [ConeFilter.criterion.mp (ready_cone Y H S s U),W.crimson S s] with j h t
  have he : 0≤ Meter j*count S := mul_nonneg (meter_p _).le (count_nonneg S)
  let f:=finale Y H S s U
  have hv (x:Palette S)(p:‖x‖=1)(v): ‖(pigment S K x) (momentm Y (i j) s) v‖ ≤ count S:= (pigment_bound ..).trans_eq (by rw [p,mul_one])
  constructor
  · rw [dist_eq_norm (E:=Music S)]; apply ContinuousLinearMap.opNorm_le_of_unit_norm he; exact fun x p=> (t.2 _ (pigment_test ..) _ (hv x p)).1
  intro v p; refine ⟨h v p,?_⟩; rw [dist_eq_norm (E:=Music S)]; apply ContinuousLinearMap.opNorm_le_of_unit_norm he; intro x h'; change ‖critic _ _ _ _ (i j) (k v) x - f x‖ ≤ _; rw [onPitch Y H S s (h v p), sharply_s]; exact (t.2 _ (pigment_test ..) _ (hv x h')).2 v p

lemma hear : Tendsto (fun n:ℕ=> gaugeEar Y H S s W.own (i n)) atTop (𝓝 (finale Y H S s W.own)) ∧
    Tendsto (fun n:ℕ×ℕ=> critic Y H S s (i n.1) (k n.2)) (ConeFilter Y i k) (𝓝 (finale Y H S s W.own)):= by
  have hf : Tendsto (fun j=> Meter j*count S) atTop (𝓝 0):= by simpa using meter_time.mul_const (count S)
  have h(H:ℝ)(p:0<H) := hf.eventually (gt_mem_nhds p)
  refine ⟨(Metric.tendsto_nhds (a:=finale Y H S s W.own)).mpr (fun ε e=> ((meshed Y H S s W).and (h ε e)).mono fun j p=> p.1.1.trans_lt p.2), (Metric.tendsto_nhds (a:=finale Y H S s W.own)).mpr (fun ε e=> ConeFilter.criterion.mpr (((meshed Y H S s W).and (h ε e)).mono fun j p t u=> (p.1.2 t u).2.trans_lt p.2))⟩
end dual

section consistency
open ContinuousLinearMap
lemma pair_eval {I:Type*}{l:Filter I}{A B:Type*}[NormedAddCommGroup A][NormedAddCommGroup B][NormedSpace ℂ A][NormedSpace ℂ B]{f:I→A→L[ℂ]B}{T:A→L[ℂ] B}{g:I→A}{E:A} (h:Tendsto f l (𝓝 T))(d:Tendsto g l (𝓝 E)): Tendsto (fun x=>f x (g x)) l (𝓝 (T E)):= (show Continuous (fun x:(A→L[ℂ]B)× A=> x.1 x.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds d)
include W
local notation "Ωs"=> swept Λ l S
local notation "V₀"=> W.own
lemma across_rows : ∀ᶠ q:ℕ in atTop,gaugeEar Y H S s W.own q=(gaugeEar Y H (swept Λ l S) (s+1) W.own q).comp (P.matinee s S q):=by
  filter_upwards [crowd Y H S s, first_row Y H Ωs (s+1) V₀] with q t h
  apply ContinuousLinearMap.ext; intro x
  change gaugeEar _ _ S _ _ _ _=(gaugeEar Y H Ωs (s+1) W.own q) _
  refine tendsto_nhds_unique_of_eventuallyEq (row_ear Y H S s V₀ q x) (pair_eval h (pair_eval ((W.receipts.clocks s S).inner q) (tendsto_const_nhds (x:=x)))) ?_
  filter_upwards [ready_row Y H S s V₀ q,ready_row Y H Ωs (s+1) V₀ q] with j p v
  exact (onPitch Y H S s p x).trans (Eq.trans (solo Y H s p.1 S t.bigger x) (by rw [onPitch Y H Ωs (s+1) v, house Y H S s ⟨t,p.1⟩])) -- tune

lemma consistent : finale Y H S s W.own = (finale Y H (swept Λ l S) (s+1) W.own).comp (P.issue s S):=by
  apply ContinuousLinearMap.ext; intro f
  change finale Y H S s W.own f=finale Y H Ωs (s+1) W.own (P.issue s S f)
  refine tendsto_nhds_unique_of_eventuallyEq (pair_eval ((hear Y H S s W).1) (tendsto_const_nhds (x:=f))) (pair_eval ((hear Y H Ωs (s+1) W).1) (pair_eval (W.receipts.clocks s S).periods (tendsto_const_nhds (x:=f)))) ?_
  exact ((V₀).pick.grow_i.tendsto_atTop.eventually (across_rows Y H S s W)).mono fun n p=> congrArg (fun h:Music S=> h f) p

-- even the rate holds in the iterated operator step. UV rate may have period-dependent gates.
lemma chamber : ∀ᶠ n in atTop, dist (P.matinee s S (i n)) (P.issue s S) ≤ Meter n:=by
  filter_upwards [W.receipts.errorC s S] with n t
  exact le_of_tendsto (((W.receipts.clocks s S).inner (i n)).dist tendsto_const_nhds) ((cadence Y k (V₀).pick.grow_k (i n)).mono fun j p=> (t j p).2.1)
end consistency
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.hear
#print axioms YM.CF.Buffered.Concord.consistent
