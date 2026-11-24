import YM.CF.Buffered.Weight

/-!
# The actual two-slab trace, for even marks

Use **kernel calculus throughout**, as in VolumeBurn. `kernelTrace` is
tr(TU) of Hilbert-Schmidt *kernels*, i.e. cyclic integral (two links in the
cycle). `kernelStar` is the Hilbert-Schmidt kernel adjoint. We show this
formula directly including its absolute-integrability conditions; no abstract
trace or spectral theory of Hilbert space operators is needed.

Redundant environment coordinates with probability weights for the T kernels:
use two independent `Pack`s for the seam data. Each holds the variables of
its own seam (others dummy). The entry pack supplies the shared links starting
on the entry plane and cues with grid index there, exit supplies the rest of
the shared data. Thus no disintegration assumptions for the gauge/tag law.
Compare to `Reflect/Merged` for this method with one pack for both; below
`twoSeams_mp` combines them before using `tiedK`. `quill` uses only the
shared cells from this combined pack.

See `Channels` for normalization of the individual slab kernel, convenient
also for different marks on the two sides. We have *two* seam channel indices
and integrate over *both* seams. Costs at fixed cutoff/geometry only.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {e d a₁ a₂ : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "U₊" => upperP (CSide m B)
local notation "Wμ" => wheel m B

-- entry pack x, exit pack y
def twoSeams (i : Axis) (z : Pack m B × Pack m B) :=
  stitch m B (univ.filter (fun e : RZ m B => e.1 i=0)) (univ.filter (fun j : Index m => j i=0)) z.1 z.2
private lemma twoSeams_mp (i) : MeasurePreserving (twoSeams i) ((Wμ).prod Wμ) Wμ := binary_w ..

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)
/-- Marked transfer kernel at this cutoff/layer count. First (row) index
entry; second index exit. -/
def transfer (e : ℝ) (i : Axis) (cut : Foot m B) (n : ℕ) (f : RP.Test m B)
    (j k : Tape m B (n+1)) (x : X × X) :=
  ∫ y, kernelInside p W clip β t u e i cut n f j k (tiedK m B i (twoSeams i x) y y) ∂Wμ

/-- Cyclic trace of two integral kernels. We use finite sums (counting measure)
for channels. -/
def kernelTrace (n : ℕ) (V W : Tape m B n → Tape m B n → Pack m B × Pack m B → ℂ) :=
  ∑ i : Tape m B n, ∑ j : Tape m B n, ∫ x:X×X, V i j x * W j i x.swap ∂((Wμ).prod Wμ)

def kernelStar (n : ℕ) (V : Tape m B n → Tape m B n → Pack m B × Pack m B → ℂ) := fun j i x => star (V i j (Prod.swap x))
theorem trace_mul_star (n : ℕ) (V : Tape m B n → Tape m B n → Pack m B × Pack m B → ℂ)
    (_h : ∀ j k, Envelope (V j k)) : 0 ≤ kernelTrace n V (kernelStar n V) :=
  sum_nonneg fun j _ => sum_nonneg fun k _ => integral_nonneg fun x => mul_star_self_nonneg (V j k x)
lemma trace_integrable {n : ℕ} (V W : Tape m B n → Tape m B n → Pack m B × Pack m B → ℂ)
    (h : ∀ j k, Envelope (V j k)) (w : ∀ j k, Envelope (W j k)) (a k) :
    Integrable (fun x : X×X => V a k x * W k a x.swap) ((Wμ).prod Wμ) :=
  Env.integrableX (env_mult (h a k) (Env.along (w k a) measurable_swap)) _
lemma star_env {n : ℕ} {V : Tape m B n → Tape m B n → Pack m B × Pack m B → ℂ} (h : ∀ j k, Envelope (V j k)) (a k) :
    Envelope (kernelStar n V a k) := Girt.pole_w _ star continuous_star (Env.along (h k a) measurable_swap)

variable (b : Budget B e d) (H : ScaleK a₁ a₂ W) (i : Axis) (cut : Foot m B)
include H b
section
local notation "T" => transfer p W clip β t u e i cut
local notation "κ" => kernelInside p W clip β t u e i cut
local notation "M" => slabTerm p W clip β t e
lemma marginalK_env {n : ℕ} (f : RP.Test m B) (hf : Envelope f) (j k : Tape m B (n+1)) :
    Envelope (fun x => ∫ y, κ n f j k (tiedK m B i x y y) ∂Wμ) := by
  have hp : Continuous fun p:X×X=> tiedK m B i p.1 p.2 p.2 := (tiedC i).comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd))
  exact env_marginal (f:=fun x=> κ n f j k (tiedK m B i x.1 x.2 x.2)) (Env.along (kernelInside_env p W clip β t u b H i cut n f hf j k) hp.measurable) _
lemma transfer_env {n : ℕ} (f : RP.Test m B) (hf : Envelope f) (j k : Tape m B (n+1)) :
    Envelope (T n f j k) := Env.along (marginalK_env p W clip β t u b H i cut f hf j k) (twoSeams_mp _).measurable
lemma hilbert_schmidt {n : ℕ} (f : RP.Test m B) (hf : Envelope f) (j k : Tape m B (n+1)) :
    MemLp (T n f j k) 2 ((Wμ).prod Wμ) := by
  have h := transfer_env p W clip β t u b H i cut f hf j k
  exact MemLp.of_bound h.meas.aestronglyMeasurable _ (Eventually.of_forall h.cost.choose_spec)

/-- Identify each approximant with the trace of the two filled slabs with
marks at the bra ends. -/
theorem at_layer (hu : 0 ≤ u) (n : ℕ) (f g : RP.Test m B) (hf : NorthMark i f) (hg : NorthMark i g) :
    (∫ x, slabTerm p W clip β t e (testProduct i f g) (hotEvol i cut u n) x ∂wheel m B) =
      kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)) := by
  let N := Tape m B (n+1)
  let a := tiedK m B i
  let F (x) (y) j k := κ n f j k (a x y y)
  let G (x) (y) j k := κ n g j k (a x y y)
  let P (j k : N) x := (∫ y, G x y j k ∂Wμ)*star (∫ y, F x y j k ∂Wμ)
  let Q := M (testProduct i f g) (hotEvol i cut u n)
  have hp := slabTerm_env p W clip β t b H _ _ (product_env i hf.envelope hg.envelope) (Env.compact (hotEvol_cont i cut u n))
  have ht(j k:N):Envelope (P j k):=env_mult (marginalK_env p W clip β t u b H i cut g hg.envelope j k)
    (Girt.pole_w _ star continuous_star (marginalK_env p W clip β t u b H i cut f hf.envelope j k))
  have hx (x : X) : (∫ z, Q (RP.quill m B i (x,z)) ∂(Wμ).prod Wμ)= ∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), P j k x := by
    let A' j k (z:X×X) := G x z.1 j k * star (F x z.2 j k)
    have he (z:X×X) : Q (RP.quill m B i (x,z))=∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), A' j k z :=
      (sewn_sum p W clip β t u b H hu i cut n f g hf hg x z.1 z.2).trans (sum_congr rfl fun j _ => sum_congr rfl fun k _ => mul_comm ..)
    have hA (j k:N): Envelope (A' j k) := by
      have hz : Continuous fun y:X=> tiedK m B i x y y := (zoneA i x).comp (continuous_id.prodMk continuous_id)
      exact env_mult (Env.along (kernelInside_env p W clip β t u b H i cut n g hg.envelope j k) (hz.measurable.comp measurable_fst))
        (Girt.pole_w _ star continuous_star (Env.along (kernelInside_env p W clip β t u b H i cut n f hf.envelope j k) (hz.measurable.comp measurable_snd)))
    simp_rw [he]
    rw [integral_finsetSum]; swap
    · exact fun i _ => Env.integrableX (Env.total _ (hA i)) _
    refine sum_congr rfl fun j _ => ?_; rw [integral_finsetSum]; swap
    · exact fun i _ => Env.integrableX (hA j i) _
    refine sum_congr rfl fun k _ => ?_ ; unfold A' P; rw [integral_prod_mul (fun y=> G x y j k) (fun z => star (F x z j k))]; exact congrArg (_ * ·) (show (∫ z, star (F x z j k) ∂Wμ)=_ from integral_conj (𝕜:=ℂ) (f:=fun z=> F x z j k))
  unfold kernelTrace; rw [heard m B i Q (Env.integrableX hp Wμ)]
  simp_rw [hx]; rw [integral_finsetSum]; swap
  · exact fun i _ => Env.integrableX (Env.total _ (ht i)) _
  refine sum_congr rfl fun j _ => ?_; rw [integral_finsetSum]; swap
  · exact fun i _ => Env.integrableX (ht j i) _
  refine sum_congr rfl fun k _ => ?_
  -- use both seams and their measures
  simp_rw [kernelStar,Prod.swap_swap]
  change ∫ x,P j k x ∂Wμ = ∫ x, P j k (twoSeams i x) ∂(Wμ).prod Wμ
  have hv := twoSeams_mp (m:=m) (B:=B) i
  exact (congrArg (fun ν:Measure X => ∫ x,P j k x ∂ν) hv.map_eq.symm).trans (integral_map hv.measurable.aemeasurable (ht j k).meas.aestronglyMeasurable)

lemma slab_limit (f : RP.Test m B) (hf : Envelope f) : Tendsto (fun n=> ∫ x, M f (hotEvol i cut u n) x ∂Wμ)
    atTop (𝓝 (heatNum p W clip β t e u (axisCut m B i cut) f)) := by
  obtain ⟨K',W',hk,hw,v⟩ := hotEvol_uniform i cut u
  have hP := scalarWeight_env p H b clip β t
  have hK:= seedOp_env (m:=m) b
  obtain ⟨d₁,h₁⟩:=hf.cost; obtain ⟨d₂,h₂⟩:=hP.cost; obtain ⟨d₃,h₃⟩:=hK.cost
  obtain ⟨K,L⟩:=v.norm.bddAbove_range

  let τ : X → ℝ := fun _=> d₂*(d₁*K*d₃)
  unfold heatNum; rw [heatTerm_slab p W clip β t u b]
  refine tendsto_integral_filter_of_dominated_convergence τ (Eventually.of_forall fun n=>
    (slabTerm_env p W clip β t b H _ _ hf (Env.compact (hotEvol_cont i cut u n))).meas.aestronglyMeasurable) ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun n=> Eventually.of_forall fun x=> ?_
    have hn : ‖hotEvol i cut u n x‖ ≤ K:= by rw [←hk n]; exact ((K' n).norm_coe_le_norm x).trans (L ⟨n,rfl⟩)
    have hm : ‖f x * hotEvol i cut u n x‖ ≤ d₁*K:= (norm_mul_le ..).trans (mul_le_mul (h₁ x) hn (norm_nonneg _) ((norm_nonneg _).trans (h₁ x)))
    unfold slabTerm; rw [norm_mul]; exact mul_le_mul (h₂ x) ((norm_entry ..).trans ((norm_mul_le ..).trans (mul_le_mul hm (h₃ _) (norm_nonneg _) ((norm_nonneg _).trans hm)))) (norm_nonneg _) ((norm_nonneg _).trans (h₂ x))
  refine Eventually.of_forall fun x => ?_
  let V(y:A):=scalarWeight p W clip β t e x * (f x*y*seedOp e x) U₊ U₊
  have hv : Continuous V:=continuous_const.mul (((continuous_const.mul continuous_id).mul continuous_const).matrix_elem _ _)
  have hE : Tendsto (fun n=>hotEvol i cut u n x) atTop (𝓝 (actualEvol i cut u x)) := by
    simp_rw [←hk, ←hw x]; exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp v).tendsto_at x
  exact (hv.tendsto _).comp hE

theorem from_layers (hu : 0 ≤ u) (f g : RP.Test m B) (hf : NorthMark i f) (hg : NorthMark i g) :
    Tendsto (fun n => kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)))
      atTop (𝓝 (heatNum p W clip β t e u (axisCut m B i cut) (testProduct i f g))) :=
  (slab_limit p W clip β t u b H i cut _ (product_env i hf.envelope hg.envelope)).congr
    (fun n => at_layer p W clip β t u b H i cut hu n f g hf hg)

theorem two_slab (hu : 0 ≤ u) (f : RP.Test m B) (hf : NorthMark i f) :
    0 ≤ heatNum p W clip β t e u (axisCut m B i cut) (testProduct i f f) :=
  ge_of_tendsto' (from_layers p W clip β t u b H i cut hu f f hf hf) fun _ =>
    trace_mul_star _ _ (transfer_env p W clip β t u b H i cut _ hf.envelope)
end
end YM.CF.Buffered.Heat
