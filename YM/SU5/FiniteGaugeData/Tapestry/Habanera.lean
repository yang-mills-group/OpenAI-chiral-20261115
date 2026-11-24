import YM.SU5.FiniteGaugeData.Tapestry.Temporal
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin Haro
attribute [local instance] opCStarAlgebra
open Pastry Tap Nacre Ember Pec
open Push.BetaTransport

/-!
# Step deformation at a fixed period.

Includes op norm statement for every UV row of a physical exhibition enriched
with Fashion. Note the Loom used by the LIMIT step map is not being altered in a
row. It is taken already from the participating history, and depends on the two
side lengths exactly as therein. The limit parameters aren't a uniform ``bare
criterion'' either. Separate proof of convergence in the period of these steps
at fixed support of BOTH fields (not only when their Loom parameters have matching
stencils) is needed and provided by Exhibition; both use the original steps. We
relate the claims via evaluation on Ward.
-/
set_option quotPrecheck false
section
variable {N P:Side}(G:Ratio N P)(j:ℕ)(M:Male)(ho:Odd G.count.val)(l:Loom N)(q:Chi)(d:ℝ)(A:StepData (More N) (More P))
local notation "F" β:max Q:max => pushMark G A j Q M ho q d β l
variable {R w:ℕ}(p:LaurentRadius j G.count R) (u:A.ratio=ratio G) (a:0<d)(b:2*d<firstRadius SU.group)
  (e:Measurable l)(v:LoomLaw l w)(h:A.patch.Branches A.kernel SU.group)
def tuneₗ (x:Tariff) : Ward N→ₗ[ℂ] Ward P where
  toFun f := frock ((surround G A j x.snd.val M ho q d x.fst l p e h a b (attire f) (Ward.signs f) v u).mono (subset_univ _))
  map_add' f g:= attireL_inj (pushPlus G A j x.snd.val M ho q d x.fst l (attire f) (attire g) p e h a b (Ward.signs f).env (Ward.signs g).env)
  map_smul' z f:= attireL_inj (pushScale G A j x.snd.val M ho q d x.fst l (attire f) p e h a b (Ward.signs f).env z)
local notation "V"=> tuneₗ G j M ho l q d A p u a b e v h
lemma attireT (x:Tariff)(z:Ward N): attire (tuneₗ G j M ho l q d A p u a b e v h x z)= (F x.fst x.snd.val) (attire z):=rfl
lemma tunePlan (x:Tariff) : ∃ D:ℝ,∀ t:Ward N, ‖(V x) t‖ ≤ D*‖t‖:=by
  obtain ⟨Z,X,T⟩:=tollFixed G j M ho p q d x.snd; obtain ⟨W,g,T'⟩:= canopyPrice A h x.fst
  let f:= V x; apply LinearMap.bound_of_ball_bound (by exact zero_lt_one) (W*Z) f -- namespace
  intro z v; have u':= T z (mem_ball_zero_iff.mp v).le
  apply Ward.save; intro w; rw [attireT,outright G A j x.snd.val M ho q d x.fst l p e h a b _ (Ward.signs z).env w]
  refine (norm_integral_le_of_norm_le_const (C:=W*Z) (μ:=city N) ?_).trans_eq (by simp)
  refine Filter.Eventually.of_forall fun u=>?_; rw [norm_smul]
  exact mul_le_mul (mem_of_mem_nhds T' w.1 u.1) (u' ..) (norm_nonneg _) g.le

def tune (x:Tariff) : Ward N →L[ℂ] Ward P:= (V x).mkContinuous _ (tunePlan G j M ho l q d A p u a b e v h x).choose_spec
local notation "σ" => tune G j M ho l q d A p u a b e v h
@[simp] lemma attireTune (x z) : attire (tune G j M ho l q d A p u a b e v h x z) = pushMark G A j x.snd.val M ho q d x.fst l (attire z):=rfl
-- fix omit later
private lemma assemblage {X:Type*}[NormedRing X][NormedAlgebra ℝ X]{a b:ℝ}{A B:X}{q r s t:ℝ}(h:‖a-b‖ ≤ q)(v:‖a‖ ≤ r)(p:‖A-B‖ ≤ s)(w:‖B‖≤ t): ‖a • A-b • B‖ ≤ r*s+q*t:=by
  calc
   _ = ‖a • (A-B)+(a-b) • B‖:= by rw [smul_sub,sub_smul]; abel_nf
   _ ≤ _ := (norm_add_le ..).trans (add_le_add (by rw [norm_smul]; exact mul_le_mul v p (norm_nonneg _) ((norm_nonneg _).trans v)) (by rw [norm_smul]; exact mul_le_mul h w (norm_nonneg _) ((norm_nonneg _).trans h)))
lemma tuneMoves (x:Tariff): ContinuousAt (tune G j M ho l q d A p u a b e v h) x:=by
  refine Metric.tendsto_nhds.mpr fun ε ε' => ?_
  obtain ⟨W,g,T'⟩:= canopyPrice A h x.fst; obtain ⟨Z,X,T⟩:=tollFixed G j M ho p q d x.snd
  let σ₁:ℝ:=(ε/2)/(W+Z); have q₁ :0< σ₁:= by unfold σ₁; positivity
  filter_upwards [(continuous_fst.continuousAt (x:=x)).tendsto.eventually T',(continuous_fst.continuousAt (x:=x)).tendsto.eventually (temporalPrice A h x.fst σ₁ q₁),(continuous_snd.continuousAt (x:=x)).tendsto.eventually (rationTemporal G j M ho p q d x.snd σ₁ q₁)] with y price distance ration
  rw [dist_eq_norm (σ y) (σ x)]; apply lt_of_le_of_lt _ (half_lt_self ε'); apply skimEnvelope (by positivity); intro z τ
  apply Ward.save; intro w'
  change ‖(F y.fst y.snd.val) (attire z) w'- (F x.fst x.snd.val) (attire z) w'‖ ≤ε/2
  have he:= (Ward.signs z).env
  have hv(x:Tariff):= pushIntegrable G A j x.snd.val M ho q d x.fst l (attire z) p e h a b he w' w'.1
  rw [outright G A j y.snd.val M ho q d y.fst l p e h a b _ he w', outright G A j x.snd.val M ho q d x.fst l p e h a b _ he w',←integral_sub (hv y) (hv x)]
  refine (norm_integral_le_of_norm_le_const (C:=ε/2) (μ:=city N) ?_).trans_eq (by simp)
  refine Filter.Eventually.of_forall fun t=>?_
  apply (assemblage (distance w'.1 t.1) (price w'.1 t.1) (ration z (le_of_eq τ) w' (drawn l t)) (T z τ.le w' (drawn l t))).trans_eq
  have hX:= div_mul_cancel₀ (ε/2) (add_pos g X).ne'; dsimp [σ₁]; linarith
lemma tuneGlee (x:Tariff): (σ x) 1=1:= attireL_inj (pushUnit G A j x.snd.val M ho q d x.fst l h)
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.tuneMoves
