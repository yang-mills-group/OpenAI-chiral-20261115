import YM.CF.Buffered.Pinning
import YM.CF.Buffered.Borel

/-!
# The two scalar slabs of the heat donor (payer, Borel on both halves)

Boundary/interior represented redundantly using `RP.quill`: shared both seam
fields from x, positive half field y, reflected negative half z. This stage is
pointwise, not yet averaged over any fields.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Gloss Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra

variable {m B : Side} {c : Phase.Part m B} {A D d e : ℝ}
local notation "X" => Pack m B

lemma primal_nonneg (clip : Clip) (β t : ℝ) (V : Skin m B) :
    0 ≤ primal clip (Domain m B) β t V :=
  ge_of_tendsto' (Spark.going clip t β V) fun _ => (Real.exp_pos _).le
lemma primal_trip (clip : Clip) (β t : ℝ) (b : Trip m) (x : Pack m B) :
    primal clip (Domain m B) β t (onPack B b x).1 = primal clip (Domain m B) β t x.1 := by
  apply tendsto_nhds_unique_of_eventuallyEq (Spark.going ..) (Spark.going ..)
  exact Eventually.of_forall fun _ => congrArg _ (Spark.staff ..)

lemma primal_decks (clip : Clip) (β t : ℝ) (i : Axis) (x y z : Pack m B) :
    let V (y z : Pack m B) := primal clip (Domain m B) β t (tiedK m B i x y z).1
    V y z * V y z = V y y * V z z := by
  intro V
  let U (y z : X) := tiedK m B i x y z
  have he (x : X) := Spark.going (m := m) (B := B) clip t β x.1
  apply tendsto_nhds_unique_of_eventuallyEq ((he (U y z)).mul (he (U y z))) ((he (U y y)).mul (he (U z z)))
  refine Eventually.of_forall fun k => ?_
  change Real.exp _ * Real.exp _ = Real.exp _ * Real.exp _
  rw [← Real.exp_add, ← Real.exp_add]
  apply congrArg
  have h := Spark.steer clip i x y z t β k
  have g := Spark.staff clip (U y z) t β k (slideM m i)
  change sail clip t β k (Pbar m B i (U y z)).1 = _ at g
  rw [show Pbar m B i (U y z)=U z y from sew ..] at g
  exact (congrArg (sail clip t β k (U y z).1 + ·) g.symm).trans h

lemma primal_env (clip : Clip) (β t : ℝ) : Envelope (primal clip (Domain m B) β t) := by
  apply env_indicator _ (calm_m ..)
  apply Env.compact
  exact Real.continuous_exp.comp (continuous_const.mul (ren_c clip)).neg
lemma primal_net_env (clip : Clip) (β t : ℝ) : Envelope (fun x:Pack m B => primal clip (Domain m B) β t x.1 * net m B 0 x) :=
  Envelope.mul (Env.along (primal_env clip β t) measurable_fst) (Env.compact (net_cont m B 0))

def scalarWeight (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t e : ℝ) (x : Pack m B) : ℂ :=
  (TallyR m B e 0).indicator (fun y => ((primal clip (Domain m B) β t y.1 * net m B 0 y:ℝ):ℂ) * Complex.exp (-p.cabin W y)) x
def halfWeight (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t e : ℝ) (i : Axis) (x : Pack m B) : ℂ :=
  (TallyR m B e 0).indicator (fun y => (Real.sqrt (primal clip (Domain m B) β t y.1 * net m B 0 y):ℂ) *
    Complex.exp (-p.pass W i y)) x

variable (p : Pinning m B) {W : Scroll m B c} (H : ScaleK A D W) (g : Budget B e d)
include H g
lemma scalarWeight_split (clip : Clip) (β t : ℝ) (i : Axis) (x y z : Pack m B) :
    let U := tiedK m B i x
    scalarWeight p W clip β t e (U y z) = star (halfWeight p W clip β t e i (U z z)) * halfWeight p W clip β t e i (U y y) := by
  intro U
  unfold scalarWeight halfWeight
  by_cases u : U y z ∈ TallyR m B e 0
  · obtain ⟨e₁,e₂⟩ := (RP.apt ..).1 u
    rw [Set.indicator_of_mem u, Set.indicator_of_mem e₁, Set.indicator_of_mem e₂, p.cabin_split_sewn H g i x y z _ u]
    let f (x : X) := primal clip (Domain m B) β t x.1 * net m B 0 x
    have hf (x:X) : 0 ≤ f x := mul_nonneg (primal_nonneg ..) (net_pos ..)
    have hv : f (U y z) ^ 2 = f (U y y) * f (U z z) := by
      unfold f; rw [mul_pow, decks, pow_two, primal_decks clip β t i x y z]; ring
    have ht := (sq_eq_sq₀ (hf (U y z)) (show 0 ≤ Real.sqrt (f (U y y)) * Real.sqrt (f (U z z)) from mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp (by rw [mul_pow (Real.sqrt _) (Real.sqrt _), Real.sq_sqrt (hf _), Real.sq_sqrt (hf _), hv])
    change (↑(f (U y z)):ℂ)*Complex.exp (-(p.pass W i (U y y) + star (p.pass W i (U z z))))=star ((Real.sqrt (f (U z z)):ℂ)*_) * ((Real.sqrt (f (U y y)):ℂ)*_)
    rw [ht, Complex.ofReal_mul, neg_add, Complex.exp_add, star_mul', show ∀ z : ℂ, star (Complex.exp z)=Complex.exp (star z) from fun z=>Complex.exp_conj z|>.symm,star_neg]
    simp only [Complex.star_def, Complex.conj_ofReal]; ring
  rcases not_and_or.mp (show ¬ (U y y∈ TallyR m B e 0 ∧ U z z ∈ TallyR m B e 0) from fun h => u ((RP.apt ..).2 h)) with k|k <;>
    rw [Set.indicator_of_notMem u, Set.indicator_of_notMem k] <;> simp
lemma scalarWeight_env (clip : Clip) (β t : ℝ) : Envelope (scalarWeight p W clip β t e) := by
  let f (y:X) : ℂ := ↑(primal clip (Domain m B) β t y.1 * net m B 0 y:ℝ)
  let U := TallyR m B e 0
  let g' := U.indicator (p.cabin W)
  obtain ⟨K, -, h⟩ := p.cabin_bound H g
  have he : Envelope g' := env_piece U (tally_meas ..) ((p.cabin_continuousOn H g).mono fun _ p => tallyP p) K fun x p => h x (tallyP p)
  rw [show scalarWeight p W clip β t e = U.indicator (fun y => f y * Complex.exp (-g' y)) from ?_]
  · exact env_indicator _ (tally_meas ..) (env_mult (Girt.pole_w _ _ Complex.continuous_ofReal (primal_net_env clip β t))
      (Girt.pole_w _ (fun z=> Complex.exp (-z)) (Complex.continuous_exp.comp continuous_neg) he))
  apply Set.indicator_congr
  intro y v; dsimp only [g']; rw [Set.indicator_of_mem (show y∈U from v)]
lemma halfWeight_env (clip : Clip) (β t : ℝ) (i : Axis) : Envelope (halfWeight p W clip β t e i) := by
  let f (y:X) : ℂ := Real.sqrt (primal clip (Domain m B) β t y.1 * net m B 0 y:ℝ)
  let U := TallyR m B e 0
  let g' := U.indicator (p.pass W i)
  obtain ⟨K, -, h⟩ := p.cabin_half_bound H g i
  have he : Envelope g' := env_piece U (tally_meas ..) ((p.cabin_half_continuousOn H g i).mono fun _ p => tallyP p) K fun x p => h x (tallyP p)
  rw [show halfWeight p W clip β t e i = U.indicator (fun y => f y * Complex.exp (-g' y)) from ?_]
  · exact env_indicator _ (tally_meas ..) (env_mult (Girt.pole_w _ (fun z:ℝ => (Real.sqrt z:ℂ)) (Complex.continuous_ofReal.comp Real.continuous_sqrt) (primal_net_env clip β t))
      (Girt.pole_w _ (fun z=> Complex.exp (-z)) (Complex.continuous_exp.comp continuous_neg) he))
  apply Set.indicator_congr; intro y v; dsimp only [g']; rw [Set.indicator_of_mem (show y∈U from v)]

end YM.CF.Buffered.Heat
