import YM.CF.Buffered.Trace

/-! # Reuse the actual seam pairing estimator, ON BOTH grades -/
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


variable {g₀ : Bool}
structure PolePiece (g₀ : Bool) (i : Axis) (f : RP.Test m B) : Prop where
  envelope : Envelope f
  sector (x) : Sector (colony m B i) g₀ (f x)
  loc x y : NorthOf m B i x y → f x=f y


def dialProduct (g₀ : Bool)(i : Axis)(f g : RP.Test m B): RP.Test m B := chord g₀ • testProduct i f g
lemma dialProduct_env (b: Bool)(i : Axis) {f g : RP.Test m B} (h : Envelope f) (k : Envelope g) : Envelope (dialProduct b i f g):= Girt.pole_w _ (fun x: A=> chord b • x) (by fun_prop) (product_env i h k)

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)
lemma poll_sector (i : Axis) (cut : Foot m B) (n : ℕ)
    (f : RP.Test m B) (h : PolePiece g₀ i f) (a b : Tape m B (n+1)) (x : X) (e : ℝ) :
    Sector (colony m B i) (g₀.xor (parityTape _ a b)) (rightHand i cut u e n f x a b) := by
  have he := sector_exp (RP.letter U₊ (colony m B i) (seedArg e x))
  simpa only [rightHand, Bool.xor_false, Bool.false_xor] using (((h.sector x).mul (hand_sector i cut _ x _ a b)).mul he : Sector (colony m B i) _ (rightHand i cut u e n f x a b))

variable (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include H b

lemma pole_sum (hu : 0 ≤ u) (i : Axis) (cut : Foot m B) (n : ℕ) (f g : RP.Test m B) (hf : PolePiece g₀ i f) (hg : PolePiece g₀ i g)
    (x y z : Pack m B) : let Q := tiedK m B i x
    slabTerm p W clip β t e (dialProduct g₀ i f g) (hotEvol i cut u n) (Q y z) =
      ∑ a : Tape m B (n+1), ∑ k : Tape m B (n+1),
        star (kernelInside p W clip β t u e i cut n f a k (Q z z)) * kernelInside p W clip β t u e i cut n g a k (Q y y) := by
  intro Q
  unfold slabTerm
  rw [scalarWeight_split p H b]
  by_cases k : Q y z ∈ TallyR m B e 0
  · let T := RP.finger m B i; let S := RP.colony m B i; let σ := Q z z; let γ := Q y y
    let F := f σ; let G := g γ
    let P := pairSquare T g₀ F G
    let r := ((n+1:ℝ)⁻¹) * u
    let A' := hand i cut r γ (n+1); let B' := hand i cut r σ (n+1)
    have ht : dialProduct g₀ i f g (Q y z)= P := by
      change chord g₀ • (theta T (f (Pbar m B i (Q y z))) * g (Q y z)) = chord g₀ • (theta T (f σ) * g γ)
      rw [show Pbar m B i (Q y z)=Q z y from sew .., hf.loc _ σ (strum ..), hg.loc _ γ (strum ..)]
    have hE : hotEvol i cut u n (Q y z)= ∑ a,∑ b, pairSquare T (parityTape _ a b) (B' a b) (A' a b) := n_layer_expand i cut u _ (by positivity) x y z _
    rw [ht,hE,seed_split b i k]; simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply,Finset.mul_sum]; refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    let z' := halfSeed e i σ; let y' := halfSeed e i γ
    let w := parityTape _ a b
    have hz : Sector S false z' := sector_exp (RP.letter ..)
    have hA : Sector S w (A' a b) := hand_sector ..
    have hB : Sector S w (B' a b) := hand_sector ..
    have hv :
        P * pairSquare T w (B' a b) (A' a b) * pairSquare T false z' y' =
         pairSquare T (g₀.xor w) (rightHand i cut u e n f σ a b) (rightHand i cut u e n g γ a b) := by
      unfold P
      rw [square_mul T S (hg.sector γ) hB (movedCol ..), square_mul T S ((hg.sector γ).mul hA) hz (movedCol ..), Bool.xor_false]; rfl
    let V₁ := rightHand i cut u e n f σ a b; let V₂ := rightHand i cut u e n g γ a b
    let h x := halfWeight p W clip β t e i x
    change star (h σ)*h γ * (P * pairSquare T w _ _ * pairSquare T false z' y') U₊ U₊ = star (h σ * V₁ U₊ U₊) * (h γ * V₂ U₊ U₊)
    rw [hv, show pairSquare T (g₀.xor w) V₁ V₂ U₊ U₊ = star (V₁ U₊ U₊)*V₂ U₊ U₊ from
      theta_square U₊ T (slide_plus i) S (movedCol ..) V₁ V₂ (g₀.xor w) (poll_sector u i cut n f hf a b σ _) (poll_sector u i cut n g hg a b γ _), star_mul']; ring
  dsimp only [kernelInside, halfWeight]
  rcases not_and_or.mp (show ¬ (Q y y∈ TallyR m B e 0 ∧ Q z z ∈ TallyR m B e 0) from fun h => k ((RP.apt ..).2 h)) with l|l
  all_goals dsimp only [Q] at l ⊢; simp_rw [Set.indicator_of_notMem l]; simp

variable (i : Axis) (cut : Foot m B)
section
local notation "T" => transfer p W clip β t u e i cut
local notation "κ" => kernelInside p W clip β t u e i cut
local notation "M" => slabTerm p W clip β t e
theorem fixed_poles (hu : 0 ≤ u) (n : ℕ) (f g : RP.Test m B) (hf : PolePiece g₀ i f) (hg : PolePiece g₀ i g) :
    (∫ x, slabTerm p W clip β t e (dialProduct g₀ i f g) (hotEvol i cut u n) x ∂wheel m B) =
      kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)) := by
  let N := Tape m B (n+1)
  let a := tiedK m B i
  let F (x) (y) j k := κ n f j k (a x y y)
  let G (x) (y) j k := κ n g j k (a x y y)
  let P (j k : N) x := (∫ y, G x y j k ∂Wμ)*star (∫ y, F x y j k ∂Wμ)
  let Q := M (dialProduct g₀ i f g) (hotEvol i cut u n)
  have hp := slabTerm_env p W clip β t b H _ _ (dialProduct_env g₀ i hf.envelope hg.envelope) (Env.compact (hotEvol_cont i cut u n))
  have ht(j k:N):Envelope (P j k):=env_mult (marginalK_env p W clip β t u b H i cut g hg.envelope j k)
    (Girt.pole_w _ star continuous_star (marginalK_env p W clip β t u b H i cut f hf.envelope j k))
  have hx (x : X) : (∫ z, Q (RP.quill m B i (x,z)) ∂(Wμ).prod Wμ)= ∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), P j k x := by
    let A' j k (z:X×X) := G x z.1 j k * star (F x z.2 j k)
    have he (z:X×X) : Q (RP.quill m B i (x,z))=∑ j : Tape m B (n+1), ∑ k : Tape m B (n+1), A' j k z :=
      (pole_sum p W clip β t u b H hu i cut n f g hf hg x z.1 z.2).trans (sum_congr rfl fun j _ => sum_congr rfl fun k _ => mul_comm ..)
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
  have hv : MeasurePreserving (twoSeams i) ((Wμ).prod Wμ) Wμ := binary_w ..
  exact (congrArg (fun ν:Measure X => ∫ x,P j k x ∂ν) hv.map_eq.symm).trans (integral_map hv.measurable.aemeasurable (ht j k).meas.aestronglyMeasurable)

theorem from_poles (hu : 0 ≤ u) (f g : RP.Test m B) (hf : PolePiece g₀ i f) (hg : PolePiece g₀ i g) :
    Tendsto (fun n => kernelTrace (n+1) (T n g) (kernelStar (n+1) (T n f)))
      atTop (𝓝 (heatNum p W clip β t e u (axisCut m B i cut) (dialProduct g₀ i f g))) :=
  (slab_limit p W clip β t u b H i cut _ (dialProduct_env g₀ i hf.envelope hg.envelope)).congr
    (fun n => fixed_poles p W clip β t u b H i cut hu n f g hf hg)

theorem pole_positive (hu : 0 ≤ u) (f : RP.Test m B) (hf : PolePiece g₀ i f) :
    0 ≤ heatNum p W clip β t e u (axisCut m B i cut) (dialProduct g₀ i f f) :=
  ge_of_tendsto' (from_poles p W clip β t u b H i cut hu f f hf hf) fun _ =>
    trace_mul_star _ _ (transfer_env p W clip β t u b H i cut _ hf.envelope)
end
end YM.CF.Buffered.Heat

#print axioms YM.CF.Buffered.Heat.pole_positive
