import YM.CF.Buffered.Weight

/-!
# The chord-i reflection budget at the very same heat donor

Modified from Buffered/Weight, tracking parity XOR of rightHand when f is odd.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open YM.CF.Buffered.Heat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
open RP Spark RG WilsonStartup Vale Scroll Spire Nova Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {e d : ℝ}
local notation "X" => Pack m B
local notation "I" => Xmind m B
local notation "A" => FC (Xmind m B)
local notation "U" => upperP (CSide m B)

structure HalfOdd (i : Axis) (f : RP.Test m B) : Prop where
  envelope : Envelope f
  sector (x) : Sector (colony m B i) true (f x)
  loc x y : NorthOf m B i x y → f x=f y

lemma rightHand_odd (u : ℝ) (i : Axis) (cut : Foot m B) (n : ℕ)
    (f : RP.Test m B) (h : HalfOdd i f) (a b : Tape m B (n+1)) (x : X) (e : ℝ) :
    Sector (colony m B i) (true.xor (parityTape _ a b)) (rightHand i cut u e n f x a b) := by
  have he := sector_exp (RP.letter U (colony m B i) (seedArg e x))
  simpa only [rightHand, Bool.xor_false, Bool.false_xor] using (((h.sector x).mul (hand_sector i cut _ x _ a b)).mul he : Sector (colony m B i) _ (rightHand i cut u e n f x a b))

variable (p : Pinning m B) (W : Scroll m B c) (clip : Clip) (β t u : ℝ)
variable {a₁ a₂ : ℝ} (b : Budget B e d) (H : ScaleK a₁ a₂ W)
include b H
local notation "λ₀" => fun (i : ℕ)=> (i+1:ℝ)⁻¹
lemma sewnOdd (hu : 0 ≤ u) (i : Axis) (cut : Foot m B) (n : ℕ) (f g : RP.Test m B) (hf : HalfOdd i f) (hg : HalfOdd i g)
    (x y z : Pack m B) : let Q := tiedK m B i x
    slabTerm p W clip β t e (Complex.I • testProduct i f g) (hotEvol i cut u n) (Q y z) =
      ∑ a : Tape m B (n+1), ∑ k : Tape m B (n+1),
        star (kernelInside p W clip β t u e i cut n f a k (Q z z)) * kernelInside p W clip β t u e i cut n g a k (Q y y) := by
  intro Q
  unfold slabTerm
  rw [scalarWeight_split p H b]
  by_cases k : Q y z ∈ TallyR m B e 0
  · let T := RP.finger m B i; let S := RP.colony m B i; let σ := Q z z; let γ := Q y y
    let F := f σ; let G := g γ
    let P := pairSquare T true F G
    let r := λ₀ n * u
    let A' := hand i cut r γ (n+1); let B' := hand i cut r σ (n+1)
    have ht : (Complex.I • testProduct i f g) (Q y z)= P := by
      rw [Pi.smul_apply]; unfold testProduct P pairSquare
      rw [show Pbar m B i (Q y z)=Q z y from sew .., hf.loc _ σ (strum ..), hg.loc _ γ (strum ..)]; rfl
    have hE : hotEvol i cut u n (Q y z)= ∑ a,∑ b, pairSquare T (parityTape _ a b) (B' a b) (A' a b) := n_layer_expand i cut u _ (by positivity) x y z _
    rw [ht,hE,seed_split b i k]; simp_rw [Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply,Finset.mul_sum]; refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    let z' := halfSeed e i σ; let y' := halfSeed e i γ
    let w := parityTape _ a b
    have hz : Sector S false z' := sector_exp (RP.letter ..)
    have hA : Sector S w (A' a b) := hand_sector ..
    have hB : Sector S w (B' a b) := hand_sector ..
    have hv :
        P * pairSquare T w (B' a b) (A' a b) * pairSquare T false z' y' =
         pairSquare T (true.xor w) (rightHand i cut u e n f σ a b) (rightHand i cut u e n g γ a b) := by
      unfold P
      rw [square_mul T S (hg.sector γ) hB (movedCol ..), square_mul T S ((hg.sector γ).mul hA) hz (movedCol ..), Bool.xor_false]; rfl
    let V₁ := rightHand i cut u e n f σ a b; let V₂ := rightHand i cut u e n g γ a b
    let h x := halfWeight p W clip β t e i x
    change star (h σ)*h γ * (P * pairSquare T w _ _ * pairSquare T false z' y') U U = star (h σ * V₁ U U) * (h γ * V₂ U U)
    rw [hv, show pairSquare T (true.xor w) V₁ V₂ U U = star (V₁ U U)*V₂ U U from
      theta_square U T (slide_plus i) S (movedCol ..) V₁ V₂ (true.xor w) (rightHand_odd u i cut n f hf a b σ _) (rightHand_odd u i cut n g hg a b γ _), star_mul']; ring
  dsimp only [kernelInside, halfWeight]
  rcases not_and_or.mp (show ¬ (Q y y∈ TallyR m B e 0 ∧ Q z z ∈ TallyR m B e 0) from fun h => k ((RP.apt ..).2 h)) with l|l
  all_goals dsimp only [Q] at l ⊢; simp_rw [Set.indicator_of_notMem l]; simp

end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.sewnOdd
