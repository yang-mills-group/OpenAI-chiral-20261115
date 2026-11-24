import YM.SU5.Reconstruction.LinkMeasures.LiteralCost
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
/-!
# The actual-frame material approximation, keeping EXACT S and height and singlet
-/
open PaymentCamera Tower Tower.PhaseChoice CF.Pannier.Chancel
variable (S:Finset Cover)
variable (K:Calibration)(m:Side)(p:Hosp S (K.c m))(Λ:Preparation)(l:ℕ)
local notation "n" => K.c m
local notation "W" => Swatch S
local notation "X" => ScoreBook S
variable (g:Zodiac (K.c m))
local notation "Rr" => rotAct S (g∘wrap (More n))
local notation "τ★" => (rotAct S (g∘wrap (More n)))
local notation "U★" => orbitC S K m
local notation "μs" => actual S Λ l
local notation "q" => qty S Λ l
local notation "bσ" => sideGauge S Λ l
open Set
include p
lemma rotate_funded (i:Evens S)(F:W): ‖(sideGauge S Λ l i) (orbitC S K m F g)‖≤ qty S Λ l F:=by
 let G(j:Evens S) := accession S (F j)
 let x:= accession S ((orbitC S K m F g) i)
 have ht:= physically_rot S (g∘wrap (More n)) Λ l
 have hi(i:Evens S):Integrable (fun y:X=> ‖(G i).val (Rr y)‖) μs:= ht.integrable_comp_of_integrable (Test.finances (actual S Λ l) (G i)).norm
 have he(j:Evens S) : ∫ y:X, ‖(G j).val (Rr y)‖∂μs=bill (actual S Λ l) (G j):=by rw [bill_eq]; nth_rw 2 [← ht.map_eq]; rw [integral_map ht.measurable.aemeasurable (G j).meas.norm.aestronglyMeasurable]
 rw [←widget,bill_eq]; have hh: ∀ y, ‖x.val y‖≤ ∑ i:Evens S,‖(G i).val (Rr y)‖:=fun y=> budget_rotate S K m p g F y i
 refine (integral_mono (Test.finances μs x).norm (integrable_finsetSum _ (fun i _=> hi i)) hh).trans_eq ?_
 rw [integral_finsetSum (s:= Finset.univ) (fun i _=> hi i)]; exact Finset.sum_congr rfl fun i _=> he i

lemma cookDifference (f x:W)(p':Tapestry.Neutral K (Tapestry.render S K x)):
 orbitC S K m (f-x) g=orbitC S K m f g-x:= by change ocelli K S _ (f-x)=_; rw [show ocelli K S (g ∘ wrap (More n)) (f-x)=orbitC S K m f g-orbitC S K m x g from map_sub (show Swatch S →L[ℂ] Swatch S from ocelli K S _) f x]; exact congrArg (orbitC S K m f g- ·) (gauge_fixed S K m p g x p')
lemma integralDifference (f x:W)(h:Continuous (appear S K m f)) (p':Tapestry.Neutral K (Tapestry.render S K x)) (i:Evens S): ‖sideGauge S Λ l i (reynoldsC S K m f-x)‖≤ q (f-x) := by
 let G(g:Zodiac n):=orbitC S K m f g-x; let L:= (sideGauge S Λ l i)
 have he:Integrable G (domeLaw n):= ((orbitC_cont S K m f p h).sub (continuous_const (y:=x))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 calc
  _ = ‖L (∫ g,G g∂domeLaw n)‖:=by unfold G; rw [integral_sub ((orbitC_cont S K m f p h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)]; rw [integral_const,probReal_univ,one_smul]; rfl
  _ ≤ _:=by rw [←(ContinuousLinearMap.integral_comp_comm (E:=Swatch S) (Fₗ:=Lp ℂ 1 μs) (𝕜:=ℂ) L he)]; --
            apply le_trans (norm_integral_le_of_norm_le_const (μ:=domeLaw n) (C:=q (f-x)) ?_); · simp
            apply Eventually.of_forall; intro g; unfold G; rw [←cookDifference S K m p g f x p']; exact rotate_funded S K m p Λ l g i (f-x)
lemma literal_neutral (f:W)(h:Tapestry.Neutral K (Tapestry.render S K f))(ε:ℝ)(x:0<ε): ∃ A:W,A∈ literal S∧ Neutral K (render S K A) ∧ qty S Λ l (A-f)≤ ε:=by
 set r:=Tapestry.spread S; have hr:0≤r:=Nat.cast_nonneg _; set δ:= ε/(r+1); have hδ:0<δ:=by unfold δ; positivity
 obtain ⟨a,t,hp⟩:= billable S Λ l f δ hδ; let A:=reynoldsC S K m a; have hz:= literal_measured S K m a t
 refine ⟨A,polled_lit S K m p a t,neutralC S K m a p hz,?_⟩
 refine (Finset.sum_le_sum (g:=fun _=>δ) (fun i _=>?_)).trans ?_
 · rw [widget]; exact (integralDifference S K m p Λ l a f hz h i).trans hp
 rw [Finset.sum_const,nsmul_eq_mul,card_univ]; change r*δ ≤ ε; have he:(r+1)*δ=ε:=mul_div_cancel₀ ε (by positivity); nlinarith
end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.literal_neutral
