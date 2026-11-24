import YM.SU5.Reconstruction.LinkMeasures.PointWard
import YM.SU5.Reconstruction.LinkMeasures.Springs
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
open PaymentCamera Tower Tower.PhaseChoice CF.Pannier.Chancel
variable (S:Finset Cover)
variable (K:Calibration)(m:Side)(p:Hosp S (K.c m))(Λ:Preparation)(l:ℕ)
local notation "n" => K.c m
local notation "W" => Swatch S
local notation "X" => ScoreBook S
variable (g:Zodiac (K.c m))
local notation "U★" => orbitC S K m
lemma literal_measured (f:W)(h:f∈ literal S): Continuous (Tapestry.appear S K m f):=by
 change Continuous (fun v:Fields (K.c m)=> Tapestry.appear S K m f v); simp_rw [seek_op]; refine continuous_finsetSum _ fun i _=> ?_; exact (((item_clear S i f h).comp (seek_c S K m))).smul continuous_const
include p
lemma literal_orbit_closed (f:W)(h:f∈ literal S):∃ A:Submodule ℂ (Swatch S), A.FG ∧ A ≤ literal S ∧ ∀ g, orbitC S K m f g∈ A:=by
 choose x t u using fun i:Evens S=> (show ∃ x:Manifest S,x∈ glancing S∧ mentor S x=f i from h i (Set.mem_univ _))
 choose V₀ b v w using fun i:Evens S=> orbit_purchased S _ (t i)
 let Z: Submodule ℂ (Manifest S):= ⨆ i:Evens S, V₀ i; let A:= Z.map (mentor S)
 refine ⟨Submodule.pi Set.univ (fun _:Evens S=>A), Submodule.fg_pi (fun i=> (Submodule.fg_iSup V₀ b).map _), ?_,fun g'=>?_⟩
 · have a : Z≤ glancing S:= iSup_le v; have h:A ≤ literalM S := Submodule.map_mono a; exact fun Q p i x=> h (p i x)
 intro j _
 let c(i:Evens S):= eye S K m p j (twist (star (quantU (tradew n g'))) (spool n (tagWord S i.val)))
 let U:=g'∘ wrap (More n)
 let V:= ∑ i:Evens S, c i • sight S U (x i)
 refine ⟨V, Z.sum_mem (fun i _=> Z.smul_mem _ (show sight S U (x i)∈ Z from (le_iSup V₀ i : V₀ i ≤ Z) (w i U))),?_⟩
 refine (seatFaith S).symm.injective (Subtype.ext (show (accession S (mentor S V)).val=(accession S (orbitC S K m f g' j)).val from funext fun y=> ?_)); rw [mentor_read S, single_entry S K m p]; simp_rw [←u,mentor_read]; unfold V; simp_rw [ContinuousMap.sum_apply,ContinuousMap.smul_apply]; rfl
lemma polled_lit(f:W)(h:f∈ literal S) : reynoldsC S K m f ∈ literal S := by
 obtain ⟨A,v,a,k⟩:=literal_orbit_closed S K m p f h; haveI : Module.Finite ℂ A:= (Submodule.fg_iff_finiteDimensional A).mp v
 apply a
 exact sky_integral (E:=Swatch S) (M:=A) (domeLaw n) A.closed_of_finiteDimensional ((orbitC_cont S K m f p (literal_measured S K m f h)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (Eventually.of_forall k)

end YM.CF.Buffered.Afterglow.Satori
#print axioms YM.CF.Buffered.Afterglow.Satori.polled_lit
#print axioms YM.CF.Buffered.Afterglow.Satori.literal_measured
