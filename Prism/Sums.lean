import Taffeta.Quote
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered Dyad Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
namespace Decaf
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}(V:Grace K R L){e h:ℝ}{m B:Side}{P:Grasp V.U B e}(W:GivenX V P)
variable {I:Type}[Fintype I][LinearOrder I]{G:Scree.Loom (mid m B)}
local notation "Sm"=> mid m B
local notation "Pk"=> PairKey I
set_option maxHeartbeats 1200000 in
lemma bound_tip (o:I→ Site Sm)(T:Log I Sm)(X:GramM Sm){κ q r F0:ℝ}(x:Clinic o T 1 h κ q X R.L (soot r))(y:∀ v:Key Pk,v∈Mew.hill Pk→ ∀ z:Orbit Sm, ‖Graph.recX P (markedB T X v) G z‖≤ Real.exp F0)(z:Orbit Sm)(l:List Pk): ‖Complex.exp (-X.v) • season_Y (Gℓ:=G) (X:=X) (U:=P) V T l z‖≤ Real.exp F0:=by
 let g(v:Key Pk):=dSign (U:=P) (X:=X) (Gℓ:=G) V T v z
 let s:= Complex.exp (-X.v)
 have he:River g:= allC V o T z x.age.1 x.age.2
 have H:River (fun v=> s • g v):=by
   exact sc_V he (s • ContinuousLinearMap.id _ _)
 change ‖s • tipI g l‖ ≤ _; rw [←tip_C he s l]; apply lance_bound H _ _ _ roots; exact fun v hv=>y v hv z

lemma bound_clover (o:I→ Site Sm)(T:Log I Sm)(X:GramM Sm){κ q r F0 a:ℝ}
 (x:Clinic o T 1 h κ q X R.L (soot r))(y:∀ v:Key Pk,v∈Mew.hill Pk→ ∀ z:Orbit Sm, ‖Graph.recX P (markedB T X v) G z‖≤ Real.exp F0)(v:Real.exp a≤‖Complex.exp (-X.v)*partitionZ X P G‖)
 (l:List Pk): ‖response (X:=X) (G₀:=G) (U:=P) V T l 1‖≤Real.exp (F0-a):=by
 let b:= season_Y (X:=X) (Gℓ:=G) (U:=P) V T l
 let s:=Complex.exp (-X.v); let f:= fun z=>beamZ Sm (b z)
 have hf(z): ‖s*f z‖≤ Real.exp F0:=by
    let Wm:=mateK Sm
    change ‖s*inner ℂ Wm (b z)‖≤ _
    rw [←inner_smul_right]
    refine (norm_inner_le_norm ..).trans ?_; rw [(tickB Sm).2,one_mul]; exact bound_tip V o T X x y z l
 have hi: ‖s* ∫ z,f z ∂city Sm‖≤ Real.exp F0:=by
    rw [← integral_const_mul]; refine (norm_integral_le_of_norm_le (integrable_const _) (Filter.Eventually.of_forall hf)).trans ?_; rw [integral_const,MeasureTheory.probReal_univ,one_smul]
    -- Goal may reflexivity
    
 let A:=∫ z,f z ∂city Sm; let Bv:=partitionZ X P G
 unfold response; rw [Buffered.markvac]; change ‖A / Bv‖≤ _
 rw [←mul_div_mul_left A Bv (Complex.exp_ne_zero (-X.v)),norm_div]
 let ha:= ‖s*Bv‖; change _/ha ≤ _; rw [Real.exp_sub]; exact div_le_div₀ (Real.exp_pos _).le hi (Real.exp_pos _) v -- check order
#print axioms bound_clover
end Decaf
end YM.CF.Py.Rate
end
