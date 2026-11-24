import Crape.Heights
import Crape.Sewn
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)
local notation "μ"=>P.ColorHil 3 x
local notation "Lx"=>P.par.R.L
local notation "E"=> (P.physicalEnergy 3 x).E
local notation "T"=>timeMesh P.par
noncomputable def recoup (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(s j:ℕ):P.ColorHil 3 x:= ((basket P.par.R.L C D F s:ℝ):ℂ) • P.viewF 3 x s (certificate P F s j)
open MeshClock
local notation "c" j:max s:max => castor (timeMesh P.par) j s (setback P F j)
-- exact relative gate displacement at any common refinement
lemma parity {j i s:ℕ}(q:F ≤ i)(h:F ≤ j)(e:j ≤ s)(u:i ≤ s) :
 bell T s ((c i s)-(c j s))= tidal P F i-tidal P F j:=by
 have v:=bell_add (timeMesh P.par) s ((c i s)-(c j s)) (c j s); rw [sub_add_cancel,refineZ _ i _ u,refineZ _ j _ e] at v;
 rw [adj_time P F i q,adj_time P F j h]; linarith
lemma notebook {j i s:ℕ}(q:F ≤ i)(h:F ≤ j)(e:j ≤ s)(u:i ≤ s) (t:tidal P F j ≤ tidal P F i) : let n:ℕ:= ((c i s)-(c j s)).toNat
                     whenly (timeMesh P.par) s n=⟨tidal P F i-tidal P F j,sub_nonneg.mpr t⟩ ∧ (n:ℤ)+(c j s)=c i s:=by
 intro n; have H:=parity P F q h e u
 have H0: 0 ≤ c i s-c j s:= (bell_le (timeMesh P.par) s 0 _).mp (by rw [H]; simp [bell]; linarith)
 have hp:(n:ℤ)=(c i s)-(c j s):=Int.toNat_of_nonneg H0
 refine ⟨Subtype.ext ?_, by omega⟩; change _=(tidal P F i-tidal P F j); rw [←H,←hp,natural_time]
lemma align_s {j i s:ℕ}(q:F ≤ i)(h:F ≤ j)(e:j ≤ s)(u:i ≤ s)(t:tidal P F j≤ tidal P F i):
 recoup P F C D x s i = E ⟨tidal P F i-tidal P F j,sub_nonneg.mpr t⟩ (recoup P F C D x s j):=by
 let n:= ((c i s)-(c j s)).toNat; obtain ⟨p,v⟩:= notebook P F (j:=j) (s:=s) q h e u t; change (n:ℤ)+_= _ at v
 let f:= certificate P F s j; let g:= P.passesLater 3 s n f
 have he:P.viewF 3 x s (certificate P F s i)=P.viewF 3 x s g:=P.identical_F 3 x s _ _ (by rw [er P F s i q u, er P F s j h e,P.shifts_sum,v])
 unfold recoup; rw [he,P.releasedLater _ _ _ n f,map_smul,p]
#check parity
#print axioms align_s
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
