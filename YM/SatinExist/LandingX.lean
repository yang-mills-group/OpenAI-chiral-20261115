import YM.SatinExist.BilletV
import YM.SatinExist.Plutus
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey
variable {N P:Side}(G:Ratio N P) (j:ℕ)(hj:4≤j)(p:Odd G.count.val)(e:3≤G.count.val)
namespace Xara
open Buffered.Stent.Rhoda
variable (Q:SpaceM)(M:Male)(ho:‖Q‖≤1){w:ℕ}(b:LaurentRadius j G.count w)(w₀:2*w<N.val)
variable (V:StepData (More N) (More P))(ξ:Chi)(δ β:ℝ)(l:Loom N) (t:V.patch.Branches V.kernel SU.group)(q:0<δ)(u:2*δ<firstRadius SU.group)(hx:Measurable l)
variable (a c:Cover)(k v: Fin 3)(f f':SU.F) (n m:Fin 2)
local notation "Φ" y:max=> Advance.padded G (Satin.region y N) (clothRadius G.count w)
local notation "K" b:max z:max V:max=> byMode G j Q.val M z b V
local notation "ι" i:max f:max => basisC N a i f
section waves
include hj e p ho w₀ b
private lemma ready (ζ:Nom N P) (z:Bool) (a:Cover)(i:SpinIdx)(s:SU.Slot): ‖byMode G j Q.val M ζ z (basisC N a i s)‖ ≤ spendU:=by unfold basisC; rw [map_smul,norm_smul,Lifted.winding, fee_norm,one_mul]; exact wave_here G j hj p e b w₀ ζ i _ s z M Q.val ho
lemma ready_up (ζ:Nom N P)(S U:Finset Cover)(t:nodeC a∈S)(g:Advance.padded G (Satin.region S N) (clothRadius G.count w)⊆Satin.region U P) : KeepC spendU (Satin.region U P) true (K true ζ (ι (upSpin n) (Bun k f))) := by
 let i:=Lifted.index N a (upSpin n) (Bun k f); let E:= basisC N a (upSpin n) (Bun k f); let A:=K true ζ E; let Y:=Satin.region S N
 refine ⟨ready G j hj p e Q M ho b w₀ ζ true a (upSpin n) _,?_⟩
 have hp(U':Finset (Single N))(h:i∈U'):withinM U' E:= by unfold withinM E basisC; rw [map_smul,within_basis U' _ h]
 intro l r
 have hx(Z: Finset (Single P))(h:withinM Z A):l∈Z:=by by_contra g; exact r ((within_test ..).1 h l g)
 have he:i∈modesIn N Y:=(modes_at ..).2 (node_of N a ▸ mem_image_of_mem _ t)
 have H':i∈Tset N:=(Window.mem_Tset ..).2 (up_half _)
 exact ⟨modes_monotone g (hx _ (mode_support G j Q.val M p Y b (hp _ he) true)), hx _ (byMode_species false G j Q M p b (hp _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)) true), if_pos rfl ▸ hx _ (carried_up G j Q.val M p _ true (hp _ H'))⟩
lemma ready_dn (ζ:Nom N P) (S U:Finset Cover)(t:nodeC a∈S)(g:Advance.padded G (Satin.region S N) (clothRadius G.count w)⊆Satin.region U P) : KeepC spendU (Satin.region U P) false (K false ζ (ι (dnSpin n) (Bun k f))) := by
 let i:=Lifted.index N a (dnSpin n) (Bun k f); let E:= basisC N a (dnSpin n) (Bun k f); let A:=K false ζ E; let Y:=Satin.region S N
 refine ⟨ready G j hj p e Q M ho b w₀ ζ false a (dnSpin n) _,?_⟩
 have hp(U':Finset (Single N))(h:i∈U'):withinM U' E:= by unfold withinM E basisC; rw [map_smul,within_basis U' _ h]
 intro l r
 have hx(Z: Finset (Single P))(h:withinM Z A):l∈Z:=by by_contra g; exact r ((within_test ..).1 h l g)
 have he:i∈modesIn N Y:=(modes_at ..).2 (node_of N a ▸ mem_image_of_mem _ t)
 have H':i∈(Tset N)ᶜ:= mem_compl.mpr (fun t=> dn_half _ ((Window.mem_Tset ..).1 t))
 refine ⟨modes_monotone g (hx _ (mode_support G j Q.val M p Y b (hp _ he) false)), hx _ (byMode_species false G j Q M p b (hp _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)) false),by simp only [Bool.false_eq_true,↓reduceIte]; exact hx _ (carried_down G j Q.val M p _ false (hp _ H'))⟩
#print axioms ready_up
end waves
end Xara
end YM.CF.Buffered.Afterglow.Six
