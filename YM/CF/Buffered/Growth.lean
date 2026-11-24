import YM.CF.Buffered.Flips
/-!
# Powers comparison in the rectangle family (same Ticket)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B n n' p':Side}{δ δ' δ₃:Axis→Side}{i:Axis}{ζ:TStem i}
variable {e x:ℝ} (K: Ticket m v B p e x) (Z:Badge v B) (q:Clip)(β u:ℝ)
namespace Growth
local notation "N" => n.val
local notation "A" => Saddle.printF
local notation "U" => unitTurn ζ v B
local notation "η" => fluid ζ v B
local notation "W" => Car ζ
variable (V:Traversed ζ δ n) (L:Landing δ)
variable (ζ) in
def filmQ : Film (Wet ζ v B) (Wet ζ v B) (EdgePorts ζ v B) (Wide ζ v B):= Saddle.printF K (fun w=> Z.stencil (tint w)) q β u false
-- acquire discrete measurable on these finite types. don't clash with others via type inference. use [ms] for all then specialize if available
section powers
variable [MeasurableSpace (EdgePorts ζ v B)][DiscreteMeasurableSpace (EdgePorts ζ v B)]
local notation "F" => filmQ ζ K Z q β u
local notation "P" => Batch.transfer F η η (upper ζ v B)
variable (v':0≤u)
include L v' V
lemma matched : Tendsto (fun j=> ((Kern.power (P j) (n.val/2)):ℂ)) atTop (𝓝 (prism δ K Z.reflected q β u)):=by
 let a := fun t:Fin N=> decide (t.val%2=1)
 let f(j:W):= Z.stencil (tint j); let g:= fun j:W => Badge.reflect i (f j)
 rw [Saddle.at_batch K (Z.reflected) q β u V a L v']
 refine Batch.paired _ (printF K g q β u true) _ (curve v B V) _ _ (fun i=> ?_) (backwards K f q β u false V L g (fun i w=> Badge.thus ..)) upper_v ?_
 · unfold Saddle.record a; split
   next h=> rw [show decide _=false from (show decide (i.val % 2 = 1)=false by rw [h]; decide)]; unfold filmQ; congr 1; funext p; unfold comp Badge.reflected; rw [V.pigment i p,h,if_neg (by decide)]
   next h=>
     have he : i.val % 2=1:=by omega
     rw [decide_eq_true he]; congr 1; funext p; unfold comp Badge.reflected g; rw [V.pigment i p,he,if_pos rfl, Badge.stencil_at (p:=tint_off p)]
 rw [V.own]; exact L i
lemma dim : Tendsto (fun j=> Kern.power (P j) (n.val/2)) atTop (𝓝 ‖prism δ K Z.reflected q β u‖):=(matched K Z q β u V L v').norm.congr fun i=> by simp [Real.norm_of_nonneg (Kern.power_nonneg ..)] -- tune
lemma geA : 0 ≤ prism δ K Z.reflected q β u := ge_of_tendsto' (matched K Z q β u V L v') (fun i=> by simpa [Complex.le_def] using (Kern.power_nonneg (P i) (N/2)))
variable (V':Traversed ζ δ' n') (L':Landing δ')
include V' L'
lemma monot (k:Side)(p:n'.val=k.val*n.val): ‖prism δ' K Z.reflected q β u‖ ≤ ‖prism δ K Z.reflected q β u‖^ k.val:=by
 refine le_of_tendsto_of_tendsto' (dim K Z q β u V' L' v') ((dim K Z q β u V L v').pow _) ?_
 intro x; obtain ⟨x',h⟩:= L i; rw [← V.own] at h; have he:0 < n.val:= n.property; rw [show n'.val/2=k.val*(n.val/2) from ?_]; · exact (Kern.power_monotone (P x) (by omega) k.property)
 rw [p, Nat.mul_div_assoc _ (by exact ⟨x',by omega⟩)]
lemma middle (V₃ : Traversed ζ δ₃ p') (L₃:Landing δ₃)(ht:p'.val=3*n.val)(k:ℕ)(p: n'.val=(3+2*k)*n.val) :
 ‖prism δ₃ K Z.reflected q β u‖^(k+1) ≤ ‖prism δ K Z.reflected q β u‖^k * ‖prism δ' K Z.reflected q β u‖:=by
 refine le_of_tendsto_of_tendsto' ((dim K Z q β u V₃ L₃ v').pow _) (((dim K Z q β u V L v').pow _).mul (dim K Z q β u V' L' v')) ?_; intro j
 obtain ⟨x,h⟩:= L i; rw [← V.own] at h; have he:0 < n.val:=n.property; rw [show p'.val/2=3*(n.val/2) by omega, show n'.val/2= (3+2*k)*(n.val/2) from ?_]; · exact Kern.convex_comparison (P j) (by omega) k
 rw [p,Nat.mul_div_assoc _ (by exact ⟨x,by omega⟩)]
end powers
end Growth
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Growth.matched
