import YM.CF.BProof.Bias.Reel
import YM.CF.BProof.Trek.Home
/-! Construct Vent at actual bands. Aim apply only actual-layout fields. Utility
estimates with twist-time node offsets. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real Mapping Angular Hero Dream Trek
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev instant (x:Per N): Per (More N):= base (assembly N) x+1
lemma spell (x:Site N)(i:Axis): (node x) i= instant (x i):=rfl
lemma timed (x:Site N): time (node x)=instant (time x):=rfl
lemma instant_add (x:Per N)(i:ℕ): instant (x+(i:Per N))=instant x+(↑(2*i):Per (More N)):=by unfold instant; rw [base_add,base_nat,Nat.cast_mul]; rw [show (assembly N).count.val=2 from rfl]; abel -- tune
lemma δ_instant (x y:Per N): delta1 (More N) (instant x) (instant y) =2*delta1 N x y := by
 rw [instant,instant,d_shift,delta_eq, base_distance,delta_eq]; change min (2*_) ((N.val)*2-2*(along y x)) = _; omega
lemma nearest (u:Per (More N)):∃ x:Per N,∃ i≤ (1:ℕ), instant x+ i=u:=by
 let R:=assembly N; let P := part R (u-1); have h:P.val<2:=P.isLt; refine ⟨block R (u-1),P.val,(by omega),?_⟩; unfold instant; rw [add_right_comm (_:Per (More N)),show base (assembly N) (block R (u-1)) + ↑P.val=u-1 from glue_block ..]; abel
-- sets
variable (Y:Yard (More N))
def StackS := univ.filter (fun x:Per N=> dark Y (join (instant x) 0))
def bright := (StackS Y).filter (fun x=> Y.D (hr Y (join (instant x) 0)))
lemma StackS_iff {x:Site N}: x 0∈ StackS Y ↔ dark Y (node x):= by rw [StackS,mem_filter,and_iff_right (mem_univ _)]; rfl -- tune
lemma loom_s (x:Per N): x∈StackS Y↔ ∃ i:Y.Index,Y.Band i (instant x):=by
 rw [StackS,mem_filter,and_iff_right (mem_univ _)]; refine ⟨fun h=> ⟨hr Y (join (instant x) 0), mem_strip.mp (band_pick Y _ h)⟩,fun ⟨i,k⟩=> (codeB Y (mem_strip.mpr k)).1⟩
lemma loom_b {x:Per N}{i:Y.Index}(h:Y.Band i (instant x)): x∈bright Y ↔ Y.D i:=by
 rw [bright,mem_filter,and_iff_right ((loom_s ..).2 ⟨i,h⟩),(codeB Y (mem_strip.mpr h)).2]
def area (i:Y.Index)(r:ℕ):= univ.filter (fun x:Per N=> Y.Vic i r (instant x))
lemma areaT{i:Y.Index}{t:Per N}{r:ℕ}: t∈ area Y i r ↔ Y.Vic i r (instant t):=by simp [area]
lemma pinsB (c:Side)(g:Ratio c (More N)): Trek.Pins Y g ∅=rowsX (StackS Y)ᶜ:=by rw [empty_pins]; ext x; rw [mem_filter,and_iff_right (mem_univ _),row_at,mem_compl,StackS_iff]
-- growth from time t
lemma area_up (i:Y.Index)(s t v:ℕ)(q:s+2*t≤v): Extend (area Y i s) (area Y i v) t:=by
 intro x hx y g; apply (areaT Y).2; apply Y.vic_nearer _ _ _ _ q (Y.vic_trans i s _ _ (2*t) ((areaT Y).1 hx) ?_); unfold Circle.δ; rw [δ_instant,d_sym]; exact Nat.mul_le_mul_left _ ((cent_at ..).1 g)
end YM.CF.BProof.Bias
