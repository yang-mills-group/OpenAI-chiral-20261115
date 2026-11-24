import YM.CF.BProof.Shade.Act
/-! Basic maps for every fixed field; stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Nest Stave Gallery Function MeasureTheory Metric Filter Finset Wilson Lattice
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {n:Side}{s l q:ℕ}{u ε d a b δ θ:ℝ}
local notation "Sκ"=>Site n
local notation "Z"=> Nerve.Halo
namespace Score
variable {T:Tray (Floor q) ε}{F:Drum (rollup q T) (Floor q)} {A A':Score n q} {R R':StampB n}
variable {U V:Heads n}(W:Writ q T s l u a b δ d θ F) (B:Seal A s l b a)
abbrev localLens(M:ℕ)(i:Bones n): Support n := halo M {i.1,i.1+step i.2}
local notation "LΨ"=> make s l u T F A R
include B
lemma stencil(i:Bones n)(p:Reads (localLens (wager s l) i) A A' U V)(g:R i=R' i): make s l u T F A R U i= make s l u T F A' R' V i:=by
 have ha:=p.reduce (Mesh.fine {i.1,i.1+step i.2} (wager s l) i.1 (by simp)); have hb:=p.reduce (Mesh.fine {i.1,i.1+step i.2} (wager s l) (i.1+step i.2) (by simp))
 rw [make, make, caught_cost B ha, caught_cost B hb, open_cost B ha,open_cost B hb, p.ties i (halo_subset _ _ (by simp)) (halo_subset _ _ (by simp)), g]
lemma patch0(i:Bones n)(p:Disjoint (RG.flags u U) (localLens (wager s l) i)):LΨ U i=U i:=by
 have H(x:Sκ)(v:x∈ ({i.1,i.1+step i.2}:Support n)):caught s l u A U x:=by
    intro j g; exact p.mono_right ((reg_pay (B.mi.mom _ _ g) (show Z*l+Radius s l ≤ wager s l from by unfold wager; omega)).trans (Mesh.fine _ _ _ v))
 unfold make; rw [if_pos ⟨H _ (by simp),H _ (by simp)⟩]
omit B
open Cube
variable {m:Side} {A:Score (Cube.More m) q} {R:StampB (Cube.More m)} -- tune `More`
include W
lemma is_basic {d':ℝ} (p:14*d ≤ d'* SU.group.colorScale) (B:Seal A s l b a): Skye.Basic m (make s l u T F A R) u d' (wager s l):= ⟨turn_frame W B p, make_meas ..,fun _ i=> patch0 B i,fun V Y i h=> stencil B i ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,h⟩ rfl⟩
end Score
end YM.CF.BProof.Mesh.Shore
