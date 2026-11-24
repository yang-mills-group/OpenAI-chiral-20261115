import YM.CF.BPress.Peel.Floor
/-! VolumeB-vac. carrier prices for micro.Fee.Bands POST.SEw. same short thresholds for any family (may only need/use short improvement for near-bias primary). Include support for indicators e.g. distance <30. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch LocalH Cube Lat SU Skye Port Locale Sugar Wealth Weave House Scree Precision Pressure Next.SectorChange RG Push.SectorMeasure Sugar.Crew Grid Env Bands Vesper Hazel Hazel.Letters Net Fock Spin Spin.Paint Habitat Meadow.Frame Meadow Meadow.Tent
open scoped Topology BigOperators Classical YM.CF.BPress.Vesper Matrix Matrix.Norms.L2Operator InnerProductSpace YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
variable {N: Side}{B:BandWidth}{A: Bands (More N) B}{R: Hangar (More N)}
open Palmer Contour Along Sheet
variable {H: Sugar.Crew A} {T S E P: Seal (BlockY A R)}{i : BlockY A R}{q : A.Index}{k r:ℕ}{X: Sugar.Stage N}
namespace Spine
variable {U:Support (More N)}
abbrev mcap (U:Sugar.Stage N)(F:Sugar.Crew A)(h:ℕ):= U.W.M+(h+fundP U F)
structure ShortP (X:Sugar.Stage N)(H:Sugar.Crew A)(R:Hangar (More N))(h:ℕ):Prop where
 μWide : mcap X H h< umbra B
 μBlock : mcap X H h ≤ R.L.val
variable (vt:Locale.meets A X.W.M U)(u:Grove (Grid.field 4 (More N)) U)(p:U.card≤r)(t:ShortP X H R r)
include u p in
lemma persistent (a b:Site (More N))(v:a∈ U)(z:b∈Magnified U X H) : separation a b≤ r+ fundP X H:=by obtain ⟨b,v',z⟩:= halo_spec.mp z; exact (separation_triangle ..).trans (add_le_add ((u.lim a v _ v').le.trans p) z)
lemma lowP {a:ℕ}(p:a ≤ umbra B): a≤ Wealth.cloak B:= by unfold umbra at p; unfold Wealth.cloak; omega
include vt u p t
lemma seasonal : ∃ i:A.Index,Magnified U X H⊆ reachP i (mcap X H r):=by
 obtain ⟨x,h,i,q⟩:=vt; refine ⟨i,fun t h'=>?_⟩; exact halo_sail (A.gap i) ((zone_of_halo ..).2 q) (persistent u p _ _ h h')
lemma morning (x:Site (More N))(h:x∈U) (z:Site (More N))(v:z∈ Magnified U X H): let j:=moment A (x 0); z∈ reachP j (mcap X H r)∧ plan A R z∈ Peel.stem (plan A R x) 1 :=by
 let w:=lowP t.μWide.le; obtain ⟨i,q⟩:= seasonal vt u p t; let a:= moment_p A w (q (halo_subset _ _ h)); let g:=moment_p A w (q v); intro j; refine ⟨?_,space_tang x z (a.trans g.symm) ((persistent u p x z h v).trans ((Nat.le_add_left ..).trans t.μBlock))⟩; change z∈reachP (town A x) _; rw [a]; exact q v -- tune coherence
lemma shortBody (v:Host R H)(x: Site (More N))(h:x∈ U){n:ℕ}(y:7 ≤ n): Spine H X U (Peel.stem (plan A R x) n):=by
 let z:= town A x; let A':= Peel.stem (plan A R x) n; let a(j)(e:j∈ Magnified U X H):= morning vt u p t x h j e; have he(j)(v:j∈ Magnified U X H): Peel.stem (plan A R j) 6⊆ A':=fun i e=> stem_mid (plan A R x) y (stem_join (r:=1) (t:=6) (a j v).2 e); refine ⟨he,fun S Q H z w y'=>?_ ,fun i a0 b l e y f=>?_⟩; · apply H.stokes v.hearth v.size _ ((inside_iff ..).2 ⟨reach_m _ _ (lowP t.μWide.le) ((a _ w).1), reach_m _ _ (lowP t.μWide.le) ((a _ y').1)⟩) ((stem_mid _ (by norm_num : 1≤6)).trans (he _ w))
 exact False.elim (off_far (lt_of_lt_of_le t.μWide (by omega : umbra B≤ 2*umbra B)) ((mem_filter.mp f).2) (near_gap (a _ ((mem_filter.mp f).1)).1)) -- tune omega
omit vt u p t
variable (X H)
def magicC:=fundP X H+fundP X H+1
lemma magnified (s:Support (More N)): (Magnified s X H).card ≤ magicC H X^4 * s.card:= (Corona.halo_size s _).trans_eq (mul_comm ..)
-- bound long footprint factors with any constant hBoom.Frame.Trans.
def constant(u:ℕ):= estate u * baser
def overhead(u:ℕ):=estate u*(pacer H.n H.L H.y * magicC H X^4)
variable {X H}
lemma expenseBody (t:Rights R B H.L H.y X.W.M)(z:Host R H) (vt:Locale.meets A X.W.M U)(u:Grove (Grid.field 4 (More N)) U)(r:ℕ)(p:6≤r) : ∃ G:Seal (BlockY A R), Grove (shape A R) (halos G 6) ∧ Spine H X U (halos G 6)∧ R.L.val*(halos G 6).card ≤ constant r*R.L.val + overhead H X r*U.card :=by
 let M:= Magnified U X H; obtain ⟨G,a,h⟩:= floor_pays A R H.Z M (Wealth.halo_g _ u) t (by obtain ⟨x,v,h⟩:=vt; exact ⟨x,halo_subset _ _ v,h⟩); let V:= shape A R; have hg:= b_print A R G a.base_g 6; have hp: estate 6 ≤ estate r:=by unfold estate; gcongr
 refine ⟨G,hg.1,long_sp z a t, ((Nat.mul_le_mul_left _ hg.2).trans_eq (mul_left_comm _ (estate 6) _)).trans ?_⟩
 have hh:R.L.val*G.card ≤ baser*R.L.val + pacer H.n H.L H.y * M.card:= h; refine (Nat.mul_le_mul hp hh).trans ?_; rw [Nat.mul_add]; unfold constant overhead; rw [mul_assoc (estate r) baser, mul_assoc (estate r) (pacer H.n H.L H.y * magicC H X^4),mul_assoc (pacer H.n H.L H.y) (magicC H X^4)]; exact Nat.add_le_add le_rfl (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (magnified H X U))) -- tune hp omega
end Spine
end YM.CF.BPress.Peel
