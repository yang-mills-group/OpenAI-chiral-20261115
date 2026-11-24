import YM.SU5.Thin.Glacier.Horizon
import YM.SU5.Thin.Cascade.Earnest
-- needed `OrbRate`: may be UNCACHED in other sandbox. document if bootstrap needed. otherwise adapt.
import YM.CF.BPress.Spin.Touches
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {a C r e:ℝ}{n m N:Side}
open Rapids BPress.Spin
open Pressure
open YM.Gleam
variable {d v:ℝ} {w l k:ℕ} {X:Scree.Loom n}{U:Orbit n}
variable {R:Lattice.Ratio m (More n)}(T:Tree.Forest R)
abbrev frilly (T:Tree.Forest R)(U: Orbit n): Seat n→SU.E:= T.foldAt U.1
lemma torso (U:Pane n) : ∃ W:T.Slice SU.group, T.drape W= Lattice.gauge (T.foldAt U) U:=by
 let V:=Lattice.gauge (T.foldAt U) U; refine ⟨fun i=> V i.val,?_⟩; funext x; by_cases h:x∈T.trunks
 · exact (T.on_tree _ ⟨x,h⟩).trans (T.compress U x h).symm
 exact T.off_tree _ ⟨x,h⟩
-- in cell qualifications. Requires no correction to Mask radius once Roof applied.
private lemma trial_in {i:Seat n}{v₀:ℕ}(p:Gleam.Safe R (broken R d U.1) v₀ i) (q:d≤v): i∉ RG.flags v U.1:=by
 -- legit p.1 gives ≤ r.count halo root using near_root
 intro x; have ht:= Gleam.legit p.1; refine Finset.disjoint_left.mp ht (?_ : i ∈ halo (R.count.val+1) {R.embed (R.parent i)}) ?_ -- order
 · exact halo_spec.mpr ⟨_, mem_singleton_self _, le_trans (near_root R rfl) (Nat.le_add_right ..)⟩
 obtain ⟨F,a,v'⟩:=(RG.flags_spec ..).1 x; exact (RG.flags_spec ..).mpr ⟨F,a,q.trans_lt v'⟩
lemma inSight {i:Seat n}(B:Roof n v r w X)(h: 0≤d)(t: d≤v)(g:2*(R.count.val+1)< (More n).val) (p:Gleam.Safe R (broken R d U.1) (l+w+1) i):Rightful (halo l {i}) (Lattice.gauge (frilly T U) (X U)) 1 (sphereRate * suitedFee R.count.val d):=by
 let A:=broken R d U.1; let V:= Lattice.gauge (frilly T U) U.1; obtain ⟨W,hX⟩:=torso T U.1; have hc:= sphereRate_cost.positive
 intro a z; let o:= node (0:Site n); let t':=v; have hp(x:Seat n)(h:x∈ Lattice.halo l {i}):Gleam.Safe R A (w+1) x:=p.shift (by have he: separation i x≤ l:=(by simpa only [halo_spec,mem_singleton, exists_eq_left] using h); omega)
 have hx:A=broken R d V:=by unfold A broken V; rw [malaise_home]
 obtain ⟨h1,h2⟩:= (mem_filter.mp z).2
 let E':= Lattice.halo l {i}; have hu:∀ x∈ ends a,x∈ E':=by intro x t; obtain ha|ha:= mem_insert.mp t; rw [ha]; exact h1; exact mem_singleton.mp ha ▸ h2 -- precedence
 have he:a.1∈ E':=h1; let H:= hp a.1 he; have ht: InHouse R (R.parent a.1) a:=safeIn H (by omega)
 have hv: SU.group.chord (V a) ≤ suitedFee R.count.val d:=by unfold V frilly; rw [←hX]; exact purified h (show R.parent a.1∉ broken R d (T.drape W) from (by rw [show T.drape W=V from hX,←hx]; exact H.1)) g ht
 have hl:X U a= U.1 a:= B.lamp U.1 U.2 a (Finset.disjoint_left.mpr fun i t0 p0=> by
    obtain ⟨u,v₁,y⟩:= halo_spec.mp p0; let J:= hp u (hu u v₁); let l:Gleam.Safe R A 0 i:= J.shift (y.trans (Nat.le_add_right ..)); exact trial_in l t t0)
 let P:= gauge (frilly T U) (X U); have hp0: P a=V a:=by unfold P V Lattice.gauge; rw [hl]
 apply (pi_norm_le_iff_of_nonneg (mul_nonneg sphereRate_cost.positive.le (by unfold suitedFee; positivity))).2; intro j
 have ht: ‖brand (V a)-brand 1‖ ≤ sphereRate * suitedFee R.count.val d:=by
    rw [Prod.norm_def]; apply (max_le (sphereRate_cost.bot (V a) 1) (sphereRate_cost.top (V a) 1)).trans; rw [BPress.chord.one]; gcongr
 -- orient profile
 change ‖(profile P a - profile 1 a) j‖ ≤ _; cases j
 · change ‖star (brand (P a))-star (brand 1)‖ ≤ _; rw [hp0,← star_sub,norm_star]; exact ht
 change ‖brand (P a)-brand 1‖ ≤_; rw [hp0]; exact ht
end YM.CF.Pannier.Chancel
