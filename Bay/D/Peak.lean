import Bay.D.Gannet
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Resonance Brecht Circuit
open CF.Onyx CF.Ember
open Stationary (Gaia)
open Maxwell

/- all posed probes with displacement vectors differing by \(R\) gauge units;
    effective seat displacement can be boundedly different. -/
variable {N:Side}

abbrev spireAxis(R:ℕ):Cover:= R • (Lattice.step 3:Cover)
variable {m k R:ℕ}{o b c:Site (More N)}
structure Bore (M:Side)(m k R:ℕ)(o b c:Site M):Prop where
 moored: pdist o≤3
 aligned:b-c=wrap M (spireAxis R)
 remote:(2*((k:ℝ)+12))*meander m≤ R
 fine:R* Ember.pinch M ≤ (meander m)⁻¹
variable {i j:Cella (More N)}
lemma liftable(h:Bore (More N) m k R o b c)(e:i∈ Lagoon k o):
   pdist i.1 ≤ k+6:=by
 obtain ⟨v,g,l⟩:=halo_spec.mp (mem_product.mp e).1
 replace g:=mem_singleton.mp g
 rw[g,separation_comm] at l
 rw [←sub_add_cancel i.1 o]
 exact (pdist_triangle ..).trans (by
    change pdist (i.1-o)≤ _ at l; have:=h.moored;omega)
lemma cover_le{x:Site (More N)}{D:ℕ}(p:pdist x≤D)(a:Axis): |(Lattice.lift x a:ℝ)|≤D:=by
 exact_mod_cast (show |Lattice.lift x a|≤ (D:ℤ) from by
   simpa using (show ((Lattice.lift x a).natAbs:ℤ)≤D from by exact_mod_cast (component_le x a).trans p))

lemma rud_le(a:Axis)(F:PlaqAxes): |(rudder F a:ℝ)|≤1:=by
 by_cases h:F.val.2=3
 · simp [rudder,h];split <;> norm_num
 simp [rudder,h]
lemma sX (R:ℕ)(z:Cover)(a:Axis)(t:(0:ℝ)<R):
   riseX R (spireAxis R + z) a - latX a = z a / (R:ℝ):=by
 change (( ((R • step 3:Cover)+z) a:ℤ):ℝ)/R- _=_
 rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,step_apply]
 simp [latX]
 split_ifs with h -- Pi.single
 · subst a;field_simp; ring
 simp
lemma tine_here(h:Bore (More N) m k R o b c)
   (u:i∈Lagoon k o)(v:j∈Lagoon k o):
   ∃z,Tine m (More N) R z∧ i.1+b - (abaft j.1 j.2.1+c)=wrap (More N) z:= by
 let x:= coup.act j.1
 let z:= Lattice.lift i.1-(Lattice.lift x + rudder j.2.1)
 have ht:=meander₀ m
 have g:=h.remote
 have hv: meander m ≤ R:=le_trans (le_mul_of_one_le_left ht.le (by linarith)) g
 refine ⟨spireAxis R + z,⟨hv,h.fine,fun a=>?_⟩,?_⟩
 · rw [sX _ z _ (ht.trans_le hv),abs_div,abs_of_pos (ht.trans_le hv)]
   have hx :pdist x≤k+6:=by simp only[x,pdist_invariant];exact liftable h v
   have hz : |(z a:ℝ)| ≤2*((k:ℝ)+12):=by
     have hb:=cover_le hx a

     have hc:=cover_le (liftable h u) a
     unfold z; simp only [Pi.sub_apply,Pi.add_apply, Int.cast_sub, Int.cast_add]
     push_cast at hb hc
     refine (abs_sub ..).trans (le_trans (add_le_add_right (abs_add_le _ _) _) ?_)
     linarith only [hc,hb,rud_le a j.2.1]
   rw [←one_div,div_le_div_iff₀ (ht.trans_le hv) ht,one_mul]
   exact (mul_le_mul_of_nonneg_right hz ht.le).trans g
 unfold z x abaft; rw[map_add, map_sub, map_add,wrap_lift,wrap_lift, ←h.aligned];abel

end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.tine_here
