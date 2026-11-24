import YM.CF.BProof.Mapping.Cover
import YM.CF.BProof.Mapping.Block

/- support grouping in deep profile. Neighbor all lookups must be paid. `raise`
 sets are at distance ≥r from faces inside band, `Stack` parts touching ≥2r
 threshold. Use Circle.deep and uniform prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping
open Lattice Finset Filter Function Grid Cube Circle Micro Angular Angular.Yard
open scoped Topology BigOperators Classical
variable {s c : Side}(Y:Yard s)
namespace Deep
variable (T:Support s)(r:ℕ)(i:Y.Index)

-- Int≥r on both ends. Equivalent det distances at most radius long (≤s/4).
def rise (x:Per s) := Y.Band i x ∧ r≤along (Y.u i) x ∧ r≤along x (Y.v i)
def IntS := univ.filter (fun x: Site s=> rise Y r i (time x))
abbrev D := Y.long/32
lemma D_le : 32*D Y≤ Y.long:=Nat.mul_div_le ..
lemma D_pos (h:32≤Y.long):0<D Y:=Nat.div_pos h (by decide)
lemma D_u (h:32≤Y.long): Y.long≤63*D Y:=by have := D_pos Y h; unfold D at *; omega
lemma climb {a b:ℕ} (v:a≤b){x:Per s} (h:rise Y b i x): rise Y a i x:=⟨h.1,v.trans h.2.1,v.trans h.2.2⟩
-- reach farther by r (incl wrap), stays in r. note along costs.
lemma climb_next {x y:Per s}{d:ℕ}(h:rise Y (r+d) i x)(p:Circle.δ x y≤d): rise Y r i y:=by
 obtain ⟨a,b,c⟩:=h; have he:=Y.before_u i a; have hu:Y.Band i y:= Circle.deep (Y.u i) x Y.long d (by omega) (by omega) (by have :=Y.count_small; have :=Y.long_lt; omega) y p; refine ⟨hu,?_⟩
 have hv:= Y.before_u i hu
 rcases (δle x _ y).1 p with hp|hp
 · have hx:= Circle.triangle (Y.u i) x y; suffices along (Y.u i) x ≤ along (Y.u i) y by omega
   have hl:= Circle.deposit (Y.u i) x y (by have :=Y.count_small; have :=Y.long_lt; omega); omega
 have hx:= Circle.triangle (Y.u i) y x; have hl:= Circle.deposit (Y.u i) y x (by have :=Y.count_small; have :=Y.long_lt; omega); omega
lemma mist {x:Per s} (a: Y.Band i x)(p:¬ rise Y r i x)(g:4*r<Y.long): Y.Hot i r x ∨ Y.Cold i r x:=by
 by_cases h:r≤along (Y.u i) x; · right; exact ⟨(lt_of_not_ge (fun q=> p ⟨a,h,q⟩)).le,a⟩
 left; exact ⟨(lt_of_not_ge h).le,a⟩
@[simp] lemma riseS (x:Site s) : x∈IntS Y r i↔ rise Y r i (time x):=by simp [IntS]
lemma lower : IntS Y r i ⊆ Y.band i:= fun x h=>mem_strip.mpr ((riseS ..).1 h).1
lemma height {j:Y.Index}{x}(d:ℕ)(h:rise Y r i x)(p:d <r)(g:2*d<Y.long): ¬ Y.Vic j d x:=by
 obtain ⟨a,b,c⟩:=h; intro q; rcases Y.vic_split j d x g q with u|u|u
 · have e:= (Y.u_part i x a).symm.trans (Y.u_part j x u.2); subst j; have hx:=u.1; omega
 · rcases Y.common i x a u with ⟨e,p⟩|⟨e,p⟩; rw [e,along_self] at b; omega; rw [e,along_self] at c; omega
 have e:= (Y.u_part i x a).symm.trans (Y.u_part (j+1) x u.2); subst i; have he:=u.1; omega
/-- components of T reaching the 2r deep zone. restricted to r zone. selected even D (not needed but convenient). -/
def Stack := (Part.parts 1 (T∩IntS Y r i)).filter fun S=> ∃ x∈ S,rise Y (2*r) i (time x)
lemma exists' (x:Site s)(p:x∈T)(h:rise Y (2*r) i (time x)): ∃ Q∈Stack Y T r i,x∈ Q:=by
 let A:= T∩IntS Y r i; have hv:x∈A:=mem_inter.mpr ⟨p,(riseS ..).2 (climb Y i (by omega) h)⟩; let X:=Part.range 1 A x; exact ⟨X,mem_filter.mpr ⟨Part.part_of hv _,x, Part.base hv,h⟩,Part.base hv⟩
lemma brings (Q:Support s)(h: Q∈Stack Y T r i): Loc Q ∧ Q⊆ T∩ IntS Y r i∧Q.Nonempty:= Part.geo (mem_filter.mp h).1
-- cost total and lower cardinal
lemma pricePart {Q:Support s}(h:Q∈Stack Y T r i)(p:Loc T)(u:¬ T⊆IntS Y r i) : r≤Q.card:=by
 obtain ⟨x,hx,v⟩:=(mem_filter.mp h).2; obtain ⟨y,hy,z,hz,a,b⟩:=Part.boundary (mem_filter.mp h).1 p u; have hv:= span_dist (brings Y T r i Q h).1 hx hy; contrapose! a; apply (riseS ..).2; apply climb_next Y r i _ ((Nat.add_le_add ((time_jump x y).trans hv.le) ((time_jump y z).trans b)) |> fun k=> (Cube.d_one_triangle _ _ _).trans k) -- radius d maybe Q.card+1
 exact climb Y i (by omega : r+(Q.card+1)≤2*r) v
lemma partialCost : ∑ q∈Stack Y T r i,q.card ≤ (T∩ IntS Y r i).card:=by
 nth_rw 1 [← Part.cost (T∩IntS Y r i) 1]; exact sum_le_sum_of_subset (filter_subset ..)
lemma attending : ∑ i:Y.Index,∑ q∈Stack Y T r i,q.card ≤ T.card:=by
 apply (sum_le_sum (fun i _=> partialCost Y T r i)).trans; rw [← card_biUnion]; apply card_le_card; apply Finset.biUnion_subset.mpr; exact fun i _=>inter_subset_left; intro i hi j hj v; exact disjoint_left.mpr fun _ a b=> v <| (Y.u_part _ _ ((riseS ..).1 (mem_inter.mp a).2).1).symm.trans (Y.u_part _ _ ((riseS ..).1 (mem_inter.mp b).2).1)
end Deep
end YM.CF.BProof.Mapping
