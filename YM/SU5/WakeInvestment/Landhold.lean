import SatinThinSkating
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Pannier.Chancel.Rous
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Hill.Box Hill.Post Graph Next.Rank Tree BPress.Spin
open scoped Classical
open Font
variable {j w k:ℕ}{n:Side} {γ t s u v δ δ' η τ ε a:ℝ}{r:Side} {A: Orbit n→Pane n}
def Tiny (S:Support (More n))(U:Pane n)(v:ℝ) : Prop := ∀ (i:Edge (Site (More n))), i.1∈S→ i.1+Lattice.step i.2∈ S → SU.group.chord (U i)≤ v
lemma Tiny.raise {T V : Support (More n)}{U:Pane n}(p:Tiny T U s)(q:V⊆ T)(e:s≤ t) : Tiny V U t:=fun i w v=>(p i (q w) (q v)).trans e
-- actual Pole. Lens pays `G_*g'` tilt. Thus must check prospects on first-Pane in the lighting
-- of that g', namely atFrame, not a unit chosen from G or after enumeration of the stationary points.
lemma ballot_old(r:Side) (h:0 ≤ t)(U:Pane n): Tiny (iceland r 0 U t) (Lattice.gauge (metroFrame r U) U) (4*r.val*t) :=by
 intro i px _; let W:= columbia r (More n); let G:= W.foldAt U; let L:= gauge G U; let T:=menu U t
 have he:Light r T 1 i.1:= (mem_filter.mp px).2
 have hP:Light r (menu L t) 1 i.1:=by rw [show menu L t=T from ?_]; exact he; unfold L T Hill.Box.menu; simp only [face_gauge,Gauge.chord_conj]
 have hl: ∃ V:W.Slice SU.group, L=W.drape V := by
    let f:W.Slice SU.group:=fun i=> L i.val; refine ⟨f,funext fun i=>?_⟩; by_cases w:i∈W.trunks; · have hp':L i=1:=W.compress U i w; exact hp'.trans (W.on_tree f ⟨i,w⟩).symm
    exact (W.off_tree f ⟨i,w⟩).symm
 obtain ⟨j,u⟩:=hl; exact hP.link j u i.2 h

def shoreline (t:ℝ)(r:Side) (k:ℕ) (A:Orbit n→Pane n) (X:Orbit n):= iceland r 0 (A X) t \ Lattice.halo k (flags t X.1)

lemma near_lamp (t:ℝ)(r:Side)(p:Roof n u δ k A)(h:0≤t)(l:t ≤u)(X:Orbit n): Tiny (shoreline t r k A X) (gauge (metroFrame r (A X)) X.1) (4*r.val*t):= by
 let F:=A X; let S:= shoreline t r k A X; let B:= flags t X.1
 have hv:Disjoint (Lattice.halo k S) B:=by
    apply disjoint_left.mpr; intro i e t; obtain ⟨j,u,v⟩:=halo_spec.mp e; exact (mem_sdiff.mp u).2 (halo_spec.mpr ⟨i,t,(separation_comm ..).trans_le v⟩)
 have H:= fledged p S X l hv
 intro i hi hp; unfold Lattice.gauge; rw [← H i hi hp]; exact ballot_old r h F i ((mem_sdiff.mp hi).1) ((mem_sdiff.mp hp).1)

abbrev shoreDust (k:ℕ)(r:Side):ℝ:= (4*((k+4)*2+1)^4*(Fintype.card PlaqAxes)*r.val^4+4*(k+k+1)^4:ℕ)
abbrev soreFoot(t:ℝ)(r:Side)(k:ℕ)(X:Pane n):= (24/r.val:ℝ)*((More n).val:ℝ)^4 + shoreDust k r*flakes t X
private lemma shoreWh (N r: Side)(u:r.val≤ N.val) : (↑(N.val/r.val)+1:ℝ)≤ 2*(N.val:ℝ)/(r.val:ℝ):=by
 rw [le_div_iff₀ (show (0:ℝ)<↑(r.val:ℕ) from Nat.cast_pos.mpr r.property)]; have h:(↑(N.val/r.val):ℝ)*(r.val:ℝ)≤ (N.val:ℝ):=by exact_mod_cast Nat.div_mul_le_self N.val r.val
 have hv:(r.val:ℝ) ≤ (N.val:ℝ):= Nat.cast_le.mpr u; linarith only [hv,h]
lemma surcharge (p: Roof n u δ k A)(v:t≤u)(X: Orbit n)(r:Side)(he:r.val ≤ (More n).val) : ((shoreline t r k A X)ᶜ.card:ℝ) ≤ soreFoot t r k X.1:=by
 let M:= (More n).val; let T:ℝ:=M; let Y:= (M/r.val:ℕ); let S:= (roughness t X.1).card; let r':ℝ:=r.val
 have hv: (shoreline t r k A X)ᶜ.card ≤ 12*(Y+1)*1*M^3 + (S*4*((k+4)*2+1)^4*Fintype.card PlaqAxes)*r.val^4 + S*4*(k+k+1)^4 := by
    unfold shoreline; rw [compl_sdiff, himp_eq,sup_comm, sup_eq_union]
    exact (card_union_le ..).trans <| Nat.add_le_add ((countI (w:=0) (s:=t) (r:=r) _).trans (Nat.add_le_add (count_edge ..) (Nat.mul_le_mul_right _ (rough_count X p v)))) ((Corona.halo_size _ k).trans (Nat.mul_le_mul_right _ (flag_coat _ t)))
 apply (Nat.cast_le (α:=ℝ).mpr hv).trans
 have ht: (12:ℝ)*(Y+1)*(T^3) ≤ 24/r'*T^4:=by
    have h:0≤T:=Nat.cast_nonneg _; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (shoreWh _ r he) (by norm_num:(0:ℝ)≤12)) (pow_nonneg h 3)).trans_eq (by ring)
 unfold soreFoot shoreDust S T M r' flakes at *; push_cast at ht ⊢; linarith only [ht]
end YM.CF.Pannier.Chancel.Rous
