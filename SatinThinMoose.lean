import SatinThinFlakes
import YM.SU5.Selected.Dais.Rous
import YM.CF.BPress.Spin.Touches

/-! # cost of station selection in additional global columbia frame. A variant
 of craneReady (Dais.Rous); count receipts from there.
-/
set_option autoImplicit false
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
variable {j w k:ℕ}{M:Jill.Male} {n:Side} {γ t s u v δ δ' η τ ε a:ℝ}{r:Side} {A: Orbit n→Pane n}
abbrev scaleTown (r:Side)(t:ℝ):=sphereRate*(4*r.val*t)
def metroFrame (r:Side)(U:Pane n) : Seat n→SU.E := (columbia r (More n)).foldAt U
lemma scaleTown_ge (r:Side){t:ℝ}(g:0≤t): 0≤ scaleTown r t:=mul_nonneg sphereRate_cost.positive.le (mul_nonneg (by positivity) g)
lemma frame_ready (r:Side)(w:ℕ)(n:Side) (h:0 ≤ t)(U:Pane n): Rightful (Lattice.halo w (iceland r w U t)) (Lattice.gauge (metroFrame r U) U) 1 (scaleTown r t) :=by
 let W:= columbia r (More n); let G:= W.foldAt U; let L:= gauge G U; let T:=menu U t; apply (riotPort ..).mpr; intro i p; obtain ⟨x,hx,q⟩:= halo_spec.mp (mem_filter.mp p).2.1; have he:Light r T 1 i.1:= ((mem_filter.mp hx).2).sees q
 have hP:Light r (menu L t) 1 i.1:=by rw [show menu L t=T from ?_]; exact he; unfold L T Hill.Box.menu; simp only [face_gauge,Gauge.chord_conj]
 have hl: ∃ V:W.Slice SU.group, L=W.drape V := by
    let f:W.Slice SU.group:=fun i=> L i.val; refine ⟨f,funext fun i=>?_⟩; by_cases w:i∈W.trunks; · have hp':L i=1:=W.compress U i w; exact hp'.trans (W.on_tree f ⟨i,w⟩).symm
    exact (W.off_tree f ⟨i,w⟩).symm
 obtain ⟨j,u⟩:=hl; have hg:BPress.chord (L i) 1≤ 4*r.val*t:=by rw [BPress.chord.one]; exact hP.link j u i.2 h
 let Y:= L i; change ‖brand Y-brand 1‖≤_ -- tune
 have hu:=mul_le_mul_of_nonneg_left hg sphereRate_cost.positive.le; rw [Prod.norm_def]; exact max_le ((sphereRate_cost.bot ..).trans hu) ((sphereRate_cost.top ..).trans hu)
lemma frame_gate {d C s:ℝ}(W:Colts j n a C d)(c:0≤C)(t:0<d)(r:Side)(M:Tulip.Male)(p:0≤ s)(g:Roof n u δ' k A)(h:s≤u)(x: Orbit n)(w:ℕ)(ht:δ'≤d)(Z:Brace.Sparkle n δ' M j):let N:=(More n).val; let K:= (roughness s x.1).card*4*((k+4)*2+1)^4*Fintype.card PlaqAxes;
 Papyrus.Franc.revE (twist (tradew n (metroFrame r (A x))) (spar j M (A x))-spar j M (1:Pane n))≤ Fintype.card (Single n)*shortfall a C d (scaleTown r s) w + (12*(N/r.val+1)*(w+1)*N^3+K*r.val^4:ℕ)*180*(2*C):=by
 intro N K; let V:= A x; let L:= Lattice.gauge (metroFrame r V) V; have hv:= g.paid x
 rw [← Z.covary (A x) (metroFrame r (A x)) hv]; apply (raising_tickets W M L 1 (iceland r w V s) c t ((hv.cov _).shrink ht) (guard0 t.le) (scaleTown_ge r p) (frame_ready _ _ _ p V)).trans
 apply add_le_add (le_refl _) (mul_le_mul_of_nonneg_right _ (by positivity))
 let S:= iceland r w V s; have hb: ((modesIn n S)ᶜ: Finset (Single n)).card ≤ (12*(N/r.val+1)*(w+1)*N^3+K*r.val^4)*180:= (fallenB S).trans (Nat.mul_le_mul_right _ ((countI V).trans (Nat.add_le_add (count_edge ..) (Nat.mul_le_mul_right _ (rough_count x g h)))))
 exact_mod_cast hb
end YM.CF.Pannier.Chancel.Rous
#print axioms YM.CF.Pannier.Chancel.Rous.frame_gate
