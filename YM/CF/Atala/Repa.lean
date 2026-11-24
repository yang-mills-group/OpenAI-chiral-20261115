import YM.CF.Forge.Cote
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Atala
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
lemma coverV {U:Config G f}(i:Cell f)(t:ℝ)(h:∀ b:Bond f,b.1∈touched i → G.chord (U b) ≤ t): G.chord (faceValue U i) ≤4*t:=by
 rcases i with ⟨x,⟨⟨i,j⟩,hk⟩⟩; let a:= faceValue U (x,⟨(i,j),hk⟩); have hh:a=U (x,i)*(U (x+step i,j)*((U (x+step j,i))⁻¹*(U (x,j))⁻¹)):=by simp [a,faceValue,square,travel]; abel_nf -- tune
 change G.chord a ≤ _; rw [hh]; let z:=G.chord_triangle (U (x,i)) (U (x+step i,j)*((U (x+step j,i))⁻¹*(U (x,j))⁻¹)); refine z.trans ((add_le_add (h _ (by simp [touched,square_corners])) ((G.chord_triangle ..).trans (add_le_add (h _ (by simp [touched,square_corners])) ((G.chord_triangle ..).trans (add_le_add ?_ ?_))))).trans_eq (by ring));
 · rw [Gauge.chord_inv]; exact h _ (by simp [touched,square_corners,add_right_comm])
 rw [Gauge.chord_inv]; exact h _ (by simp [touched,square_corners])
lemma sits{F:Forest S.ratio}{i: Bond f}(h:i∈F.trunks): S.ratio.parent (i.1+step i.2)= S.ratio.parent i.1:=by
 obtain ⟨a,p,rfl⟩:=(F.trunk_mem_iff i).mp h; have hh:=F.stays a p
 cases hx:F.up a with| mk i d=>
  rw [hx] at hh
  cases d; exact hh
  simpa [Step.used,Step.vec,←sub_eq_add_neg] using hh.symm
lemma augG(g:Site c→G.El)(U:Config G c)(i:Bond f): Lattice.gauge (g∘S.ratio.parent) (replica S.ratio U) i= replica S.ratio (Lattice.gauge g U) i:=by
 unfold replica Lattice.gauge; simp only [Function.comp_apply]; split
 · next p=> simp [p]
 next p=> rw [show S.ratio.parent (i.1+step i.2) = S.ratio.parent i.1+step i.2 from ?_]; have ht:= S.ratio.parents_hop S.patch.odd_side i.1 i.2; split at ht; exact ht; contradiction
lemma dome_u {A:Stores S}{s t:Site c}(p:t∈A.dome v)(h:v+separation t s≤r): s∈A.dome r:=by obtain ⟨i,p,e⟩:=halo_spec.mp p; exact halo_spec.mpr ⟨i,p,(separation_triangle i t s).trans (by omega)⟩
lemma pay_v {A:Stores S}{o:Site c}{V:Config G c}{t:ℝ}(h:flags t V ⊆ A.place)(p:o∉ A.dome v) {y: Site c}(u:separation o y ≤ v)(l:PlaqAxes):G.chord (faceValue V (y,l))≤t:=by by_contra! k; exact p (halo_spec.mpr ⟨y,h ((flags_spec ..).mpr ⟨(y,l),Work.E01.base_touched _,k⟩),by rwa [separation_comm]⟩)
abbrev rate_x:ℝ:= 16*(2*(20:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)
-- uses only flags V local
lemma saneP (S:StepData c f)(hg:40<c.val) {V:Config G c}{A:Stores S} {a u d:ℝ} (h:flags a V ⊆ A.place)(hp:0 ≤ d)(hx:0 ≤ a) (C: Config G f)(Z:ℕ)(k:∀ b:Bond f, S.ratio.parent b.1∉ A.dome Z → ∃ x:G.Color,‖x‖ ≤ u∧ C b=G.lieExp x* replica S.ratio V b)(q:∀ x:G.Color,‖x‖≤ u→ G.chord (G.lieExp x) ≤ d) (L:Cell f)(hz:S.ratio.parent L.1∉ A.dome (Z+20)): G.chord (faceValue C L) ≤ 4*(d+rate_x*a):=by
 let o:=S.ratio.parent L.1
 obtain ⟨g,hg⟩:= Work.E08.axial_patch o V 19 20 (by decide) (show 2*20<c.val from hg) a hx (fun i p l=> pay_v h hz (p.trans (by omega)) l) -- toll defeq
 let g':=g∘S.ratio.parent; rw [← G.chord_conj (g' L.1) (faceValue C L),←face_gauge]; refine coverV _ _ fun b p=>?_
 have hh:separation o (S.ratio.parent b.1) ≤ 19 :=by have hv:=Work.E04.parent_separation S.ratio L.1 b.1; have hy:=Work.E01.sep_touched L b.1 p; unfold o; omega
 obtain ⟨x,u,he⟩:= k b (fun v=>hz (dome_u v (by rw [separation_comm]; unfold o at hh; omega)))
 rw [show Lattice.gauge g' C b=(g' b.1*G.lieExp x*(g' b.1)⁻¹)*Lattice.gauge g' (replica S.ratio V) b from ?_, show Lattice.gauge g' (replica S.ratio V) b=_ from augG _ _ b]
 · refine (G.chord_triangle ..).trans (add_le_add (by rw [Gauge.chord_conj]; exact q x u) ?_); unfold replica; split; rw [Gauge.chord_one]; unfold rate_x; positivity; exact hg _ hh
 unfold Lattice.gauge; rw [he]; group
end YM.CF.Atala
