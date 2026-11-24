import YM.SU5.Relativistic.Coraline
/-! # Concretion with caloric flags. Exact direct fields. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 590000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Papyrus.Franc.Meshy
open Function Filter NormedSpace Metric Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Rush SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered
open Lifted Pea Omelet Afterglow Satin Pannier Pannier.Chancel Pannier.Chancel.ScreeV Cliplet RG Tenant Scree Loaves
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
-- base receipt at any sufficiently large Pane, no cost-estimate on G-space before symbolic h
variable {L:List Wine}{S T:Finset Cover}{o:Cover}{N n: Side}{K δx W:ℕ}{s d C B ε η r γ:ℝ} (v:o∈ T)(H:AreaW false S L) {M:Jill.Male}
def mud (L:List Wine)(z:ℂ)(o:Cover)(T:Finset Cover)(N:Side): Cliplet N 1:=⟨terrace N T, fun _=> wrap (More N) o,false, fun F=> whisper z (tallyW L) (motet N L F)⟩
variable {z:ℂ}
private lemma backs(P Q:Op (Single N))(B:Op (Single N))(g:UNI (Single N))(x:twist g Q=P)(t:twist g B=B)(S:Support (More N))(y:twist g (Vo S)=Vo S)(F:FC (Single N)) (p:IsStarProjection P)(q:IsStarProjection Q)(b:Nought (Saber (B:=B) p K) (twist (quantU g) F) P η r (modesIn N S)): Nought (Saber (B:=B) q K) F Q η r (modesIn N S):=by
 -- subst P then specialize
 -- proof irrelevance
 have ht:twist (star g) P=Q:=by rw [←x,twist_inv]
 subst Q
 have hx':twist (star (g: UNI (Single N))) B=B:=by nth_rw 1 [←t]; rw [twist_inv]
 have hs:twist (star g) (Vo S)=Vo S:=by nth_rw 1 [←y]; rw [twist_inv]
 have h:=motz _ (star g) B P p q hx' hs _ K b; rw [show twist (quantU (star g)) (twist (quantU g) F)=F from ?_] at h; exact h
 rw [show quantU (star g)=star (quantU g) from Subtype.ext (quant_star _), twist_inv]
include v H
lemma icon (e:S⊆ T)(g:0<γ)(u:s≤d) (pB: ∀ N:Side,∀ x:Fields N,BlankT C B (whisper z (tallyW L) (motet N L x)))
    :∃ τ>(0:ℝ),∃ k w:ℕ, W+δx≤ w∧∀ N:Side,k≤N.val →∀ M:Tulip.Male,∀ t:ℝ,0≤t→t≤τ→(∀ (U:Pane N),∀ X:Fields N,Guard U d → Rightful (Lattice.halo W (terrace N T)) U 1 γ → Rightful (terrace N S) X.1 1 γ→∀ Q:IsStarProjection (spar 4 M U), Nought (Saber (B:=tickA N) Q K) (whisper z (tallyW L) (motet N L X)) (spar 4 M U) η r (modesIn N (terrace N T)))→ Brace.Sparkle N s M 4 → covariant (mud L z o T N).frame → AtSupport false (terrace N T) (mud L z o T N).frame → Crisp M K W w s t η r C B (mud L z o T N):=by
 obtain ⟨A,hv⟩:= ScreeV.long_cost T o; let P:=A+W; obtain ⟨τ,t,b⟩:= stampG_price P γ g; let a:= P+1+δx; refine ⟨τ,t,P+P+4,a,(by unfold a P; omega),fun n hx M z' he hs H' Tq hm hp=>?_⟩
 let S':=terrace n T; let C:=Lattice.halo W S'; let A0:=wrap (More n) o
 constructor
 · exact hp
 · exact Finset.mem_image_of_mem _ v
 · exact pB n
 intro x p k i V X
 let G:=stampG A0 x.1; let U:=Lattice.gauge G x.1; let U':=Lattice.gauge G x.2
 let F:=simultaneous G x; have hk:A0∈S':=Finset.mem_image_of_mem _ v
 have hz:S'⊆C:= halo_subset W _ -- tune Top
 have he:C⊆BlockP P A0:=by intro y t; obtain ⟨l,h,t⟩:= halo_spec.mp t; obtain ⟨x,e,rfl⟩:=Finset.mem_image.mp h; exact blocks_test.mpr ((separation_triangle ..).trans (Nat.add_le_add (hv _ _ e) t))
 have ha:Rightful C U 1 γ:=by
    have ht: Disjoint (BlockP (P+1) A0) (flags z' x.1):= Finset.disjoint_of_subset_left (Finset.Subset.trans (Corona.halo_mono (show P+1≤a by unfold a; omega) (Finset.singleton_subset_iff.mpr hk)) (Subset.refl _)) k
    apply Staff.rightfulInv (b z' (by linarith) hs (by change 2*(P+1)< n.val*2; omega) le_rfl A0 x.1 ht) he le_rfl -- name he shadow positivity
 have hk: Rightful C U' 1 γ:=by
    apply (riotPort ..).2; intro j h; have hy:= mem_filter.mp h; rw [show U' j=U j from (by unfold U' U Lattice.gauge; rw [i j hy.2.1 hy.2.2])]; exact (riotPort ..).1 ha _ h
 have hw:Guard U' s:=Cube.Guard.cov p _
 let M0:= Tq.projection _ hw; have hb:=H' U' F (hw.shrink u) hk (Staff.rightfulInv ha (Finset.Subset.trans (image_subset_image e) hz) le_rfl) M0
 let B:=mud L z o T n; let V':=tradew n G; let T':= B.frame x; change Nought _ (B.frame F) _ _ _ _ at hb; rw [show B.frame F= twist (quantU V') (B.frame x) from hm G x] at hb
 exact backs _ _ (tickA n) _ (Tq.covary _ _ p|>.symm) (Cascade.tick_g ..) _ (gauge_frost ..) _ M0 X hb
end YM.CF.Papyrus.Franc.Meshy
#print axioms YM.CF.Papyrus.Franc.Meshy.icon
