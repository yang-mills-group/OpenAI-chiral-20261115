import Anomaly.Cover.Variety
import Anomaly.Ward.Foliage
import YM.SU5.FiniteGaugeData.Tapestry.Precompact
/-! unbounded matrix entries paid even variable orbits these sharply trimmed.
Menu on lists.`Contract` frame for both transport & load.G grafts -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open CF.Swell Rill
variable {I V:Type*}[MeasurableSpace V](s:Finset Cover){P: I→Side}(f:(i:I)→ V→Pane (P i))
local notation "ΦM" i:max=> P i
local notation "u"=> Σ i:I, Edge (Seat (P i))
def pageCover {I X:Type*}{N:I→Side}(F:(i:I)→X→Pane (N i)) :Prop := Shelf (fun (z:Σ i:I, Edge (Seat (N i))) x=>F z.1 x z.2)
variable (h:pageCover f)(y:∀ i,Measurable (f i))
lemma regraft {g:V→LinksC} : pageCover (fun (i:I) x=> graft s (P i) (g x)):= graftShelf s _ g (fun i:u=> i.2)
include h
lemma visor_gale (Q:(i:I)→ Sweep (P i)): pageCover (fun (i:I) x=> flashA (Q i) (f i x)):=by
 let F(j:u)(x:V):= f j.1 x (lane (Q j.1) j.2)
 have he:Shelf F:= Shelf.regroup (g:=fun j:u=>(⟨j.1,lane (Q j.1) j.2⟩:u)) h
 let g(Y:Bool×Bool)(f:SU.E):= if Y.1 then (polarT Y.2 f)⁻¹ else polarT Y.2 f
 let b(j:u): Bool×Bool:=((Q j.1).s.flip j.2.2,(Q j.1).charge)
 apply Shelf.swap (Shelf.merge (I:=u) (fun i j x=>g i (F j x)) (fun i=> he.thenDo (fun j x=>g i (j x))) b); intro j x; change g _ _=flashA (Q j.1) (f j.1 x) j.2; rw [Skye.flash]; unfold F b g; split_ifs with h l <;> simp_all only [Prod.mk.injEq,map_inv]; -- tune
lemma pageFace : Shelf (fun (i:Σ i:I,Face (Per (More (P i)))) x=> faceValue (f i.1 x) i.2):=by
 unfold faceValue
 apply travelShelf _ _ (k:=4)
 · intro b; exact Shelf.regroup (g:=fun i=>(⟨i.1,b i⟩:u)) h
 intro i; exact le_refl _
include y
lemma gates_p (ε:ℝ) : ∃ P':Satin.Deck V,P'.dark ∧ ∀ x v,P'.withZ x v →∀ i:I,∀ S:Support (More (P i)),pingS ε S (f i x) ↔ pingS ε S (f i v):=by
 let L:=Σ i:I,Face (Per (More (P i))); let Q(z:SU.E):Bool:= decide (SU.group.chord z < ε); let R(i:L)(x:V): Bool:= Q (faceValue (f i.1 x) i.2)
 have hx:Shelf R:=(pageFace f h).thenDo fun v x=> Q (v x)
 have ht:Measurable Q:=by
    have he:MeasurableSet {z|SU.group.chord z<ε}:=(isOpen_lt SU.group.continuous_chord continuous_const).measurableSet
    exact Measurable.ite he (measurable_const (a:=true)) (measurable_const (a:=false)) -- Q defeq not ite? decide
 have he(j):Measurable (R j):=ht.comp ((continuous_travel _ _).measurable.comp (y j.1)) -- tune square
 obtain ⟨m,b,M⟩:=hx.exactDeck he (fun _=>Set.toFinite _)
 refine ⟨m,b,fun x y p i S=>?_⟩; have hh(j: Face (Per (More (P i)))): SU.group.chord (faceValue (f i x) j)<ε ↔ SU.group.chord (faceValue (f i y) j)<ε:=by simpa [R,Q] using M x y p ⟨i,j⟩
 simp only [Scree.pingS,hh] -- tune
lemma pages_deal : Deal (fun (i:u) x=> profile (f i.1 x) i.2):=by
 let F(j:u)(x:V): SU.E:=f j.1 x j.2; let W(z:SU.E)(x:Bool):= if x then Tulip.brand z else star (Tulip.brand z)
 have he:Continuous W:= by
    refine continuous_pi ?_; intro i; cases i
    · exact Continuous.star Dial.spinD
    exact Dial.spinD
 have hy:Shelf F:=h; exact (hy.slight (fun i=> (measurable_pi_apply _).comp (y i.1))).post he
variable {t: Side}{a b d e:ℝ}{o:(i:I)→ Site (P i)}{K: (i:I)→ Scree.Loom (P i)}{X:(i:I)→ SOp (P i)}{D:BudgetPoint}{k r:ℕ}
variable (L:∀ i,Roof (P i) e d r (K i))(B:∀ i,Trunk (node (o i)) (X i) k a b d)(p:D.threshold ≤e)(q:k+r+10≤D.B)(a0:0 ≤ a)(d0:0<d)(b0:0≤b)
local notation "ι" i:max=> Single (P i)
-- polynomial threshold passes before Toll χ.Reorient; does not require BQueue.tf test continuity on mask!
include a0 d0 b0 L B p q
set_option maxHeartbeats 400000 in
lemma verve_t : Menu (fun i x=> traceMeter D (K i) (o i) (X i) (f i x))∧ Menu (T:=fun i=> FC (Single (P i))) (fun i x=> spinMark D (K i) (o i) (X i) (f i x,f i x)):=by
 let z(i:I)(x:V):Orbit (P i):= (f i x,Classical.arbitrary _)
 let F(i:I):= pinMatrix D (K i) (node (o i)) (X i)
 have hp(i:I)(x:V): (∑ j:ι i,∑ k:ι i,‖F i (f i x) j k‖) ≤ b:= pinMatrix_price (L i) d0 (B i) p q (z i x) a0
 have hc(ε:ℝ)(t:0<ε) : ∃ m:Satin.Deck V,m.dark ∧ ∀ x y:V, m.withZ x y → ∀ i, (∑ j:ι i,∑ k:ι i,‖(F i (f i x)-F i (f i y)) j k‖)≤ ε:=by
    let Q:= fun s=> levΦ k d s*b; have hQ:Continuous Q:=by unfold Q levΦ; fun_prop
    have hm:Tendsto Q (𝓝[>] 0) (𝓝 0):=by
       have ht:Q 0=0:=by simp [Q,levΦ]
       simpa only [ht] using ((hQ.tendsto 0).mono_left (show 𝓝[>] (0:ℝ) ≤ _ from nhdsWithin_le_nhds)) -- tune rewrite 0s
    obtain ⟨δ,u',pδ⟩:= ((hm.eventually (ge_mem_nhds t)).and self_mem_nhdsWithin).exists
    change 0<δ at pδ
    obtain ⟨g,pp,hg⟩:=pages_deal f h y δ pδ; obtain ⟨M,a,M'⟩:= gates_p f h y D.threshold
    refine ⟨(g:Finset _)∪ M,Satin.Deck.join g M pp a,fun x y v i=>?_⟩
    have h1:= hg x y (Satin.Deck.grow Finset.subset_union_left x y v); have hx:= M' x y (Satin.Deck.grow Finset.subset_union_right x y v) i (offsetMask D.B (o i)); by_cases k: pingS D.threshold (offsetMask D.B (o i)) (f i x)
    · refine (billed_menu (L i) d0 (B i) p q a0 (f i x) (f i y) k (hx.mp k) pδ.le (fun j _=>?_)).trans u'
      specialize h1 (⟨i,j⟩:u); rw [dist_eq_norm] at h1; exact h1.le
    unfold F; rw [pinMatrix, Set.indicator_of_notMem (show f i x ∉ {U| pingS _ _ U} from k), Set.indicator_of_notMem (show f i y ∉ {U|pingS _ _ U} from mt hx.mpr k)]; simpa using t.le
 refine ⟨⟨fun ε e=>?_,b,b0,fun i x=> menu_trace _ (hp i x)⟩,⟨fun ε e=>?_,b+b,by positivity,fun i x=>menu_spin _ (hp i x)⟩⟩
 · obtain ⟨m,a,h⟩:=hc (ε/3) (by linarith); refine ⟨m,a,fun x y g i=>?_⟩; rw [dist_eq_norm]; unfold traceMeter; rw [←Matrix.trace_sub]; exact lt_of_le_of_lt (menu_trace _ (h x y g i)) (by linarith)
 obtain ⟨m,a,h⟩:=hc (ε/3) (by linarith); refine ⟨m,a,fun x y g i=>?_⟩; rw [dist_eq_norm]; exact lt_of_le_of_lt (menu_Δspin _ _ (h x y g i)) (by linarith)
end YM.CF.Buffered.Afterglow.Tapestry
