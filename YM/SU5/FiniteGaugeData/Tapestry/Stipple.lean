import YM.SU5.FiniteGaugeData.Tapestry.Catalog
import YM.Push.GRID_APPROXIMATION.KernelLocal
set_option maxHeartbeats 100000
set_option trace.profiler false
--set_option diagnostics true
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Hard branch decisions revisited. Finite catalog on **fine** inputs taken
from the patch/singlet tasks despite varying tori; use when extending the
Satin approximation to the *range* of the actual linear operators.

No continuity of selected frames or best tag in `U` is assumed. No sparse
field hypothesis on Cape or theory - sparse in this file refers to ordinary
`graft` for reading off coefficients of an advanced mark in local norm.
-/
open Push.GridApprox
variable {I:Type*}(A N:I→Side)(R:Patch)(K:KernelChoices)
    (sz:∀ i,(More (N i)).val=(A i).val*R.L.val)
    (u:R.Branches K SU.group)
    (S:Finset Cover)

abbrev equipment(i:I):StepData (A i) (More (N i)):=⟨R,K,sz i⟩
local notation "L"=> equipment A N R K sz
abbrev grafted (x:PairsC)(n:Side): Pane n:= graft S n x.1
lemma graftedM(n:Side):Measurable (fun x=>grafted S x n):=(graft_b S n).comp measurable_fst

include u
lemma branchShelf (a:(i:I)→Site (A i)) (t:I→ R.FrameTag):
    Shelf (I:=I) (fun i x=> R.frame K (expandAt ((L i).ratio.embed (a i)) (show Config SU.group _ from grafted S x (N i))) (t i)) ∧
    Shelf (fun i x=> R.frameMass K (expandAt ((L i).ratio.embed (a i)) (show Config SU.group _ from grafted S x (N i))) (t i)):=by
  let J:=↥(Lattice.box (reach R))×Axis
  let F(i:I)(x:PairsC): CoverConfig SU.group:= expandAt ((L i).ratio.embed (a i)) (grafted S x (N i))
  let H(i:I)(x:PairsC)(w:J):SU.E:= F i x (w.1,w.2)
  let G(x:J→SU.E): CoverConfig SU.group:= fun w=>if h:w.1 ∈ Lattice.box (reach R) then x (⟨w.1,h⟩,w.2) else 1
  haveI: Fintype J:= inferInstanceAs (Fintype (↥(Lattice.box (reach R))×Axis))
  have h(i:I)(x:PairsC): Agrees (Lattice.box (reach R)) (G (H i x)) (F i x):=by
    intro e v t; unfold G; rw [dif_pos (show e.1 ∈ Lattice.box (Push.GridApprox.reach R) from v)]
  have z(j:J): Shelf (fun i x=> H i x j):= graftShelf S N Prod.fst _
  have hz:Shelf H:= Shelf.tuple z
  have ha:Shelf (I:=I) (X:=PairsC) (fun i _=> t i):= Shelf.photo t fun z _=> z
  exact ⟨(hz.twain ha fun f z x=> R.frame K (G (f x)) (z x)).swap (fun i x=> (patch_dep R u _ (h i x)).1), (hz.twain ha fun f z x=> R.frameMass K (G (f x)) (z x)).swap (fun i x=> (patch_dep R u _ (h i x)).2)⟩

abbrev Ornaments (R:Patch) (n:Side):= (Site n → R.FrameTag) × (Edge (Site n)→ R.Points)
variable (t:(i:I)→ Ornaments R (A i))(e:(i:I)→Edge (Site (A i)))
include t
lemma connectorShelf : Shelf (Y:= R.Connector SU.group) fun i x=> (L i).connector (show Config SU.group _ from grafted S x (N i)) (t i).1 (e i):=by
  let a(i:I):Site (A i):=(e i).1; let b(i:I):Site (A i):=a i+Lattice.step (e i).2
  let X(i:I)(x:PairsC):Config SU.group (More (N i)):=grafted S x (N i)
  have hs(c:(i:I)→Site (A i)) (w:R.Points): Shelf (Y:=SU.E) (fun (i:I) (x:PairsC)=> (equipment A N R K sz i).frames (X i x) (t i).1 (c i) w) := by
    change Shelf fun (i:I) x=> R.frame K (expandAt ((L i).ratio.embed (c i)) (show Config SU.group _ from grafted S x (N i))) ((t i).1 (c i)) w
    exact (branchShelf A N R K sz u S c (fun i=> (t i).1 (c i))).1.thenDo (fun f x=> f x w)
  apply Shelf.tuple; intro w
  let p(i:I):Walk:=List.replicate R.L.val (posDir (e i).2)
  let q(i:I):Seat (N i):= wrap (More (N i)) w.val + (L i).ratio.embed (a i) -- may w inferred L patch defeq?
  have h:Shelf (fun i x=> travel (X i x) (q i) (p i)):= travelShelf N X (fun e=>graftShelf S N Prod.fst e) q p R.L.val (fun i=>by simp [p])
  apply (((hs a w).twain h (fun f g x=> f x * g x)).twain (hs b w) (fun f g x=> f x*(g x)⁻¹)).swap
  intro i x; dsimp only; rw [StepData.connector,travel_at]
lemma predicts : Shelf fun i x=> (L i).prediction (show Config SU.group _ from grafted S x (N i)) (t i) (e i) := by
  refine (connectorShelf A N R K sz u S t e).twain (Shelf.photo (X:=PairsC) (J:= ↥(R.sites)) (fun i=>(t i).2 (e i)) (fun v _=>v)) (fun f g x=> R.predict K (f x) (g x))
lemma predictor_weight : Shelf fun i x=> R.predictorMass K ((L i).connector (show Config SU.group _ from grafted S x (N i)) (t i).1 (e i)) ((t i).2 (e i)) := by
  refine (connectorShelf A N R K sz u S t e).twain (Shelf.photo (X:=PairsC) (J:= ↥(R.sites)) (fun i=>(t i).2 (e i)) (fun v _=>v)) (fun f g x=> R.predictorMass K (f x) (g x))

omit t
lemma flatFrame (a:(i:I)→Site (A i))(t:I→ R.FrameTag) :
    let F(i:I)(x:PairsC):= R.frameMass K (expandAt ((L i).ratio.embed (a i)) (show Config SU.group _ from grafted S x (N i))) (t i)
    ∃ P:Deck PairsC, P.dark∧∀ x y,P.withZ x y→∀ i,F i x= F i y:=by
  intro F
  refine Shelf.exactDeck (f:=F) (branchShelf A N R K sz u S a t).2 (fun i=>?_) fun i=>?_
  · refine (Patch.frameMass_meas (G:=SU.group) R (C:=K) (t i)).comp ?_
    exact (Continuous.measurable (f:=fun x:Pane (N i)=> expandAt ((L i).ratio.embed (a i)) x)
      (continuous_pi fun v=> continuous_apply _)).comp (graftedM S (N i))
  let Q:=Set.range (fun s:Finset R.FrameTag=> (s.card:ℝ)⁻¹)
  refine ((Set.finite_range (fun s:Finset R.FrameTag=> (s.card:ℝ)⁻¹)).insert 0).subset ?_
  rintro _ ⟨x,rfl⟩; unfold F Patch.frameMass; split
  · apply Set.mem_insert_of_mem; exact ⟨univ,by simp only [card_univ]⟩
  split
  · apply Set.mem_insert_of_mem; exact Set.mem_range_self _
  exact Set.mem_insert ..
include t
lemma flatPredictor :
    let F(i:I)(x:PairsC):= R.predictorMass K ((L i).connector (show Config SU.group _ from grafted S x (N i)) (t i).1 (e i)) ((t i).2 (e i))
    ∃ P:Deck PairsC, P.dark∧∀ x y,P.withZ x y→∀ i,F i x=F i y:=by
  intro F
  apply Shelf.exactDeck (f:=F) (predictor_weight A N R K sz u S t e) (fun i=>?_); swap
  · refine (R.predictorMass_meas _).comp (((L i).connector_meas u _ _).comp (graftedM S (N i))) -- tune implicit
  intro i; let a:R.Points:= (t i).2 (e i)
  refine ((Set.finite_singleton (R.weight a)).insert (Fintype.card R.Points:ℝ)⁻¹).subset ?_; rintro _ ⟨x,rfl⟩; unfold F Patch.predictorMass; split
  · exact Set.mem_insert ..
  apply Set.mem_insert_of_mem; rfl
lemma strandsDeal : Deal (X:=PairsC) (T:=fun _:I=>SU.E) (fun i x=> (L i).prediction (grafted S x (N i)) (t i) (e i)) := Shelf.slight (predicts A N R K sz u S t e) fun i=> (measurable_pi_apply _).comp (((L i).prediction_meas u (t i)).comp (graftedM S (N i)))
omit t
-- exact matches across fields of any one torus, including predictor and frame tag WEIGHTS at all links/sites simultaneously!
lemma likelihood_deck : ∃ P:Deck PairsC,P.dark ∧ ∀ x y, P.withZ x y→∀ i, ∀ t:Ornaments R (A i),
    (L i).likelihood (show Config SU.group _ from grafted S x (N i)) t=(L i).likelihood (show Config SU.group _ from grafted S y (N i)) t:=by
  let J:= Σ i:I,Ornaments R (A i) × Site (A i); let V:= Σ i:I,Ornaments R (A i) × Edge (Site (A i)); let p:J→I:= fun i=>i.fst; let ν:V→I:=fun i=>i.fst
  obtain ⟨F,f,W⟩:= flatFrame (A∘p) (N∘p) R K (fun j=> sz (p j)) u S (fun j=>j.2.2) (fun j=> j.2.1.1 j.2.2)
  obtain ⟨G,g,H⟩:= flatPredictor (A∘ν) (N∘ν) R K (fun i=>sz (ν i)) u S (fun i=>i.2.1) (fun i=>i.2.2)
  refine ⟨(F:Finset _)∪G,F.join G f g, fun x y a i t=>?_⟩
  have hw:= W x y (Deck.grow Finset.subset_union_left x y a)
  have h:= H x y (Deck.grow Finset.subset_union_right x y a)
  unfold StepData.likelihood; exact congrArg₂ (·*·) (prod_congr rfl fun s _=> hw ⟨i,t,s⟩) (prod_congr rfl fun s _=>h ⟨i,t,s⟩)
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.likelihood_deck
