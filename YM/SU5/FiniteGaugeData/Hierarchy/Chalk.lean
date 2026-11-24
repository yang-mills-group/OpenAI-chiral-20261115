import YM.SU5.FiniteGaugeData.Hierarchy.Dic
/-! # Finite answers to questions in the Step likelihood with a replanted finite-support link background.

Stronger than a Menu estimate. In the application `N` (and fine/coarse Choices) will vary over a Course. The same finite questions on `PairsC` work for every StepData (sizes allowed to vary, kernel an exact identity across all steps in use, cuts needn't be continuous), at every site/tag. This will allow averaging over an unbounded number of alternatives using bounded probabilities, without growing the needed Deck with volume. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra

namespace Chalk
section
variable {I J X Y Z V:Type*}
/-- Only finitely many FUNCTIONS of X as i varies. -/
def Fin (f:I→ X→ Y):Prop:= Set.Finite (Set.range f)

lemma applied {f:I→ X→ Y}(h:Fin f)(g:Y→Z):Fin (fun i x=>g (f i x)):=
  (h.image (fun v:X→Y=>g ∘ v)).subset (by rintro p ⟨i,rfl⟩; exact ⟨f i,⟨i,rfl⟩,rfl⟩)
lemma congr {f g:I→ X→ Y}(h:Fin f)(p:∀ i x,f i x=g i x):Fin g:= (funext fun i=>funext fun x=>p i x) ▸ h
lemma evalK {f:I→ X→ Y}{g:I→ X→ Z} (h:Fin f)(u:Fin g)(M:Y→ Z→ V):Fin (fun i x=> M (f i x) (g i x)):=by
  let a(F:(X→Y) × (X→Z))(x:X):= M (F.1 x) (F.2 x); exact ((h.prod u).image a).subset (by rintro s ⟨i,rfl⟩; exact ⟨(f i,g i),⟨⟨i,rfl⟩,⟨i,rfl⟩⟩,rfl⟩)
lemma post {f:I→X→Y}(h:Fin f)(e:J→I):Fin (fun i x=>f (e i) x):= h.subset (by rintro v ⟨i,rfl⟩; exact ⟨e i,rfl⟩)
lemma of_one (x:X→Y):Fin (I:=I) (fun _=> x):=(Set.finite_singleton x).subset (by rintro t ⟨_,rfl⟩; rfl)
lemma basis [Finite J](p:J→ X→ Y)(f:I→X→Y)(h:∀i, ∃ j,f i=p j): Fin f:=(Set.finite_range p).subset (by rintro v ⟨i,rfl⟩; obtain ⟨j,e⟩:= h i; exact ⟨j,e.symm⟩)
lemma casesT [Finite J](p:J→ I→ X→ Y)(h:∀j,Fin (p j))(e:I→J):Fin (fun i x=>p (e i) i x):=
 (Set.finite_iUnion h).subset (by rintro v ⟨i,rfl⟩; exact Set.mem_iUnion.mpr ⟨e i,i,rfl⟩)
lemma collect [Finite J]{V:J→Type*}{f:I→X→ ∀ i:J,V i}(h:∀i:J,Fin (fun j x=> f j x i)):Fin f:=by
  let S(i:J):=Set.range (fun j x=> f j x i)
  let A:= Set.pi Set.univ S
  have hx:A.Finite:= Set.Finite.pi (fun i=>h i)
  exact (hx.image (fun v: (j:J)→ X→ V j => fun x i=> v i x)).subset (by rintro t ⟨i,rfl⟩; exact ⟨fun j x=> f i x j,fun j _=> ⟨i,rfl⟩,rfl⟩)

section
variable [MeasurableSpace X]{f g:I→X→Y}
def flash (f:I→X→Y):Prop:= ∃ P:Deck X,P.dark ∧ ∀ x y,P.withZ x y →∀ i,f i x=f i y
lemma change {T:I→X→Y}(h:flash T)(e:J→I):flash (fun i=> T (e i)):=by
 obtain ⟨P,v,t⟩:=h; exact ⟨P,v,fun x y u i=> t x y u (e i)⟩
lemma menus [NormedAddCommGroup Y][MeasurableSpace Y][BorelSpace Y][ProperSpace Y](h:Fin f)(e:∀i,Measurable (f i)){C:ℝ}(u:0≤C)(p:∀i x,‖f i x‖≤C):Menu f:=by
 classical
 let V:= Set.range f; haveI : Fintype V := Set.Finite.fintype h
 refine ⟨?_,C,u,p⟩
 refine Deal.assembly (fun i:V=>fun _:I=>i.val) ?_ (fun i=>⟨_,⟨i,rfl⟩⟩)
 rintro ⟨_,i,rfl⟩
 exact deal_of_one (e i) (isCompact_closedBall 0 C) (fun x=>mem_closedBall_zero_iff.mpr (p i x))
lemma deals [PseudoMetricSpace Y][MeasurableSpace Y][OpensMeasurableSpace Y][CompactSpace Y](h:Fin f)(e:∀i,Measurable (f i)):Deal f:=by
 let V:= Set.range f; haveI : Fintype V:=Set.Finite.fintype h
 refine Deal.assembly (fun i:V=>fun _:I=>i.val) ?_ (fun i=>⟨_,⟨i,rfl⟩⟩); rintro ⟨_,i,rfl⟩; exact deal_of_one (e i) isCompact_univ (fun _=> Set.mem_univ _)
lemma lamp [MeasurableSpace Y] [MeasurableSingletonClass Y](h:Fin f)(m:∀i,Measurable (f i))(p:∀i,Set.Finite (Set.range (f i))):flash f:=by
 classical
 let V:= Set.range f; haveI : Fintype V := Set.Finite.fintype h; have he(i:V): Set.Finite (Set.range i.val):=i.property.elim fun j e=>e ▸ p j
 let R(i:V)(x:Y):=i.val ⁻¹' {x}; let P:Deck X:= univ.biUnion (fun i=> (he i).toFinset.image (R i)); refine ⟨P,?_,?_⟩
 · intro _ v; obtain ⟨a,t,q⟩:= mem_biUnion.mp v; obtain ⟨x,e,rfl⟩:=mem_image.mp q; rcases a with ⟨a,i,rfl⟩; exact m i (measurableSet_singleton x)
 intro x y z i; let G:V:=⟨f i,i,rfl⟩; have hg:= z _ (mem_biUnion.mpr ⟨G,mem_univ _, mem_image_of_mem (R G) ((he G).mem_toFinset.mpr ⟨x,rfl⟩)⟩)
 exact (hg.mp (show x∈ R G (f i x) from rfl)).symm
end
end
#print axioms collect

section paths
variable {I:Type*} {X:Type*} {E : I→Type*}[∀i,AddCommGroup (E i)][∀i,One (E i)]
-- flexible path travel with common bounds
variable (V:(i:I)→ X→ Links (E i) SU.E)
lemma moves (p:∀ u:(i:I)→ Edge (Four (E i)),Fin (fun i x=> V i x (u i)))(l:Walk):
    ∀ t:(i:I)→ Four (E i),Fin (fun i x=>travel (V i x) (t i) l):=by
  induction l with
  | nil=> exact fun t=> of_one (fun _:X=>(1:SU.E))
  | cons a l ih=>
    intro t; apply evalK _ (ih (fun i=> t i + a.vec)) (·*·)
    unfold Step.read
    cases h:a.neg <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact p _
    exact applied (p _) (fun v=>v⁻¹)
lemma marches (p:∀ u:(i:I)→ Edge (Four (E i)),Fin (fun i x=> V i x (u i)))(l:I→Walk)(a:Set.Finite (Set.range l))(t:(i:I)→ Four (E i)):
    Fin (fun i x=> travel (V i x) (t i) (l i)):=by
  haveI:= Set.Finite.fintype a
  exact casesT (fun (k:Set.range l) (i:I) x=> travel (V i x) (t i) k.val) (fun k=>moves V p _ t) (fun i=>⟨l i,i,rfl⟩)
end paths

section kernel
open Push.GridApprox
variable {T X:Type*}(S:Finset Cover)(N : T→ Side)(a:T→ PairsC→LinksC)
lemma graft_link {f:X→LinksC}(w:(i:T)→Edge (Seat (N i))): Fin (fun i x=> graft S (N i) (f x) (w i)):=by
  classical
  let P(k:Option (↥S × Axis))(x:X):SU.E:= match k with
   | none => 1
   | some (v,i)=> f x (v.val,i)
  apply basis P
  intro i; by_cases h:∃ p:S,pole S (N i) p=(w i).1
  · exact ⟨some (Classical.choose h,(w i).2),funext fun x=>by rw [Satin.graft,dif_pos h]⟩
  exact ⟨none,funext fun x=>by rw [Satin.graft,dif_neg h]⟩

variable (P:T→Side)(L:RG.Patch)(K:KernelChoices)(e:∀i, (More (P i)).val=(More (N i)).val*L.L.val)
abbrev pinned {n m:Side}(L:RG.Patch)(K:KernelChoices)(h:(More m).val=(More n).val*L.L.val) : StepData (More n) (More m):= ⟨L,K,h⟩
local notation "Q" => fun (i:T)=> pinned L K (e i)
local notation "𝕂" => SU.group
variable (F:(i:T)→X→Pane (P i)) (p:∀ v:(i:T)→Edge (Seat (P i)), Fin (fun i x=> F i x (v i)))
variable (b:L.Branches K SU.group) (w:(i:T)→ (pinned L K (e i)).SitesChoice)(g:(i:T)→ Edge (Seat (N i)))
private def priv (u: Patch)(v: (Lattice.box (reach u):Type)× Axis→ SU.E):CoverConfig SU.group:= fun e=> if h:e.1∈Lattice.box (reach u) then v (⟨e.1,h⟩,e.2) else 1
include p
private lemma config_f (a:(i:T)→ Seat (N i)) (z:Edge Cover) :
    Fin (fun i x=> expandAt (((Q) i).ratio.embed (a i)) (F i x) z):= p _
include b
private lemma frame_f (a:(i:T)→ Seat (N i)) (z:(i:T)→L.FrameTag) :
    let u(i:T) (x:X):CoverConfig SU.group := expandAt (((Q) i).ratio.embed (a i)) (F i x)
    Fin (fun i x=> L.frame K (u i x) (z i)) ∧ Fin (fun i x=>L.frameMass K (u i x) (z i)):=by
  intro u
  let C:Finset Cover:= Lattice.box (reach L)
  let k(i:T)(x:X)(z:↥C × Axis):SU.E := u i x (z.1.val,z.2)
  have hk: Fin k:=collect fun z=> config_f N P L K e F p a _
  have he:=applied hk (priv L)
  have hp(i:T)(x:X)(z:L.FrameTag):L.frame K (priv L (k i x)) z=L.frame K (u i x) z ∧ L.frameMass K (priv L (k i x)) z=L.frameMass K (u i x) z:=by
    apply patch_dep L b
    intro j t _; rw [priv,dif_pos (show j.1 ∈ Lattice.box (reach L) from t)]
  exact ⟨congr (casesT _ (fun (j:L.FrameTag)=> applied he (fun v=>L.frame K v j)) z) (fun i x=> (hp i x (z i)).1), congr (casesT _ (fun (j:L.FrameTag)=> applied he (fun v=>L.frameMass K v j)) z) (fun i x=> (hp i x (z i)).2)⟩
private lemma connector_f : Fin (Y:= L.Connector SU.group) (fun i x=> ((Q) i).connector (F i x) (w i) (g i): T→ X→ L.Connector SU.group):=by
  let y(i:T):= g i|>.1; let z(i:T):= y i+step (g i).2
  let U(i:T)(x:X):CoverConfig SU.group:= expandAt (((Q) i).ratio.embed (y i)) (F i x)
  have hp :∀ v:T→Edge Cover, Fin (fun i x=> U i x (v i)):= fun v=> p _
  refine collect (V:=fun _ : L.Points => SU.group.El) (f:=fun (i:T) x v=> ((Q) i).connector (F i x) (w i) (g i) v) ?_
  intro v
  refine evalK (evalK (applied ((frame_f N P L K e F p b y (fun i=> w i (y i))).1) (fun x=>x v)) ?_ (fun (x y:SU.E)=> x*y)) (applied (frame_f N P L K e F p b z (fun i=> w i (z i))).1 (fun x=> x v)) (fun x y=> x * y⁻¹)
  exact casesT _ (fun j:Axis=> moves U hp (List.replicate L.L.val (posDir j)) (fun _=> v.val)) (fun i=> (g i).2)

lemma predicts (w:(i:T)→ (pinned L K (e i)).Choices) : Fin (fun i x=> ((Q) i).prediction (F i x) (w i) (g i)) :=
by
  apply casesT (fun (j:L.Points) (i:T) x=>L.predict K (((Q) i).connector (F i x) (w i).1 (g i)) j) _ (fun i=>(w i).2 (g i))
  exact fun j=> applied (connector_f N P L K e F p b (fun i=>(w i).1) g) (fun x=> L.predict K x j)
#print axioms predicts

section
variable [MeasurableSpace X](M:∀i,Measurable (F i))(U:(i:T)→(pinned L K (e i)).Choices)
include p b M
lemma frameLight (a:(i:T)→ Seat (N i)) : flash (fun i x=> ((Q) i).patch.frameMass K (expandAt (((Q) i).ratio.embed (a i)) (show Config SU.group _ from (F i x))) ((U i).1 (a i))) := by
  classical
  let V(i:T)(x:X):CoverConfig SU.group:= expandAt (((Q) i).ratio.embed (a i)) (F i x)
  let t(i:T): L.FrameTag:= (U i).1 (a i)
  apply lamp (f:=fun i x=>L.frameMass K (V i x) (t i)) ((frame_f N P L K e F p b a t).2)
  · intro i; refine (L.frameMass_meas (G:=SU.group) (C:=K) (t i)).comp ?_; unfold V; apply measurable_pi_lambda; intro p; exact (measurable_pi_apply _).comp (M i)
  intro i
  let A: Set ℝ := {(Fintype.card L.FrameTag:ℝ)⁻¹,(0:ℝ)}
  refine (((show A.Finite from Set.Finite.insert _ (Set.finite_singleton _))).union (Set.finite_range (fun z:Finset L.FrameTag=> (z.card:ℝ)⁻¹))).subset ?_
  rintro r ⟨x,rfl⟩; unfold Patch.frameMass; dsimp only; split
  next u=> exact Or.inl (by simp [A])
  split
  next u=> exact Or.inr ⟨_,rfl⟩
  exact Or.inl (by simp [A])

lemma predLight : flash (fun i x=> L.predictorMass K (((Q) i).connector (F i x) (U i).1 (g i)) ((U i).2 (g i))) := by
  classical
  let V(i:T)(x:X):L.Connector SU.group:= ((Q) i).connector (F i x) (U i).1 (g i)
  let t(i:T):L.Points:=(U i).2 (g i)
  refine lamp (f:=fun i x=> L.predictorMass K (V i x) (t i)) (casesT (fun (v:L.Points) i x=> L.predictorMass K (V i x) v) ?_ t) ?_ ?_
  · intro v; exact applied (connector_f N P L K e F p b (fun i=>(U i).1) g) (fun x=> L.predictorMass K x v)
  · intro i; exact (L.predictorMass_meas (C:=K) _).comp ((((Q) i).connector_meas b (U i).1 (g i)).comp (M i))
  intro i; refine (Set.Finite.insert ((Fintype.card L.Points:ℝ)⁻¹) (Set.finite_range L.weight)).subset ?_; rintro t ⟨x,rfl⟩; unfold Patch.predictorMass; dsimp only; split
  next u=> exact Or.inl rfl
  exact Or.inr ⟨_,rfl⟩

omit p
-- `D`: branch-space probability determined exactly by common answers, including for zero-prob choices.
lemma commonLight (D : Fin (fun (i:Σ j:T,Edge (Seat (P j))) x => F i.1 x i.2)) :
    flash (fun i x=> ((Q) i).likelihood (F i x) (U i)) := by
  let A:= Σ i:T,Edge (Seat (N i)); let B:= Σ i:T, Seat (N i)
  obtain ⟨d,h,k⟩:= frameLight (fun i:B=> N i.1) (fun i:B=> P i.1) L K (fun i=>e i.1) (fun i x=> F i.1 x) (fun v=>post D (fun i:B=>⟨i.1,v i⟩)) b (fun i=> M i.1) (fun i=> U i.1) Sigma.snd
  obtain ⟨u,m,q⟩:= predLight (fun i:A=> N i.1) (fun i:A=> P i.1) L K (fun i=> e i.1) (fun i x=> F i.1 x) (fun v=> post D (fun i:A=>⟨i.1,v i⟩)) b Sigma.snd (fun i=> M i.1) (fun i=> U i.1)
  classical
  refine ⟨(d:Finset (Set X))∪u,Deck.join d u h m,fun x y t i=>?_⟩; unfold StepData.likelihood; apply congrArg₂ (fun (x y:ℝ)=>x*y)
  · exact prod_congr rfl fun a _=> k x y (Deck.grow subset_union_left x y t) ⟨i,a⟩
  exact prod_congr rfl fun a _=> q x y (Deck.grow subset_union_right x y t) ⟨i,a⟩
#print axioms commonLight
end
end kernel
end Chalk
end YM.CF.Buffered.Afterglow.Hierarchy
