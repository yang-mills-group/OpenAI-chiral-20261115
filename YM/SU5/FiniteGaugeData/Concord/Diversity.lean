import YM.SU5.FiniteGaugeData.Concord.StencilMeasure
/-!
# Diversity costs

Even for discontinuous W arguments in a step (upper links), on a replant every patch decision or
read in the odds and prediction on boundedly many specified links belongs to a FINITE list of
measurable functions of the same cover pair, not growing with period. For example for the frame
read this is after using dependence on the fixed Patch.reach; not asserting continuity of the
selected frame. Here we use `StepData` definition with given patch and kernel.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
variable {I J X Y Z B : Type*}

-- calculus for finite diversity of (functions)
def Cache (f:I→Y) := Set.Finite (Set.range f)

namespace Cache
variable {f:I→Y}
protected lemma congr (h:Cache f){g:I→Y}(u:∀ i,f i=g i):Cache g := (funext u) ▸ h
protected lemma re (h:Cache f)(q:J→I): Cache (f ∘ q) := h.subset (Set.range_comp_subset_range ..)
protected lemma post (h:Cache f)(g:Y→Z):Cache (g ∘ f) := by unfold Cache; rw [Set.range_comp]; exact Set.Finite.image g h
protected lemma couple {g:I→Z}(h:Cache f)(t:Cache g):Cache (fun i:I=> (f i,g i)) := by
  apply (Set.Finite.prod h t).subset; rintro _ ⟨i,rfl⟩; exact ⟨Set.mem_range_self i,Set.mem_range_self i⟩
protected lemma price₂ (u:Cache f){h:I→Z}(z:Cache h)(g:Y→Z→B):Cache (fun i:I=> g (f i) (h i)) := (u.couple z).post (Function.uncurry g)
protected lemma piSet [Finite J]{g:I→J→B}(v:∀ j,Cache (fun i=>g i j)):Cache g:=
  (Set.Finite.pi' (fun j=>show (Set.range fun i:I=> g i j).Finite from v j)).subset (by rintro _ ⟨i,rfl⟩; exact fun _=> Set.mem_range_self i)
protected lemma docket [Finite J]{g:I→X→J→B}(v:∀j,Cache (fun i x=> g i x j)):Cache g:=
  (Cache.piSet (g:=fun i j x=> g i x j) v).post (fun f x j=> f j x)
protected lemma tiny [Finite Y] : Cache f := Set.finite_univ.subset (Set.subset_univ _)
protected lemma cashbox [Fintype J] {u:I→J} (g:J→I→Y)(v:∀ j, Cache (g j)) : Cache (fun i=> g (u i) i) :=
  (Cache.piSet (g:=fun i j=>g j i) v).price₂ Cache.tiny (fun a i=> a i)

variable [MeasurableSpace X] [MeasurableSpace B]
section deal
variable [PseudoMetricSpace B][OpensMeasurableSpace B] {f:I→X→B}
protected theorem deal (v:Cache f) (u:∀ i,Measurable (f i)) {A:Set B} (h:IsCompact A)(p:∀ i x, f i x ∈ A): Deal f:=by
  letI:Fintype (Set.range f):= Set.Finite.fintype v
  have he(y:Set.range f): Deal (I:=I) (T:=fun _=> B) (fun _ : I=> y.val) := by
    obtain ⟨t,k,e⟩:= y; change Deal (T:=fun _ : I=> B) (fun _: I=> t)
    subst t; exact deal_of_one (u k) h (p k)
  exact Deal.assembly (T:=fun _ : I=> B) (fun (q:Set.range f) (_:I)=> q.val) he (Set.rangeFactorization f)
end deal
protected theorem normMenu [NormedAddCommGroup B][ProperSpace B][OpensMeasurableSpace B]{f:I→ X→B} (v:Cache f)(u:∀i,Measurable (f i)){l:ℝ}(p:0≤l)(t:∀i x,‖f i x‖≤ l): Menu f:=
  ⟨v.deal u (isCompact_closedBall 0 l) (fun i x=> Metric.mem_closedBall.mpr (by simpa using t i x)),l,p,t⟩
end Cache

section cache
variable (S : Finset Cover)(P:I→ Side)
local notation "W₀"=> PairsC
-- use both fields
lemma from_unit {s : W₀→LinksC} (a:(i:I)→Edge (Seat (P i))) :
    Cache (fun (i:I)(x:W₀)=> graft S (P i) (s x) (a i)) := by
  let B(u:Option (↥S× Axis))(x:W₀):SU.E:=u.elim 1 (fun v=> s x (v.1.val,v.2))
  apply (Set.finite_range B).subset
  rintro _ ⟨i,rfl⟩; unfold Satin.graft; by_cases p : ∃ j : ↥S, pole S (P i) j=(a i).1
  · exact ⟨some (Classical.choose p,(a i).2), funext fun x=> Eq.symm (dif_pos p)⟩
  exact ⟨none,funext fun x=> Eq.symm (dif_neg p)⟩

-- bounded lookups in a period-dependent array with finite diversity still have that diversity (explicit shape)
lemma roll {f:I→W₀→LinksC}(h:∀ k:I→ Edge Cover, Cache (fun i x=> f i x (k i))) (w:Lattice.Walk) (v:I→ Cover) : Cache (fun i x=> Lattice.travel (f i x) (v i) w) := by

  induction w generalizing v with
  | nil => exact Set.finite_range_const (c:=fun _:W₀=> (1:SU.E))
  | cons s w ih=>
    let b(i):=s.used (v i); have ht:= h b
    have hu: Cache (fun i x=>s.read (f i x) (v i)):=by
      cases u:s.neg
      · simpa only [Step.read,u,Bool.false_eq_true,↓reduceIte] using ht
      have he:= ht.post (fun v:W₀→SU.E=> fun x:W₀=> (v x)⁻¹)
      simpa only [Step.read,u,↓reduceIte, b,Function.comp_def] using he
    exact hu.price₂ (ih (fun i=>v i+s.vec)) (·*·)

-- specialize W upper to the graft on S
variable {sP : W₀ → LinksC}
local notation "upon" i:max x:max => graft S (P i) (sP x) -- local notation type implicit may trigger unused variable
-- shape for fixed patch, kernel
variable (C: Side)(T:Finset Cover)(R:Patch)(K:KernelChoices)(hK:R.Branches K SU.group)
variable (N:I→Side)(sz:∀ i,(P i).val=(N i).val*R.L.val)

def slate (i:I) : RG.StepData (More (N i)) (More (P i)) :=
  ⟨R,K,(ratio (bead N R.L P sz i)).exact_size⟩
local notation "A" i:max => slate P R K N sz i
local notation "Tx"=> Lattice.box (Push.GridApprox.reach R)
-- Need finite repertoire of restriction on ball even when using the patch on full cover
lemma restrict_cache (y:(i:I)→Seat (P i)) : Cache (fun (i:I)(x:W₀)(a : ↥(Lattice.box (Push.GridApprox.reach R)) × Axis) => expandAt (y i) (show Config SU.group _ from upon i x) (a.1.val,a.2)):= Cache.docket (fun _=> from_unit (s:=sP) S P _)
private def rev {X:Type*} [One X](u : ↥(Lattice.box (Push.GridApprox.reach R)) × Axis → X) : Edge Cover→ X:=fun e=> if h:e.1∈ Tx then u (⟨e.1,h⟩,e.2) else 1
include hK
private lemma grew (y:(i:I)→Seat (P i))(a:I→R.FrameTag):(Cache (fun i (x:W₀)=> R.frame K (expandAt (y i) (show Config SU.group _ from upon i x)) (a i))) ∧
    Cache (fun i (x:W₀)=> R.frameMass K (expandAt (y i) (show Config SU.group _ from upon i x)) (a i)):=by
  let f(i:I)(x:W₀) : CoverConfig SU.group:= expandAt (y i) (show Config SU.group _ from upon i x)
  let F(i:I)(x:W₀)(u:(Tx:Type)× Axis):= f i x (u.1.val,u.2)
  have he:Cache F:= restrict_cache (sP:=sP) S P R y
  have v(i:I)(x:W₀)(t:R.FrameTag):=
    Push.GridApprox.patch_dep R hK t (U:=rev R (F i x)) (W:=f i x) (show Agrees (Tx : Set Cover) (rev R (F i x)) (f i x) from fun e l _=> dif_pos l)
  refine ⟨Cache.congr (he.price₂ (Cache.tiny (f:=a)) (fun (f:W₀ → ((Tx:Type)× Axis → SU.E)) t x=> R.frame (G:=SU.group) K (rev R (f x)) t)) ?_, Cache.congr (he.price₂ (Cache.tiny (f:=a)) (fun (f:W₀→ ((Tx:Type) × Axis → SU.E)) t x=> R.frameMass (G:=SU.group) K (rev R (f x)) t)) ?_⟩
  · exact fun i=>funext fun x=> (v i x (a i)).1
  exact fun i=>funext fun x=> (v i x (a i)).2
private lemma con_cache (a:(i:I)→(A i).SitesChoice)(y:(i:I)→Edge (Seat (N i))) :
    Cache (Y:=W₀→R.Connector SU.group) (fun i (x:W₀)=> (A i).connector (G:=SU.group) (upon i x) (a i) (y i)):=by
  let v(i:I)(z:Seat (N i)) := (A i).ratio.embed z
  let f(i:I)(x:W₀) := expandAt (v i (y i).1) (show Config SU.group _ from upon i x)
  refine Cache.docket (g:=fun (i:I)(x:W₀) (j:R.Points)=> _ ) ?_
  intro q
  let b(i:I) := (y i).1
  let c(i:I) := b i+Lattice.step (y i).2
  have he(b:(i:I)→Seat (N i)):Cache (fun i x=> (A i).frames (G:=SU.group) (upon i x) (a i) (b i) q):= (grew (sP:=sP) S P R K hK (fun i=> v i (b i)) (fun i=> a i (b i))).1.post (fun f: W₀→R.Frame SU.group=>fun x=> f x q)
  have grow (j:I→ Edge Cover): Cache (fun i x=>f i x (j i)) := from_unit (s:=sP) S P _
  have t:Cache (fun i x=> Lattice.travel (f i x) q.val (List.replicate R.L.val (posDir (y i).2))) :=
    Cache.cashbox (u:=fun i:I=> (y i).2) (fun k i x=> Lattice.travel (f i x) q.val (List.replicate R.L.val (posDir k))) (fun k=> roll (f:=f) grow _ (fun _=>q.val))
  exact ((he b).price₂ t (·*·)).price₂ (he c) (fun u v=>u*v⁻¹)
variable (sT : Measurable sP)(p:∀ i,Tipping T (N i) C) (f:I→FramePool C T R)(u:I→BondPool C T R)
local notation "Fr" i:max =>forFrame C T (N i) (p i)
local notation "Br" i:max =>forBond C T (N i) (p i)
variable (a:(i:I)→ (slate P R K N sz i).SitesChoice)

-- avoid rewriting through changing types; kernel canonical at slate
include sT
lemma likely : Deal (fun i (x:W₀)=> foresee C T (N i) (P i) (A i) (p i) (upon i x) (a i) (u i)):=by
  let F(i:I)(x:W₀) := foresee C T (N i) (P i) (A i) (p i) (upon i x) (a i) (u i)
  have he(j:PoleL C T): Cache (fun i x=> F i x j):= (con_cache (sP:=sP) S P R K hK N sz a (fun i=> (Br i) j)).price₂ (Cache.tiny (f:=fun i:I=>u i j)) (fun q (r:R.Points)=> fun x=> R.predict (G:=SU.group) K (q x) r)
  refine Cache.deal (B:=rawF C T) (Cache.docket he) (fun i=>?_) isCompact_univ (fun _ _=> Set.mem_univ _)
  exact measurable_pi_lambda _ fun k=> (R.predict_meas (G:=SU.group) hK (u i k)).comp (((A i).connector_meas (G:=SU.group) hK (a i) ((Br i) k)).comp ((graft_b ..).comp sT))

lemma costs : Menu (fun i (x:W₀)=> offerOdds C T (N i) (P i) (A i) (p i) (upon i x) (a i) (u i)) ∧
    Menu (fun i (x:W₀)=> lensOdds C T (N i) (P i) (A i) (p i) (upon i x) (f i)):=by
  -- induct to product Menu
  have hp (X:Type) (F:X→ I→W₀→ℝ) (t:∀ i, Menu (F i)) (s:Finset X): Menu (fun (i:I)(x:W₀)=>∏ j∈s,F j i x) := by
    induction s using Finset.induction_on with
    | empty=> simpa using (Menu.cnst (I:=I) (X:=W₀) (T:=fun _=>ℝ) (fun _=>1) zero_le_one (fun _=> norm_one.le))
    | insert j s v ih=> simp_rw [prod_insert v]; exact (t j).mul ih
  let F (j:PoleL C T)(i:I)(x:W₀):= R.predictorMass K ((A i).connector (G:=SU.group) (upon i x) (a i) ((Br i) j)) (u i j)
  let H (j : (tips (porch C T):Type)) (i:I)(x:W₀):= R.frameMass K (expandAt ((A i).ratio.embed ((Fr i) j)) (show Config SU.group _ from upon i x)) (f i j)
  refine ⟨hp (PoleL C T) F (fun j=>?_) univ,hp _ H (fun j=>?_) univ⟩
  · refine ((con_cache (sP:=sP) S P R K hK N sz a (fun i=> (Br i) j)).price₂ (Cache.tiny (f:=fun i:I=>u i j)) (fun q (r:R.Points)=> fun x=> R.predictorMass (G:=SU.group) K (q x) r)).normMenu (fun i=>?_) zero_le_one ?_
    · exact (R.predictorMass_meas (G:=SU.group) (C:=K) _).comp (((A i).connector_meas (G:=SU.group) hK (a i) ((Br i) j)).comp ((graft_b ..).comp sT))
    have h(t:R.Connector SU.group) (x:R.Points): 0≤ R.predictorMass K t x:=by unfold Patch.predictorMass; split; positivity; exact R.weight_nonneg _ -- tune syntax
    intro i x; change ‖R.predictorMass K _ _‖≤1; rw [Real.norm_of_nonneg (h ..)]
    exact (single_le_sum (f:=fun x=> R.predictorMass K _ x) (fun i _=> h _ _) (mem_univ _)).trans_eq (Patch.predictorMass_sum ..)
  refine (grew (sP:=sP) S P R K hK (fun i=> (A i).ratio.embed ((Fr i) j)) (fun i=> f i j)).2.normMenu (fun i=> ?_) zero_le_one ?_
  · refine (R.frameMass_meas (G:=SU.group) _).comp ?_
    exact measurable_pi_lambda _ fun k=> (measurable_pi_apply _).comp ((graft_b ..).comp sT)
  have h(t:CoverConfig SU.group)(x:R.FrameTag):0 ≤ R.frameMass K t x := by unfold Patch.frameMass; split; positivity; split <;> positivity
  intro i x; change ‖R.frameMass K _ _‖≤1; rw [Real.norm_of_nonneg (h ..)]
  exact (single_le_sum (f:=fun x=> R.frameMass K _ x) (fun i _=> h _ _) (mem_univ _)).trans_eq (Patch.frameMass_sum _ hK _)
end cache
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.costs
