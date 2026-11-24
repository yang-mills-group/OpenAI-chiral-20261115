import YM.SU5.FiniteGaugeData.Marked.Variation.Public
/-!
# Local account of the *upper* dependence of a step, without aligning all bare schedules

Compress the *actual* likelihood mixture at insertions, rather than making a continuity
assumption on running prediction or stabilization of laws. Formula on a common local index set.
(The notation `stretch` is indexed by the porch, not by the tips.)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin Mail.Radiant
open VolumeCape VolumeCape.Atlas VolumeCape.Read
attribute [local instance] opCStarAlgebra

section sum
-- analogue of `Radiant.countMP` for Banach-valued predictions
variable {I J X V : Type*}[Fintype I][Fintype J]
variable (e:I↪J)(q:J→ X→ℝ) [AddCommGroup V][Module ℝ V]

private lemma comps_ext (x:I→X)(y:other e→X) : mapa e X (x,y) ∘ e = x := by
  funext i; unfold mapa; dsimp only [Function.comp_apply, Equiv.trans_apply]
  nth_rw 1 [← key_in]; rw [Equiv.piCongrLeft_apply_apply]; rfl
private lemma sums_t_real [Fintype (other e)] (x:I→X)(y:other e→X) :
    ∏ i,q i (mapa e X (x,y) i)=(∏ i,q (e i) (x i))*∏ i:other e,q i.val (y i):=by
  rw [← Equiv.prod_comp (keysZ e) (fun i=> q i (mapa e X (x,y) i)),Fintype.prod_sum_type]
  unfold mapa; simp_rw [Equiv.trans_apply,Equiv.piCongrLeft_apply_apply,key_in,key_out]; rfl

variable {q}
-- careful of multiple fintype PI TC if arguments not definitionally equal
private lemma compression [Fintype X][DecidableEq I][DecidableEq J] (g:(I→X)→V)
    (h:(J→X)→V)(p:∀ x,h x=g (x∘e))(v:∀j,∑ x,q j x=1) :
    (∑ x:J→X,(∏ i,q i (x i)) • h x) = ∑ x:I→X,(∏ i,q (e i) (x i)) • g x := by
  rw [← Equiv.sum_comp (mapa e X), Fintype.sum_prod_type]
  refine sum_congr rfl fun i _=>?_
  simp_rw [p, comps_ext e, sums_t_real e q]; rw [←sum_smul,←mul_sum,
    ←Fintype.prod_sum (fun i : other e=> q i.val)]; simp [v]

omit [Fintype I] [Fintype J] in
def occupyFn [Nonempty X] (p:I→X) : J→X := Function.extend e p (fun _=> Classical.arbitrary X)

omit [Fintype I] [Fintype J] in
lemma occupyFn_comp [Nonempty X](p:I→X) : occupyFn e p ∘ e = p := by
  unfold occupyFn; exact Function.extend_comp e.injective p _
end sum

section neighbor
variable (C : Side)(T:Finset Cover) (n P:Side)(A : RG.StepData (More n) (More P))
variable (B : A.patch.Branches A.kernel SU.group)
variable (p : Tipping T n C)

def forFrame : (tips (porch C T) : Type) ↪ Seat n :=
  ⟨pole (tips (porch C T)) n,fun x y t=> Subtype.ext (p x.property y.property t)⟩
def forBond : PoleL C T ↪ Edge (Seat n) :=⟨stretch (porch C T) n,inject_stretch T n C p⟩

local notation "fF"=> forFrame C T n p
local notation "fB"=> forBond C T n p

abbrev FramePool (Q:Patch) := (tips (porch C T) : Type) → Q.FrameTag
abbrev BondPool (Q:Patch) := PoleL C T → Q.Points

def offerOdds (W: Pane P) (a:A.SitesChoice) (b:BondPool C T A.patch) := ∏ i:PoleL C T,
  A.patch.predictorMass A.kernel (A.connector (G:=SU.group) W a (fB i)) (b i)

def lensOdds (W: Pane P) (b:FramePool C T A.patch) := ∏ i:(tips (porch C T) : Type),
  A.patch.frameMass A.kernel (expandAt (A.ratio.embed (fF i)) (show Config SU.group _ from W)) (b i)

def foresee (W : Pane P)(a:A.SitesChoice)(b:BondPool C T A.patch) : rawF C T :=
  fun i => A.patch.predict A.kernel (A.connector (G:=SU.group) W a (fB i)) (b i)

include B
private lemma agrees_choices {a b:A.SitesChoice} (W: Pane P)(i : PoleL C T) (v:a∘fF=b∘fF) :
    A.connector (G:=SU.group) W a (fB i)=A.connector (G:=SU.group) W b (fB i) := by
  obtain ⟨x,i⟩ := i
  refine Push.GridApprox.connector_dep A B _ a b ?_ ?_ (fun _ _ _=> rfl) (fun _ _ _=> rfl)
  · exact congrFun v ⟨x.val, tips_here _ x.property⟩
  have he : (fB (x,i)).1 + Lattice.step (fB (x,i)).2 = fF ⟨x.val + Lattice.step i, tips_there _ x.property i⟩ := by
    change wrap (More n) x.val + step i = wrap (More n) (x.val + Lattice.step i); rw [map_add,wrap_step]
  rw [he]; exact congrFun v _
variable {V:Type*} [AddCommGroup V][Module ℝ V]
-- DECK independent sizes of A/S. Prediction and odds are functions of X itself, no regularity purchase.
theorem condense (W : Pane P) (g : rawF C T → V) :
    (∑ i:A.Choices, A.likelihood (G:=SU.group) W i • g (A.prediction (G:=SU.group) W i ∘ stretch (porch C T) n)) =
    ∑ x:FramePool C T A.patch, lensOdds C T n P A p W x • (∑ v:BondPool C T A.patch,
      offerOdds C T n P A p W (occupyFn fF x) v • g (foresee C T n P A p W (occupyFn fF x) v)) := by
  let y(i:A.SitesChoice)(j:Edge (Seat n))(u:A.patch.Points):= A.patch.predictorMass A.kernel (A.connector (G:=SU.group) W i j) u
  let v(s:Seat n)(x:A.patch.FrameTag):= A.patch.frameMass A.kernel (expandAt (A.ratio.embed s) (show Config SU.group (More P) from W)) x
  let F(i:A.SitesChoice) : V:=∑ v': BondPool C T A.patch, offerOdds C T n P A p W i v' • g (foresee C T n P A p W i v')
  let G(i:A.SitesChoice)(j:A.BondChoice):= g (A.prediction (G:=SU.group) W (i,j) ∘ fB)
  have he(i:A.SitesChoice) : (∑ x:A.BondChoice, (∏ j,y i j (x j)) • G i x) = F i :=
    compression fB (fun v'=>g (foresee C T n P A p W i v')) (G i) (fun _=>rfl) (fun j=>Patch.predictorMass_sum ..)
  let U := fun x:FramePool C T A.patch=> F (occupyFn fF x)
  have hx(i:A.SitesChoice) : F i = U (i∘fF) := by
    unfold U F; apply sum_congr rfl; intro b _
    have t(j:PoleL C T):= agrees_choices C T n P A B p W j (occupyFn_comp fF (i∘fF)).symm
    unfold offerOdds foresee; simp_rw [t]
  rw [Fintype.sum_prod_type]; change (∑ i:A.SitesChoice,∑ j:A.BondChoice, ((∏ k,v k (i k))*(∏ k,y i k (j k))) • G i j)=_
  simp_rw [mul_smul,← Finset.smul_sum,he]; exact compression fF U F hx (fun _=> Patch.frameMass_sum _ B _)
end neighbor

section exact
variable (S:Finset Cover)(C:Side)(K:ℕ→ℝ)(N P:Side)
variable (G:Ratio N P)(A:StepData (More N) (More P))(j:ℕ)(Q:Op SU.Slot)(M:Male)(ho: Odd G.count.val)
variable (χ:Chi)(γ β:ℝ)(l:Loom N){D:ℕ}(p:LaurentRadius j G.count D)
variable (v:Measurable l)(b:A.patch.Branches A.kernel SU.group)(h:0<γ)(g:2*γ<firstRadius SU.group)
variable (f : Purse S)(u:Chorus)(hf : AtSupport (Sound.treble u) (region S N) (knot N u f.val))(W: Fields P)
variable (T:Finset Cover)(uS:S⊆T)(e:halo (Advance.nearZero D) (region S N)⊆ region T N)(pS:Tipping T N C)
include uS pS
private lemma consistent (r:Courses C T)(x:Hall C T):
    let V:= replant T N (Common.pairs C K T r x)
    gathered G j Q M ho χ γ (knot N u f.val) W V = amount C K T f.val r x • gathered G j Q M ho χ γ (wholeZ N u) W V := by
  intro V
  have he:knot N u f.val V=amount C K T f.val r x • wholeZ N u V:=by
    refine congrArg (fun x : ℂ=> x • spool N u) (f.property.locus _ _ ?_ ?_)
    all_goals rintro ⟨a,i⟩ has _; dsimp only [Prod.map_fst, Prod.map_snd,V,replant]; rw [onC_spec]; exact Satin.within T N C pS ⟨a,uS has⟩ i _
  unfold gathered avgF before; simp_rw [he,map_smul,←Finset.smul_sum]; rw [smul_comm]

variable {μ:Measure (Read.Wor (More N) C)}[IsProbabilityMeasure μ]
variable (hz:∀x:Pane N,(depot N).map (fun z=>l (x,z))= (((Borel.Aerial.valsf N).prod μ)).map (VolumeCape.Dream.sceneQ C K N x))
include hf p v b h g hz e

/-- Upgrade Opera: account the weights of all panels, even when W is varying. -/
lemma scenery :
    let g: rawF C T → FC (Single P):= fun F=> ∫ t:Read.Wor (More N) C,
      (∫ z:Hall C T, amount C K T f.val (chooseCourse C T N t) z • panelX T C K N P G A j Q M ho χ γ β u W F (chooseCourse C T N t) z ∂law C T)∂μ
    let frame(x:FramePool C T A.patch) : A.SitesChoice:= occupyFn (forFrame C T N pS) x
    pushMark G A j Q M ho χ γ β l (knot N u f.val) W=
      ∑ x:FramePool C T A.patch, lensOdds C T N P A pS W.1 x • ∑ v:BondPool C T A.patch,
        offerOdds C T N P A pS W.1 (frame x) v • g (foresee C T N P A pS W.1 (frame x) v) := by
  intro g' p'
  let Z(v:Fields N) := gathered G j Q M ho χ γ (knot N u f.val) W v
  have eZ : Envelope Z:= Env.along (g:=Prod.mk W) (env_gathered G j Q M ho χ γ p h g (knot N u f.val) hf.env) (measurable_const.prodMk measurable_id)
  have tZ (a c:Fields N)(p':Agrees (region T N) a.1 c.1)(t:Agrees (region T N) a.2 c.2): Z a= Z c:= gather_dep G j Q M ho χ γ p _ hf W W (fun _ _ _=> rfl) a c (agrees_mono p' (Finset.image_subset_image uS)) (agrees_mono t e)
  let F(i:A.Choices) := A.prediction (G:=SU.group) W.1 i
  let t(i:A.Choices) (x':Orbit N):ℝ:=A.noise β (F i) x'.1
  let r(x':Orbit N):= Z (drawn l x')
  have he(i:A.Choices): (∫ x:Orbit N,t i x • r x ∂ city N) = g' (F i ∘ stretch (porch C T) N) := by
    simp_rw [←Complex.coe_smul]; rw [triangle C K T N l v hz P Z eZ tZ A β (F i) pS]
    unfold Z; simp_rw [consistent S C K N P G j Q M ho χ γ f u W T uS pS,
      smul_comm (mist _ _ _ _ _ _) (amount _ _ _ _ _ _)]; rfl
  have hm (i:A.Choices):Envelope (t i):= Env.along (g:=Prod.fst) (show Envelope (fun x':Pane N=> A.noise β (F i) x') from Env.compact (by unfold StepData.noise StepData.penaltyWeight; fun_prop)) measurable_fst
  rw [outright G A j Q M ho χ γ β l p v b h g _ hf.env]
  let w(i:A.Choices):= A.likelihood (G:=SU.group) W.1 i
  change (∫ z:Orbit N,(∑ i:A.Choices, w i*t i z) • r z∂city N) = _
  simp_rw [Finset.sum_smul, mul_smul]; rw [integral_finsetSum]; swap
  · intro i _; exact (Env.integrableX (Env.scale (hm i) (Env.along (g:=drawn l) eZ (drawn_m l v))) _).smul (w i)
  simp_rw [integral_smul,he]; exact condense C T N P A b pS W.1 g'
end exact
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.scenery
