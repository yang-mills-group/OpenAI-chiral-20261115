import YM.SU5.FiniteGaugeData.Concord.Diversity
import YM.SU5.FiniteGaugeData.Concord.Exhibit
/-!
# The output-side Arzelà budget without equating any colour channels across periods

`Menu` on the upper W-variable, for the actual nextMark over periods. Can use even with
coefficients varying with period. Works under the other corner's pre-existing uniform
estimates (`Menu`/`gifted` etc) from Afterglow. **Will get simultaneous extraction of
local strong-norm kernels**, not by discarding the second link, ignoring the actual
transmission of these tests or considering only the lattice geometric embeddings.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
open VolumeCape VolumeCape.Atlas VolumeCape.Read
attribute [local instance] opCStarAlgebra

variable {I : Type*}

lemma menu_integral {X:Type*}[MeasurableSpace X]{Z:I→Type*}[∀ i,MeasurableSpace (Z i)]{V:I→Type*}
    [∀i,NormedAddCommGroup (V i)][∀i,NormedSpace ℝ (V i)][∀i,CompleteSpace (V i)]
    (μ:(i:I)→Measure (Z i))[∀i,IsProbabilityMeasure (μ i)]
    {f:(i:I) → X→ Z i→ V i} (h : Menu (T:=fun i:Σ j,Z j=> V i.1) (fun i:Σ j,Z j=>fun x=> f i.1 x i.2))
    (p:∀ i x,Integrable (f i x) (μ i)) : Menu (T:=V) (fun i x=>∫ z,f i x z ∂μ i) := by
  obtain ⟨l,t,u⟩:=h.budget
  have hi(i)(g : Z i→ V i)(l:ℝ)(t:∀ i,‖g i‖ ≤ l) : ‖∫ z,g z∂μ i‖ ≤ l := by
    simpa using norm_integral_le_of_norm_le_const (μ:=μ i) (f:=g) (C:=l) (Eventually.of_forall t)
  refine ⟨?_,l,t,fun i x=> hi i (f i x) l (fun z=> u ⟨i,z⟩ x)⟩
  intro ε e; obtain ⟨P,v,s⟩:= h.deal _ (half_pos e); refine ⟨P,v,fun x y r i=> ?_⟩
  rw [dist_eq_norm,←integral_sub (p i x) (p i y)]; refine lt_of_le_of_lt (hi _ _ (ε/2) (fun z=>?_)) (by linarith)
  simpa only [dist_eq_norm] using (s x y r ⟨i,z⟩).le

variable (S:Finset Cover)(P N:I→Side)(R:Patch)(sz:∀ i,(P i).val=(N i).val*R.L.val)
local notation "Aloft" i:max => bead N R.L P sz i
local notation "upon" i:max x:max => replant S (P i) x
local notation "D₁" => PairsC
local notation "Mt" i:max => FC (Single (P i))

lemma upper_sail (w:(i:I)→Forest (ratio (bead N R.L P sz i)))(a:(i:I)→ Seat (P i)) :
    Deal (fun i (x:D₁)=> (w i).foldAt (upon i x).2 (a i):I→D₁→SU.E):=by
  let J:Type:={x:Lattice.Walk//x.length ≤ 4*R.L.val}
  letI:Finite Lattice.Step:=Finite.of_injective (fun x: Lattice.Step=>(x.dir,x.neg)) (fun a b h=>by cases a; cases b; simpa using h)
  letI:Fintype J:= (show Set.Finite {x:Lattice.Walk|x.length≤4*R.L.val} from List.finite_length_le ..).fintype
  let t(i:I):J:= ⟨(w i).hike (a i), ((w i).hike_lower _).trans ((w i).bound _)⟩
  let F (y:J)(i:I)(x:D₁):= Lattice.travel (upon i x).2 (a i) (y.val)
  have p (b:(i:I)→Edge (Seat (P i))): Deal (I:=I) (fun i x=>(upon i x).2 (b i)) := by
    refine (from_unit (s:=Prod.snd) S P b).deal (fun i=>?_) isCompact_univ (fun _ _=> Set.mem_univ _)
    exact (measurable_pi_apply (b i)).comp ((graft_b S _).comp measurable_snd)
  exact Deal.post (Deal.assembly (T:=fun (_:I)=>SU.E) F (fun x=> Satin.roam P (fun i x=>(upon i x).2) p _ a) t) continuous_inv

variable (χ:Chi)(γ:ℝ)(q:0<γ)(g:2*γ<firstRadius SU.group)
include q g
lemma netted (t:(i:I)→Forest (ratio (bead N R.L P sz i))) (a:(i:I)→Edge (Seat (P i))) (W:(i:I)→ Fields (N i)) :
    Deal (fun i x=> (middle (Aloft i) χ γ (t i) (upon i x) (W i)).1 (a i) : I→ D₁→ SU.E) := by
  let b(i)(x:D₁)(v:Seat (P i)):= (t i).foldAt (upon i x).2 v; let k(i):=(a i).1; let l(i):=(a i).1+Lattice.step (a i).2
  have hk:= upper_sail S P N R sz t k; have hl:= upper_sail S P N R sz t l
  let v: I→D₁→SU.E:=fun i x=> gauge (b i x) (upon i x).2 (a i)
  let r: I→ SU.E:= fun i=> Precision.replica (ratio (Aloft i)) (show Config SU.group _ from (W i).2) (a i)
  let u:I→D₁→SU.E:= fun i x=> knit χ γ (v i x) (r i)
  have hu:Continuous (fun x:SU.E × SU.E=> knit χ γ x.1 x.2):=(SU.group.lieExp_cont.comp ((patched_continuous χ q g).comp (continuous_fst.mul continuous_snd.inv))).mul continuous_snd
  have p:Deal v:=by
    have hx := (from_unit (s:=Prod.snd) S P a).deal (fun i=> (measurable_pi_apply (a i)).comp ((graft_b S _).comp measurable_snd)) isCompact_univ (fun _ _=> Set.mem_univ _)
    exact (((hk.prod hx).post (continuous_fst.mul continuous_snd)).prod hl).post (continuous_fst.mul continuous_snd.inv)
  have hx:Deal u:= (p.prod (Deal.pure (T:=fun _=>SU.E) r)).post hu
  exact (((hk.prod hx).post (continuous_fst.inv.mul continuous_snd)).prod hl).post (continuous_fst.mul continuous_snd.inv.inv)

variable (j D:ℕ)(z:LaurentRadius j R.L D)(M:I→Male)(Q:I→Op SU.Slot){d:ℝ}(y:∀i,‖Q i‖ ≤ d)
variable (u:Chorus)
include z d y
lemma held (W:(i:I)→ Fields (N i)) : Menu (T:=fun i=> Mt i) (fun i x=> gathered (Aloft i) j (Q i) (M i) R.odd_side χ γ (wholeZ (N i) u) (upon i x) (W i)):=by
  let J(i:I):= Forest (ratio (Aloft i)); let V:= Σ i,J i; let a:=fun x:V=> N x.1; let b:= fun x:V=> P x.1
  refine Satin.circle (J:=J) ?_
  refine Satin.wool a R.L b (fun v=> sz v.1) j D z R.odd_side (fun v=> M v.1) (fun v=> Q v.1) (fun v=> y v.1) (fun v x=> middle (Aloft v.1) χ γ v.2 (upon v.1 x) (W v.1)) ?_ u
  intro e; exact netted S b a R (fun v=> sz v.1) χ γ q g (fun (v:V)=> v.2) e (fun v=> W v.1)

variable (K:KernelChoices)(C : Side) (O T:Finset Cover)(v:ℕ→ℝ)
local notation "ℙ" i:max => slate P R K N sz i
variable (BF:I→ℝ){x:ℝ}(hf:∀i, ‖BF i‖ ≤ x)

include x hf
lemma unveiled (F:I→ D₁→ rawF C T)(p:Deal F)(r:I→ Courses C T)(w:I→ Hall C T):
    Menu (T:=fun i=> Mt i) (fun i x=> panelX T C v (N i) (P i) (Aloft i) (slate P R K N sz i) j (Q i) (M i) R.odd_side χ γ (BF i) u
      (upon i x) (F i x) (r i) (w i)) := by
  let U:RG.StepData 1 R.L:= ⟨R,K,by simp⟩
  let π: I→D₁→ℂ:=fun i x => mist C T U (BF i) (F i x) (w i).1
  have he:Menu π:= Menu.clip ((Deal.pure (T:=fun _=>ℝ) BF).prod (p.prod (Deal.pure (T:=fun _=>Hall C T) w))) (isCompact_Icc.prod isCompact_univ) (fun i x=>⟨abs_le.mp (hf i), Set.mem_univ _⟩) (mist_c C T U)
  exact he.scale (held S P N R sz χ γ q g j D z M Q y u (fun i=> replant T _ (Common.pairs C v T (r i) (w i))))

-- integrate twice against the SAME pre-mask as in scenery
variable (μ:(i:I)→ Measure (Read.Wor (More (N i)) C))[∀i,IsProbabilityMeasure (μ i)]
variable (t:I→Purse O){b₀:ℝ}(vT:∀i x, ‖(t i).val x‖ ≤ b₀)(hB:0≤b₀)(pS:O⊆T)

def hostess (F:I→ D₁→ rawF C T)(i:I)(a:PairsC) := ∫ w:Read.Wor (More (N i)) C,
  (∫ x:Hall C T, amount C v T (t i).val (chooseCourse C T (N i) w) x •
    panelX T C v (N i) (P i) (bead N R.L P sz i) (slate P R K N sz i) j (Q i) (M i) R.odd_side χ γ (BF i) u (upon i a)
      (F i a) (chooseCourse C T (N i) w) x ∂law C T) ∂μ i
-- `include` not inherited in def?
include pS vT hB
lemma concertSeat (F:I→ D₁→ rawF C T)(p:Deal F): Menu (hostess S P N R sz χ γ j M Q u K C O T v BF μ t F):=by
  let L(i):= Read.Wor (More (N i)) C; let V:=Σ i,L i; let W:=Hall C T
  let r(i:V):=chooseCourse C T (N i.1) i.2
  let H(i:V)(a:D₁)(x:W):= panelX T C v (N i.1) (P i.1) (Aloft i.1) (ℙ i.1) j (Q i.1) (M i.1) R.odd_side χ γ (BF i.1) u (upon i.1 a) (F i.1 a) (r i) x
  let A(i:V)(x:W):= amount C v T (t i.1).val (r i) x
  refine menu_integral μ (menu_integral (Z:=fun _:V=>W) (V:=fun i:V=>Mt i.1) (f:=fun i:V=> fun x:D₁=> fun z=> A i z • H i x z) (fun _=>law C T) ?_ ?_) (fun i _=> Integrable.of_finite)
  · let J := Σ (_:V), W; let a:=fun i:J=> i.1.1
    have he:Menu (I:=J) (fun (i:J)(x:D₁)=> H i.1 x i.2) := unveiled S (P∘a) (N∘a) R (fun v=>sz (a v)) χ γ q g j D z (M∘a) (Q∘a) (fun v=>y _) u K C T v (BF∘a) (fun v=>hf (a v)) (F∘a) (p.re a) (r∘Sigma.fst) Sigma.snd -- tune
    exact (Menu.cnst (T:=fun (_:J)=>ℂ) (fun i=> A i.1 i.2) hB (fun v=> vT _ _)).scale he
  intro i x; refine Env.integrableX (Girt.kitE (A i) (H i x) (fun (c:ℂ)(u:Mt i.1)=>c • u) (by exact continuous_fst.smul continuous_snd) (amount_env C v T ((t i.1).property.mono pS) (r i)) (xp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z q g)) _

variable (p:∀ i,Tipping T (N i) C) (l:(i:I)→ Loom (N i))(A:∀i, Measurable (l i))
variable (hZ:∀i (x:Pane (N i)),(depot (N i)).map (fun z=>l i (x,z))= (((VolumeCape.Borel.Aerial.valsf (N i)).prod (μ i))).map (VolumeCape.Dream.sceneQ C v (N i) x))
variable (hh:∀i, AtSupport (Sound.treble u) (region O (N i)) (knot (N i) u (t i).val)) (tZ:∀ i, halo (Advance.nearZero D) (region O (N i)) ⊆ region T (N i))
include p l A hZ hh tZ

lemma cards (B:R.Branches K SU.group): Menu (T:=fun i=>Mt i) (fun i x=>pushMark (Aloft i) (ℙ i) j (Q i) (M i) R.odd_side χ γ (BF i) (l i) (knot (N i) u (t i).val) (upon i x)):=by
  let V:= FramePool C T R; let V':= BondPool C T R; let r(x:V)(i:I): (ℙ i).SitesChoice:= occupyFn (forFrame C T _ (p i)) x
  let L(a:V)(i:I)(x:D₁):= lensOdds C T (N i) (P i) (ℙ i) (p i) (upon i x).1 a
  let Z(a:V)(b:V')(i:I)(x:D₁):= offerOdds C T (N i) (P i) (ℙ i) (p i) (upon i x).1 (r a i) b
  let f(a:V)(b:V')(i:I)(x:D₁):= foresee C T (N i) (P i) (ℙ i) (p i) (upon i x).1 (r a i) b
  let H(a:V)(b:V'):= hostess S P N R sz χ γ j M Q u K C O T v BF μ t (f a b)
  have he(a b): Menu (f:=H a b) := concertSeat S P N R sz χ γ q g j D z M Q y u K C O T v BF hf μ t vT hB pS (f a b) (likely (sP:=Prod.fst) S P C T R K B N sz measurable_fst p (fun _=>b) (r a))
  have h(a:V)(b:V'): Menu (Z a b) ∧ Menu (L a) := costs (sP:=Prod.fst) S P C T R K B N sz measurable_fst p (fun _=>a) (fun _=> b) (r a)
  have ht(a:V):Menu (T:=fun i=>Mt i) (fun i x=> L a i x • ∑ b:V',Z a b i x • H a b i x) :=
    (h a (fun _=> R.center)).2.scale (Menu.total univ (fun (b:V') (i:I) x=> Z a b i x • H a b i x) (fun b _=> (h a b).1.scale (he a b)))
  refine (Menu.total univ (fun (a:V) (i:I) (x:D₁)=> L a i x • ∑ b:V',Z a b i x • H a b i x) (fun a _=> ht a)).congr ?_
  intro i x; exact (scenery O C v (N i) (P i) (Aloft i) (ℙ i) j (Q i) (M i) R.odd_side χ γ (BF i) (l i) z (A i) B q g (t i) u (hh i) (upon i x) T pS (tZ i) (p i) (hZ i)).symm
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.cards
