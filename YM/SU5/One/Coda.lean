import YM.SU5.One.Bare
import YM.SU5.One.ClearBranch

/-!
# Continuity of imprints at all actually clear UV configurations

Costs not asserted uniform across periods or cutoffs. At ANY such parameters
(with cutoff late for the stated test) the observation functionality at these
points is genuinely continuous. Important that the top marker sees the first
field only already (part one, Bare); ALL patches use good branches eventually
(on any period, conditionally on actual Clear). Does NOT assert a spatial
continuity for the tower spacetime translations.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude

section map
open Stencil Next.SectorChange Precision Tree
variable {N P : Side} (G : Ratio N P) (j : ℕ) (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val)
variable {x : ℕ} (p : Stencil.LaurentRadius j G.count x) (q : Chi) (d : ℝ) (h : 0<d) (hk : 2*d < firstRadius SU.group)
include ho p h hk
lemma gathered_upper (f : Mark N) (W : Fields N) : Continuous (fun u : Fields P=>gathered G j Q M ho q d f u W):= by
  have he(i : Forest (ratio G)) : Continuous (fun u : Fields P=> before G j Q M ho q d f i u W):= by
     have hW : Continuous (fun u: Fields P=> middle G q d i u W):=
       ((brake G q d i h hk).comp (continuous_snd.prodMk (continuous_const (y:=W.2)))).prodMk continuous_const
     let g (u:Fields P): Nom N P × FC (Single N):=(middle G q d i u W,f W)
     have t: Continuous g:= hW.prodMk continuous_const
     change Continuous ((fun v: Nom N P × FC (Single N)=>subF G j Q M ho v.1 v.2) ∘ g)
     exact (sub_cont G j Q M ho p).comp t
  unfold gathered avgF
  exact continuous_const.smul (continuous_finsetSum _ (fun i _=> he i))

private def gatherBeam (f : Mark N) (R : Loom N) (A : StepData (More N) (More P)) (β : ℝ) (X: Fields P)(y: Skye.Orbit N) := A.density β X.1 y.1 • gathered G j Q M ho q d f X (drawn R y)
private lemma gatherCost (f : Mark N) (R : Loom N) (A : StepData (More N) (More P))
    (t : Measurable R) (v : A.patch.Branches A.kernel SU.group) (ε : Envelope f)
    (β:ℝ) : Envelope (uncurry (gatherBeam G j Q M ho q d f R A β)):= by
  exact Env.scale (Env.along (g:=fun x:Fields P × Skye.Orbit N=> (x.1.1,x.2.1))
      (kernel_env A β v) ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)))
    (Env.along (g:=fun x:Fields P × Skye.Orbit N=> (x.1,drawn R x.2))
      (env_gathered G j Q M ho q d p h hk f ε) (measurable_fst.prodMk ((drawn_m R t).comp measurable_snd)))
private lemma hereAt (f : Mark N) (R : Loom N) (A : StepData (More N) (More P))
    (β : ℝ) (w : Fields P) (V : ∀ y:Pane N, ContinuousAt (fun u:Pane P=> A.density β u y) w.1):
     ∀ y, ContinuousAt (fun x : Fields P => gatherBeam G j Q M ho q d f R A β x y) w:=by
  intro y
  change ContinuousAt (fun x : Fields P => A.density β x.1 y.1 • gathered G j Q M ho q d f x (drawn R y)) w
  exact ((V y.1).comp (f:=@Prod.fst (Pane P) (Pane P)) (x:=w)
    (show ContinuousAt (fun u: Fields P=>u.1) w from continuous_fst.continuousAt)).smul ((gathered_upper G j Q M ho p q d h hk f (drawn R y)).continuousAt)
omit ho p h hk in
private lemma integrate_here (B: Fields P→ Skye.Orbit N→ FC (Single P))(hz:Envelope (uncurry B))(w : Fields P)(hp : ∀ y, ContinuousAt (fun u=> B u y) w): ContinuousAt (fun u=>∫ y,B u y∂city N) w:= by
  exact MeasureTheory.continuousAt_of_dominated (F:=B) (μ:=city N)
    (Eventually.of_forall fun x=> (show Measurable (B x) from hz.meas.comp (measurable_prodMk_left (x:=x))).aestronglyMeasurable)
    (Eventually.of_forall fun u=> (Eventually.of_forall fun y=> (show ‖B u y‖≤ hz.cost.choose from hz.cost.choose_spec (u,y))))
    (bound:=fun _=> hz.cost.choose) (integrable_const _) (Eventually.of_forall hp)
lemma ascend_continuous_here (f : Mark N) (R : Loom N) (A : StepData (More N) (More P))
    (t : Measurable R) (v : A.patch.Branches A.kernel SU.group) (ε : Envelope f)
    (β : ℝ) (w : Fields P) (V : ∀ y:Pane N, ContinuousAt (fun u:Pane P=> A.density β u y) w.1):
    ContinuousAt (pushMark G A j Q M ho q d β R f) w:= by
  let B (X: Fields P)(y: Skye.Orbit N):= A.density β X.1 y.1 • gathered G j Q M ho q d f X (drawn R y)
  rw [show pushMark G A j Q M ho q d β R f=(fun x=>∫ y,B x y∂city N) from funext fun x=> outright G A j Q M ho q d β R p t v h hk f ε x]
  exact integrate_here B (gatherCost G j Q M ho p q d h hk f R A t v ε β) w (hereAt G j Q M ho p q d h hk f R A β w V)
end map

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)

lemma clear_stage_compact (s : ℕ) {O : Side} : IsCompact (clearStage Y s (O:=O)):= by
  let h:= healthy_closed (G:=SU.group) (Y.meter.a s).threshold (univ: Support (More O))
  have he: clearStage Y s (O:=O)={U: Pane O| Healthy (Y.meter.a s).threshold univ U}:= by
    ext U; change flags _ U=∅ ↔ Disjoint univ _; constructor
    · intro t; rw [t]; exact Finset.disjoint_empty_right _
    intro q; apply Finset.eq_empty_iff_forall_notMem.mpr; exact fun i p=> Finset.disjoint_left.mp q (Finset.mem_univ _) p
  rw [he]; exact h.isCompact

lemma clear_carries {s : ℕ} {O : Side} {x : Pane O} (g : Seat O → SU.E) (h:x∈ clearStage Y s):
    Lattice.gauge g x ∈ clearStage Y s := by
  change flags _ _=_; rw [gauge_flags]; exact h

lemma clear_reads {s : ℕ} {O : Side} {x : Pane O} (h:x∈ clearStage Y s) (p : Face (Per (More O))) :
    SU.group.chord (faceValue x p) ≤ (Y.meter.a s).threshold:= by
  by_contra! w
  have ht : p.1∈ flags (Y.meter.a s).threshold x:= (flags_spec ..).mpr ⟨p,by simp [touched,square,visits],w⟩
  exact Finset.notMem_empty _ ( (show flags _ _=∅ from h) ▸ ht)

-- The following gate is independent of all period choices
private def StableAt (s : ℕ) : Prop:= ∀ (c f : Side) (S:StepData c f), S.patch=Λ.R → S.kernel=Λ.K.bind →
      ∀ u:Config SU.group f, (∀ i: Face (Per f), SU.group.chord (faceValue u i) ≤ (Y.meter.a s).threshold) →
        (∀ x : Site c, S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) u)) ∧
       (∀ v : S.SitesChoice,∀ e : Edge (Site c), S.patch.usesBest S.kernel (S.connector u v e))
private lemma enough : ∀ᶠ s : ℕ in atTop, StableAt Y s := by
  refine YM.OneRegulator.quiet_branch _ _ (sharpBranches Y) (t:=fun s=> (Y.meter.a s).threshold) ?_
  have he: (fun s=> (Y.meter.a s).threshold)=fun s=> Pressure.temp (hat Λ.R.L Λ.x s):=funext fun s=> (Y.meter.boot s).1
  rw [he]; exact (show Tendsto Pressure.temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover Λ)

private lemma earlier {s : ℕ} (b:StableAt Y (s+1)) (f : Altitude.Cloud (Dome (tent Y H)))
    (i k : ℕ) (z : f∈ boardedDB (tent Y H) s) (w : Fields (Journey.side Y i (s+1))) (hw : w.1∈ clearStage Y (s+1)) :
      ContinuousAt (imprint Y H (s+1) i k f) w:= by
  rw [imprint_step Y H i k z]
  have ht:= Y.pilot_steps s i k
  have hp : Envelope (imprint Y H s i k f):= (Tapestry.Ward.signs (breathing Y H s i k f)).env
  let F:= patternA Y s i k
  apply ascend_continuous_here (Vale.apt (Y.ir i) Λ.block Λ.R.L s) _ _ _ _ (Journey.legal Λ) _ _ (threshold Y).1 (threshold Y).2 _ _ F ((Y.voyage i).ownership s).paid.bill ht.2.2 hp
  intro y; let u:=b _ _ F ht.1 ht.2.1 w.1 (clear_reads Y hw); exact YM.OneRegulator.density_here F ht.2.2 _ w.1 y u.1 u.2

private lemma extra {k t : ℕ} (b: StableAt Y (Y.uv k)) (f : Altitude.Cloud (Dome (tent Y H))) (i : ℕ) (z : f∈ boardedDB (tent Y H) t) (hx : t < Y.uv k)
    {w : Pane (Journey.side Y i (Y.uv k))}(hw:w∈ clearStage Y (Y.uv k)):
    ContinuousAt (bareStencil Y H i k f) w:=by
  suffices h: ContinuousAt (imprint Y H (Y.uv k) i k f) (w,w) from h.comp (x:=w) (f:=fun (w:Pane (Journey.side Y i (Y.uv k)))=>(w,w)) (continuous_id.prodMk continuous_id|>.continuousAt)
  -- this is dependent cutoff rewriting
  suffices h:∀ (n:ℕ),StableAt Y n→t<n→∀ w:Pane (Journey.side Y i n),w∈clearStage Y n→ ContinuousAt (imprint Y H n i k f) (w,w) from h _ b hx _ hw
  rintro (_|s) p v w u; · omega
  exact earlier Y H p f i k (Altitude.climbs _ (n:=t) (m:=s) (by omega) z) (w,w) u -- v: t<s+1

/-- Global uniform-threshold assertion at the ACTUAL bare for C0 at every
configuration on which capP is queried nontrivially. No extra hypotheses
on any marks, ANY of strictly shorter height (not any at-height).
Continuity modulus at a fixed-period fixed-test vertex only. -/
theorem each_imprint : ∀ᶠ k in atTop,∀ (s : ℕ), s < Y.uv k → ∀ i (x : Altitude.Cloud (Dome (tent Y H))),
    x∈ boardedDB (tent Y H) s → ContinuousOn (bareStencil Y H i k x) (clearStage Y (Y.uv k)) := by
  filter_upwards [Y.uv_grows.tendsto_atTop.eventually (enough Y)] with k b s u i x hx
  exact fun _ hp=> (extra Y H b x i hx u hp).continuousWithinAt

end YM.CF.Buffered.Afterglow.Tower.One
