import WakeRoad.PaidGram

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 340000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind
namespace GramSignal
open CF.Onyx Ballad Signal.Interval Lamour.Bridge.Celeste Pressure
open Stationary (Gaia)
variable (P:Spine)(f:ℕ→ℕ)
local notation "iA" n:max=> P.period (P.projection.rows (f n))
local notation "ν" s:max n:max=> side P.run (iA n) s

def localStaff (u:Cover)(L:Twah.DirSpin)(F:PlaqAxes): Staff := ⟨nodeC u,u,(nodeC u,F),L,[],rfl⟩
lemma ready_local (u:Cover)(L:Twah.DirSpin)(F:PlaqAxes): (localStaff u L F).Pays 4 0:= by
  constructor
  · exact le_rfl
  · intro i h
    change i∈ skyDeck (nodeC u) 4
    rw [show i=nodeC u from List.mem_singleton.mp h]
    exact owns ..
  intro i h
  change i ∈ skyDeck (nodeC u) 4
  change i ∈ EmberWind.visa (nodeC u,F) at h
  have ht : i∈ visits (nodeC u) (Lattice.square F.val.1 F.val.2) := List.mem_toFinset.mp h
  have hp:= walk_pav _ _ _ ht
  change i∈ skyDeck (nodeC u) 4 at hp
  exact hp
variable {P f} (I:ℝ) (p:0<I) (a b : ℕ → Cover) {X:Gaia}
local notation "Zr"=> zoomR P.par I

lemma zoom_pos (s:ℕ):0<Zr s:= Nat.ceil_pos.mpr (half_pos (BProof.coin_pos ..))
include p
lemma zoom_pays : ∀ᶠ s:ℕ in atTop, (Zr s:ℝ) ≤ sPow P.par s (I+1):=by
  filter_upwards [(turnover P.par).eventually (BProof.coin_budget (b:=I) (c:=0) (a:=0) (d:=0) (e:=I+1) (f:=0) (Or.inr (Or.inl ⟨rfl,lt_add_one _⟩)) 1 1 zero_lt_one),grow_e (I+1) 2 (by linarith) P.par] with s hx e
  have hp: (Zr s:ℝ)< sPow P.par s I/2+1:= Nat.ceil_lt_add_one (half_pos (BProof.coin_pos ..)).le
  change 1*sPow P.par s I < 1*sPow P.par s (I+1) at hx
  linarith
lemma local_seating (z:Tendsto (fun s=>riseX (Zr s) (a s-b s)) atTop (𝓝 X))
    (L G:Twah.DirSpin)(F D:PlaqAxes)(t:StrictMono f) :
    seated P f 4 0 (fun s=> localStaff (a s) L F) (fun s=>localStaff (b s) G D) (I+2) := by
  refine ⟨fun s=> ready_local ..,fun s=> ready_local ..,?_⟩
  let R:=4+Staff.clearance+8
  let m (s):= separationCost (nodeC (a s)) (nodeC (b s))
  -- bounding m via coord-wise convergence (avoid L2 norm estimates)
  have hz (i:Axis): Tendsto (fun s=> ((nodeC (a s) i - nodeC (b s) i:ℤ):ℝ)/(2*(Zr s:ℝ))) atTop (𝓝 (X i)) :=
    (show Continuous (fun x:Gaia=>(x i:ℝ)) by fun_prop).continuousAt.tendsto.comp (Spine.fireGauge a b Zr (zoom_grows P.par p) (zoom_pos I) X z)
  let T:= ∑ i:Axis,|X i|
  let H:= T+1
  have ht: 0≤T:= Finset.sum_nonneg fun i _=> abs_nonneg _
  have hH (i:Axis): |X i| < H:=(single_le_sum (f:=fun i=> |X i|) (fun _ _=> abs_nonneg _) (mem_univ i)).trans_lt (lt_add_one _)
  have he (i:Axis):∀ᶠ s:ℕ in atTop, ((nodeC (a s) i - nodeC (b s) i).natAbs:ℝ) ≤ H*(2*Zr s) :=by
    filter_upwards [(hz i).abs.eventually (gt_mem_nhds (hH i))] with s q
    have h₁: 0<2*(Zr s:ℝ):=by have h:= zoom_pos (P:=P) I s; positivity
    rw [Nat.cast_natAbs, Int.cast_abs]; exact (le_div_swap q.le h₁)
  have hr:∀ᶠ s:ℕ in atTop,(m s:ℝ) ≤ H*(2*Zr s) := by
    filter_upwards [Filter.eventually_all.mpr he] with s e
    obtain ⟨j,_,hj⟩:= exists_mem_eq_sup _ (Finset.univ_nonempty (α:=Axis)) (fun k=> ((nodeC (a s)-nodeC (b s)) k).natAbs)
    unfold m separationCost; rw [hj]; exact e j
  filter_upwards [hr,zoom_pays (P:=P) I p, (turnover P.par).eventually (BProof.coin_budget (a:=0) (b:=I+1) (c:=0) (d:=0) (e:=I+2) (f:=0) (Or.inr (Or.inl ⟨rfl,by linarith⟩)) (2*H+R) 1 zero_lt_one),grow_e (I+1) 1 (by linarith) P.par] with s v hr hb hg
  let A:= nodeC (a s); let B:= nodeC (b s)
  filter_upwards [(steps_sides P f t s).eventually (liftMoney ({A,B}:Finset Cover))] with n h
  let i:= ν s n; let q:=wrap (More i)
  refine ⟨R+m s,q A,?_,?_,?_⟩
  · change Lattice.halo R {q A} ⊆ BlockP (R+m s) (q A)
    exact Corona.halo_mono (by omega) (Subset.refl _)
  · change Lattice.halo R {q B} ⊆ BlockP (R+m s) (q A)
    intro x u
    obtain ⟨y,v,r⟩:=halo_spec.mp u
    rw [mem_singleton.mp v] at r
    apply blocks_test.mpr
    apply (separation_triangle _ (q B) _).trans
    have h':separation (q A) (q B)=m s:=h A (by simp) B (by simp)
    omega
  push_cast
  change (2*H+↑R)*sPow P.par s (I+1)< 1*sPow P.par s (I+2) at hb
  have hl:H≥0:=by unfold H; linarith
  nlinarith only [v,hr,hb,hl,hg,Nat.cast_nonneg (α:=ℝ) R]
where
  le_div_swap {x H y:ℝ}(h: |x/y|≤H)(p:0<y): |x|≤ H*y := by rw [abs_div,abs_of_pos p] at h; exact (div_le_iff₀ p).mp h -- div_le

omit p in
lemma exponent_monotone {x y:ℝ} (h:x ≤ y) (s:ℕ)(Λ:Preparation): sPow Λ s x ≤ sPow Λ s y:=by
  unfold sPow BProof.coin
  apply Real.exp_le_exp.mpr
  gcongr

open CF.Hiro Regis.Head.Brecht
/-- Simultaneous at any allowed zoom and endpoints; no assumption on enrollment beyond Q&P's own pooling. -/
theorem local_value (z:Tendsto (fun s=>riseX (Zr s) (a s-b s)) atTop (𝓝 X)) (e:X≠0)
    (L G:Twah.DirSpin)(F D:PlaqAxes) {β:ℕ→ℝ}(g:Jewel.Pooling P.run (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β)(Q:P.PhysicalWakeGram):
    let w(s:ℕ) := localStaff (a s) L F
    let v(s:ℕ) := localStaff (b s) G D
    Tendsto (staffCov P β 4 Zr w v) atTop (𝓝 (shotR L G (X:=X)*speckleV F D SU.group X)) ∧ Tendsto (oneStaff P β 4 Zr w) atTop (𝓝 0) ∧ Tendsto (oneStaff P β 4 Zr v) atTop (𝓝 0) := by
  intro w v
  have h:=zoom_pays (P:=P) I p; let U:=zoom_grows P.par p
  exact staff_limit (show (0:ℝ)<I+2 by linarith) g Q (local_seating I p a b z L G F D g.up) (h.mono (fun s t=>t.trans (exponent_monotone (by linarith) _ _))) e (zoom_pos I) U z (Spine.fireGauge a b Zr U (zoom_pos I) X z) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)

abbrev testSite (P:Spine)(A:ℝ)(s:ℕ): Cover:=P.rangeClasp (zoomR P.par A s)
def dinner (P:Spine)(A:ℝ)(i:Bool)(s:ℕ): Staff:= localStaff (cond i (testSite P A s) 0) Spine.pairMood Prototype.goldF
lemma corner_value {β:ℕ→ℝ}(g:Jewel.Pooling P.run (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β)(Q:P.PhysicalWakeGram):
    Tendsto (staffCov P β 4 Zr (dinner P I true) (dinner P I false)) atTop (𝓝 P.supper) ∧ Tendsto (oneStaff P β 4 Zr (dinner P I true)) atTop (𝓝 0) ∧ Tendsto (oneStaff P β 4 Zr (dinner P I false)) atTop (𝓝 0):= by
  exact local_value I p (testSite P I) (0:ℕ → Cover) (P.posPilot (zoom_grows P.par p) (zoom_pos I)) P.service_space Spine.pairMood Spine.pairMood Prototype.goldF Prototype.goldF g Q

lemma appointments : P.PencilLease I (corner P.pianist) 0 (testSite P I) 0:= by
  have hz:= P.service_space
  refine ⟨(appoint_as P.par p _ _).mpr ((P.posPilot (zoom_grows P.par p) (zoom_pos I)).congr fun s=> by simp [testSite]),(appoint_as P.par p _ _).mpr ?_,fun t=>False.elim (hz t)⟩
  simpa only [Pi.zero_apply, zeroSpin] using (tendsto_const_nhds (x:=(0:Gaia)) (f:=atTop (α:=ℕ)))


/- Persistent support statement. Every height has the same finite deck extent before
translating to its center node. For fixed sufficiently advanced s the two decks are
literally disjoint in the cover, all charged Tapestry widths too, with a positive physical
distance (depending on s). Contrast `no_direct_pair` for varying s.
-/
def printedDeck (P:Spine)(i:ℕ)(W:Staff): Set RSpace:= ⋃ a ∈ (↑(W.skyRent 4): Set Cover), Tapestry.shield P.par P.width i a

set_option maxRecDepth 3800
omit p in
lemma printed_bounds {s:ℕ}{x:Cover}{L:Twah.DirSpin}{F:PlaqAxes}{y:RSpace}(h:y∈printedDeck P s (localStaff x L F))(i:Axis):
    |precisionAt P.par s*y i-(nodeC x i:ℝ)| ≤ (reserve P.par P.width:ℝ)+12:=by
  rcases Set.mem_iUnion₂.mp h with ⟨a,g,t⟩
  have hv:=t i; change a∈ (localStaff x L F).skyRent 4 at g; have ha:=g; change a∈ skyDeck (nodeC x) (4+8) at ha; obtain ⟨l,u⟩:= (pav_v ..).mp ha i; have hb: |((a i:ℤ):ℝ)-nodeC x i| ≤ 12:=by
    apply abs_le.mpr
    exact ⟨by exact_mod_cast (by omega : -(12:ℤ) ≤ a i-nodeC x i), by exact_mod_cast (by omega : a i-nodeC x i≤ (12:ℤ))⟩
  change |precisionAt P.par s*y i - a i| ≤ _ at hv
  exact (abs_sub_le _ (a i:ℝ) _).trans (add_le_add hv hb)

-- Rather than assuming enough clearance in large-s layout, spend from coordinate convergence
theorem separated_decks : ∀ᶠ s:ℕ in atTop, ∀ x ∈ printedDeck P s (dinner P I true s),
    ∀ y ∈ printedDeck P s (dinner P I false s), 1/precisionAt P.par s ≤ x 3-y 3:=by
  have ht := Spine.fireGauge (testSite P I) 0 Zr (zoom_grows P.par p) (zoom_pos I) (corner P.pianist) (P.posPilot (zoom_grows P.par p) (zoom_pos I))
  have hz:Tendsto (fun s=> ((nodeC (testSite P I s) 3 - nodeC 0 3:ℤ):ℝ)/(2*(Zr s:ℝ))) atTop (𝓝 (corner P.pianist (3:Axis))):=
    (show Continuous (fun x:Gaia=> (x (3:Axis):ℝ)) by fun_prop).continuousAt.tendsto.comp ht
  have hc: P.pianist/2 < corner P.pianist (3:Axis):=by simpa [corner] using half_lt_self P.holy
  let R:ℝ:= (reserve P.par P.width:ℝ)+12
  filter_upwards [hz.eventually (lt_mem_nhds hc), (tendsto_natCast_atTop_atTop.comp (zoom_grows P.par p)).eventually_gt_atTop ((2*R+1)/P.pianist)] with s h z x tx y ty
  have hp:0< (Zr s:ℝ):=by have h:=zoom_pos (P:=P) I s; positivity
  change P.pianist/2 < _/(2*(Zr s:ℝ)) at h
  have hx:= (lt_div_iff₀ (show 0<2*(Zr s:ℝ) by positivity)).mp h
  have he:= (div_lt_iff₀ P.holy).mp z
  have hf:= (abs_le.mp (printed_bounds (x:=testSite P I s) (L:=Spine.pairMood) (F:=Prototype.goldF) tx 3)).1
  have hg:= (abs_le.mp (printed_bounds (x:=0) (L:=Spine.pairMood) (F:=Prototype.goldF) ty 3)).2
  apply (div_le_iff₀ (positiveScale _ _)).mpr
  change (2*R+1)< ↑(Zr s)*P.pianist at he
  unfold R at he
  push_cast at hx
  linarith

open Jewel
universe u'
omit p
/-- Checkpoint 1: new mixed weight-five reading, co-issued with the whole starting procurement.
Two independent axes of extraction: physical period/cutoff price realization (f∘f'), and the
rung sequence of poll readings on P (c∘c'). The staff price uses the former; since its
P.E conclusion is for *all* sufficiently late rungs, it also keeps that conclusion along the
latter. Neither the singleState price of these mixed staffs nor contour/local fields are
asserted here. -/
theorem dinnerElection (D:TintDemand)(M:ℕ) :
    ∃ (P:Spine)(K:P.Register)(E:ℝ), P.PreparedInvestment K E M ∧
    PureForce.CakeL.SignedPoseBudget P ∧ P.QualifiedWakeReadout.{u'} K ∧ P.PhysicalWakeGram ∧
    ∀ A:ℝ, 0<A → ∀ c f:ℕ→ℕ, StrictMono c → StrictMono f →
    ∀ (J:Type)[Countable J](T:J→ℕ→P.Test)(z:J→ℂ), (∀ i, Spine.WakePoll P (T i) (z i)) →
    ∃ (f' c' : ℕ→ℕ) (β:ℕ→ℝ), StrictMono c' ∧ StrictMono f' ∧
      Pooling P.run (P.period ∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) (f ∘ f') β ∧
      (let r:=zoomR P.par A; let w:=dinner P A true; let v:=dinner P A false;
      Tendsto (staffCov P β 4 r w v) atTop (𝓝 P.supper) ∧
      Tendsto (oneStaff P β 4 r w) atTop (𝓝 0) ∧ Tendsto (oneStaff P β 4 r v) atTop (𝓝 0) ∧
      0< ‖P.supper‖/2 ∧
      (∀ s (i:Bool), let W:=dinner P A i s; InTest P.calibration true (W.skyRent 4) false
        (Papal.household P.calibration (choiceWeave P β W 4 s)) ∧ CovCover P.calibration (Papal.household P.calibration (choiceWeave P β W 4 s)) ∧ printedHere P.par P.width s (W.skyRent 4) (printedDeck P s W)) ∧
      ∀ᶠ s:ℕ in atTop, ‖P.supper‖/2 < ‖staffCov P β 4 r w v s‖ ∧
        ∀ x ∈ printedDeck P s (w s), ∀ y ∈ printedDeck P s (v s), 1/precisionAt P.par s ≤ x 3-y 3) ∧
      ∀ B:P.Spectrum0 3→ Prop, (∀ᵐ x∂ P.pillars 3, B x) → ∃ x, B x ∧ Spine.JointTuple.{u'} P K x ∧
        Spine.HoldRead P A (c ∘ c') x (corner P.pianist) 0 (testSite P A) 0 ∧
        ∀ i,Tendsto (fun r => P.singleState 3 (c (c' r)) x (T i (c (c' r)))) atTop (𝓝 (z i)) := by
  obtain ⟨P,K,E,h,u,w,k⟩:=Spine.wakeElectionWithPhysicalGram.{u'} D M
  refine ⟨P,K,E,h,u,w,k,?_⟩
  intro A p c f pc pf J C T z t
  obtain ⟨f',β,hf,g⟩:= Pooling.fettle P.run P.history pf
  obtain ⟨c',hc,v'⟩:= w A p (corner P.pianist) 0 (testSite P A) 0 J c pc (appointments A p) T z t
  refine ⟨f',c',β,hc,hf,g,?_,v'⟩
  obtain ⟨hb,ht,H⟩:=corner_value A p g k
  exact ⟨hb,ht,H,half_pos P.supper_money,fun s i=>showings P A β s i,
    (hb.norm.eventually (lt_mem_nhds (half_lt_self P.supper_money))).and (separated_decks A p)⟩
where
  showings (P:Spine)(A :ℝ)(β:ℕ→ℝ)(s:ℕ)(i:Bool):
    let W:=dinner P A i s; InTest P.calibration true (W.skyRent 4) false
        (Papal.household P.calibration (choiceWeave P β W 4 s)) ∧ CovCover P.calibration (Papal.household P.calibration (choiceWeave P β W 4 s)) ∧ printedHere P.par P.width s (W.skyRent 4) (printedDeck P s W):=by
    intro W
    have h:W.Pays 4 0:=ready_local ..
    exact ⟨W.letterBudget _ P.calibration _ h,W.registration _ _ _ h,fun x hx y p=> Set.mem_iUnion₂.mpr ⟨x,hx,p⟩⟩


#check @dinnerElection
#check @local_value
#print axioms local_value
#print axioms dinnerElection
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
