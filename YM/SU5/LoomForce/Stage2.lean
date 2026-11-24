import YM.SU5.LoomForce.Earning
import SU5SatinWakePhysicalGramNovember8

/-! CP2 partial application. Elect with the *very same* mixed stencils and aperture
of CP1, proving the hypotheses of `QualifiedWakeReadout` on those. Strengthens the
physical price; use now crucially the Broom estimate earned at any arity and poses
as documented here. Note the actual separation **unit**, RUNG spacing -- see CP1's
limitation: indeed this pricing as stated using direct "duo" tenancy at N is not
possible at those sure walls and with a surviving actual node separation. This is
building the local-investment to make the actual price calibration, intended to
be used when settling the ultimate smears and supporting the procurement of those
labels on those merited powers. Not claiming here the existence of such fixed momentum
force fields, charges after unpadding etc.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce
open Function Filter Metric Fock Finset Lat Lattice Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Morn Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey Heat
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Jewel Shuttle
open YM.Stationary (Gaia)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology ContDiff Classical
open Palette
variable (P : Spine) (K : P.Register) (A : ℝ) (u v : ℕ → Cover) (β : ℕ → ℝ)
  {J : Type} [Countable J] {E : ℝ} {Mc : ℕ} {f : ℕ → ℕ}
local notation "Ω" => P.calibration
abbrev ten_floor : 4 ≤ (10:ℕ) := by norm_num

def actorE (P : Spine) (u : ℕ→ Cover) (A : ℝ) (β : ℕ → ℝ)(s:ℕ) :=
  onWord (I:=Unit) P A (fun _=>none) ten_floor β s (fun _=> u s) [()]

lemma actor_ancestry (s : ℕ) : (actorE P u A β s).val= household P.calibration (billAt P A u s β) := by
  change household Ω (blockVisit P (fun _=>none) A s β 10 (fun _=> u s) [()])=_
  rw [block_cons,stitch_yes,show blockVisit P (fun (_:Unit)=>none) A s β 10 (fun _=> u s) []= (1:Papal.Weaver) from rfl,mul_one]; rfl

def pointVote (P:Spine)(A:ℝ)(u v:ℕ→ Cover)(β:ℕ→ℝ)(i:Fin 3)(s:ℕ) : P.Test :=
  ![actorE P u A β s,actorE P v A β s,actorE P u A β s*actorE P v A β s] i
def meritTally : Fin 3 → ℂ := ![0,0,payoff]
def coupleP (P : Spine) (x : P.Spectrum0 3) (u v : ℕ → Cover) (A : ℝ) (β : ℕ → ℝ) (s : ℕ) : ℂ :=
  P.selectedPanel (actorE P u A β s) (actorE P v A β s) s x

lemma point_polls (T:PreparedInvestment P K E Mc)(p:0<A)(t:Pooling P.run (takenVolume P) (takenCutoff P) f β)
    (Q:P.PencilLease A 0 touchPoint u v) (hu:Tendsto (fun s=> infiniteE P s (billAt P A u s β)) atTop (𝓝 0))
    (hv:Tendsto (fun s=> infiniteE P s (billAt P A v s β)) atTop (𝓝 0))
    (hf:Tendsto (fun s => unselectedCost P A u v s β) atTop (𝓝 payoff)) :
    ∀ i, WakePoll P (pointVote P A u v β i) (meritTally i) := by
  have hx (i) (L:List (Fin 2)) (h:L.Nodup) (w : ∀ s,
      pointVote P A u v β i s=onWord P A (fun _=>none) ten_floor β s ![u s,v s] L)
      (q : Tendsto (fun s=>P.eReadL s (pointVote P A u v β i s)) atTop (𝓝 (meritTally i))) :
      WakePoll P (pointVote P A u v β i) (meritTally i) := by
    let y: Fin 2 → Gaia := ![0,touchPoint]; let U s : Fin 2→ Cover:=![u s,v s]; let a : Fin 2→ Sewer:=fun _=> none
    have he (i:Fin 2) : Appoint P.par A (fun s=> U s i) (y i):=by fin_cases i; exact Q.p0; exact Q.p1
    have hp : Injective y:=by intro i j k; fin_cases i <;> fin_cases j; rfl; exact (point_ne k.symm).elim; exact (point_ne k).elim; rfl
    let D := inked a (fun _=>Prototype.goldF) (fun _=>pairMood) y L
    have ht := uptakes P K T A (fun (_:Fin 2)=>Prototype.goldF) (fun _=>pairMood) y U p he a L ten_floor t
      (fun i j w'=>Eventually.of_forall (fun s=>congrArg (U s) (hp w'))) (List.Pairwise.imp (fun t w=> t (hp w)) h)
    have hy: meritTally i = D := by
      apply tendsto_nhds_unique q; exact ht.congr fun s=> (congrArg (fun x:P.Test=> P.eReadL s x) (w s)).symm
    rw [hy,funext w]; exact polls_word P K T A a L ten_floor U y p t hp he h
  intro i; fin_cases i
  · refine hx 0 [0] (by decide) (fun s=> rfl) ?_; refine hu.congr fun s=>?_; change P.E s _= P.E s (actorE P u A β s).val; rw [actor_ancestry]
  · refine hx 1 [1] (by decide) (fun s=> rfl) ?_; refine hv.congr fun s=>?_; change P.E s _= P.E s (actorE P v A β s).val; rw [actor_ancestry]
  apply hx 2 [0,1] (by decide) _
  · have he:= hf.add (hu.mul hv); rw [zero_mul,add_zero] at he; refine he.congr ?_
    intro i; rw [unselectedCost,sub_add_cancel]; apply congrArg (P.E i)
    change household P.calibration _= (actorE P u A β i).val * (actorE P v A β i).val; rw [actor_ancestry,actor_ancestry]; rfl
  intro i; apply Subtype.ext; change ((actorE P u A β i).val * (actorE P v A β i).val)=
     household P.calibration (blockVisit P (fun _=>none) A i β 10 (![u i,v i]: Fin 2→ Cover) [0,1]); rw [actor_ancestry,actor_ancestry,block_cons,block_cons, stitch_yes,stitch_yes]; simp_rw [show blockVisit P _ _ _ _ _ _ []= (1:Papal.Weaver) from rfl,mul_one]; rfl

universe j
/-- Application from the PhysicalGram election, taking actual components. -/
theorem stage2 (X : TintDemand) (Mc : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ (P : Spine) (K : P.Register) (E : ℝ) (u v : ℕ → Cover) (β : ℕ → ℝ) (f : ℕ → ℕ),
      PreparedInvestment P K E Mc ∧ PureForce.CakeL.SignedPoseBudget P ∧
      QualifiedWakeReadout.{j} P K ∧ PhysicalWakeGram P ∧
      PencilLease P A 0 touchPoint u v ∧ Pooling P.run (takenVolume P) (takenCutoff P) f β ∧
      (∀ s, |κFix β s| ≤ 2 * bornQ P.par s) ∧
      PaidPair P (A+1) (staffAt ∘ u) (staffAt ∘ v) (fun _ => 10) ∧
      (∀ s (U:ℕ → Cover), CovCover P.calibration (actorE P U A β s).val ∧
        InTest P.calibration true (skyDeck (nodeC (U s)) (10+8)) false (actorE P U A β s).val) ∧
      0 < ‖payoff‖ ∧ (∀ i,WakePoll P (pointVote P A u v β i) (meritTally i)) ∧
      Tendsto (fun s => unselectedCost P A u v s β) atTop (𝓝 payoff) ∧
      (∀ᶠ s : ℕ in atTop,
        ‖payoff‖ / 2 < ‖unselectedCost P A u v s β‖ ∧
        printedHere P.par P.width s (skyDeck (nodeC (u s)) (10+8)) (rescaledFit P s A 0 (1/4)) ∧
        printedHere P.par P.width s (skyDeck (nodeC (v s)) (10+8)) (rescaledFit P s A touchPoint (1/4)) ∧
        ∀ᶠ n in atTop, Ferry P.run s (takenVolume P (f n)) (takenCutoff P (f n)) ∧
          ShelterRent P.run s (takenVolume P (f n)) (takenCutoff P (f n)) ∧
          TiltInvoice P.run s (takenVolume P (f n)) (takenCutoff P (f n)) E) ∧
      ∀ (I : Type) [Countable I] (Z : I → ℕ → P.Test) (a : I → ℂ),
        (∀ i, WakePoll P (Z i) (a i)) → ∀ g : ℕ → ℕ, StrictMono g → ∃ c : ℕ → ℕ, StrictMono c ∧
          ∀ T : P.Spectrum0 3→Prop, (∀ᵐ x∂P.pillars 3,T x) → ∃ x, T x ∧ JointTuple.{j} P K x ∧
            HoldRead P A (g∘c) x 0 touchPoint u v ∧
            (∀ i, Tendsto (fun r=>P.singleState 3 (g (c r)) x (Z i (g (c r)))) atTop (𝓝 (a i))) ∧
            (∀ i, Tendsto (fun r=> P.singleState 3 (g (c r)) x (pointVote P A u v β i (g (c r)))) atTop
              (𝓝 (meritTally i))) ∧
            Tendsto (fun r=>coupleP P x u v A β (g (c r))) atTop (𝓝 payoff) ∧
            ∀ᶠ r in atTop, ‖payoff‖/2 < ‖coupleP P x u v A β (g (c r))‖ := by
  obtain ⟨P,K,E,u,v,β,f,c,x,i,t,q,Q,l,h,e,k,d,j,w,u',t',z,q',w0,v0⟩:= early_stamp_election.{j} X Mc A hA
  let Z:= pointVote P A u v β; have hv:= point_polls P K A u v β i hA h l z q' w0
  refine ⟨P,K,E,u,v,β,f,i,t,q,Q,l,h,e,w,?_,t',hv,w0,?_,?_⟩
  · intro s W; rw [actor_ancestry]; exact ⟨(u' W s).2,(u' W s).1⟩
  · exact v0.mono fun s ⟨w,u,f,h⟩=>⟨f,w,u,h⟩
  intro I hi V W U g hf; let E':=Sum.elim V Z; let F:=Sum.elim W meritTally
  have hp(i): WakePoll P (E' i) (F i):= by rcases i with i|i; exact U i; exact hv i
  obtain ⟨c,b,p⟩:= q A hA 0 touchPoint u v (I⊕Fin 3) g hf l E' F hp
  refine ⟨c,b,fun T hU=>?_⟩ -- shadow A
  obtain ⟨x,d,uQ,e,v'⟩:= p T ‹∀ᵐ x ∂ P.pillars 3,T x›
  let w(i:Fin 3):= v' (Sum.inr i); have hl:Tendsto (fun i=> coupleP P x u v A β (g (c i))) atTop (𝓝 payoff):=by -- ‹ℝ› danger A now shadow
    have v:=(w 2).sub ((w 0).mul (w 1)); rw [show F (Sum.inr 0)=0 from rfl,zero_mul, sub_zero] at v; exact v
  exact ⟨x,d,uQ,e,fun i=> v' (Sum.inl i),w,hl,hl.norm.eventually (lt_mem_nhds (half_lt_self t'))⟩

#print axioms stage2
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce
