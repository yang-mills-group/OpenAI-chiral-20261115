import WakeRoad.Prayer
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Vacancy Tapestry
open CF.Pannier.Chancel
open Preparation.Yoke EmberWind Jewel
open Lamour.Bridge.Celeste Morn
open Ballad
open SpinReceipt Shuttle
open Papal (Weaver household)
open WakeInvestment
open Gleam Gleam.Wake YM.WakeRoad CF.Hiro Hearth
open Precision Regis.Head.Brecht Regis.Circuit Exterior
namespace GramSignal
open Dial Pressure
open Stationary (Gaia)
set_option quotPrecheck false
open Onyx
variable {E:ℝ}{Mc n:ℕ}{P:Spine}{K:P.Register} {r f:ℕ→ℕ}
variable {β:ℕ→ℝ} {I:ℝ}
/-- two spatially oriented actual weight-five staff appointments in time layout and
   their Wick answer, ingredients before introducing contour prescription -/
structure Morning (P:Spine)(I:ℝ) where
    position: Fin 2 → Gaia
    tests: ℕ→ Fin 2→ Cover
    faces : Fin 2 → PlaqAxes
    spatial(i:Fin 2): (faces i).val.1≠3 ∧ (faces i).val.2≠3
    budget(i:Fin 2) : Appoint P.par I (fun s=>tests s i) (position i)
    offsite: Injective position

namespace Morning
variable (V:Morning P I)
abbrev ask (β:ℕ→ℝ)(i:Fin 2)(s:ℕ):=ballotT P β (V.faces i) s (V.tests s i) (zoomR P.par I s)
abbrev expect :ℂ:= shotR (X:=V.position 0 - V.position 1) 0 0 * speckleV (V.faces 0) (V.faces 1) SU.group (V.position 0 - V.position 1)
lemma table_here (β:ℕ→ℝ)(s:ℕ) : ballotDuet P V.faces (V.tests s) β I s= V.ask β 0 s*V.ask β 1 s:=by
 apply Subtype.ext; let x:= staffWeight (zoomR P.par I s); let f(i):= tee P β s (V.tests s i) (V.faces i); change x^2 • household P.calibration (YM.WakeRoad.serve f)= (x • household _ (f (0:Fin 2)))*(x • household _ (f (1:Fin 2))); rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,pow_two]; apply congrArg; unfold YM.WakeRoad.serve; rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]; simp only [List.prod_cons,List.prod_nil,mul_one]; rfl

variable (Q: Spine.PreparedInvestment P K E Mc) (HM:Pooling P.run (P.period∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) f β) (p:0<I)(W:P.PhysicalWakeGram)
include Q HM p W
lemma recipe :
    (∀ i, Spine.WakePoll P (V.ask β i) 0) ∧ Spine.WakePoll P (fun s=>V.ask β 0 s * V.ask β 1 s) V.expect ∧ ∀ i s, CovCover P.calibration (V.ask β i s).val ∧ InTest P.calibration true (skyDeck (nodeC (V.tests s i)) 12) false (V.ask β i s).val:= by
 let L:= (0:Fin 2→Ballad.Twah.DirSpin); let D:=V.faces; let a:=V.tests; let O:= V.position; let u:=fun s=> a s 0; let v:=fun s => a s 1
 let H:= afternoon Q HM a L D p V.budget V.offsite; have he: Tendsto (partyValue L D a P β I) atTop (𝓝 V.expect):=by
    have hp:= (ion L D a p V.budget 0 1).1
    obtain ⟨hx,g,q⟩:= local_value I p u v hp (sub_ne_zero.mpr (V.offsite.ne (by decide : (0:Fin 2)≠1))) 0 0 (D 0) (D 1) HM W
    have t:= hx.add (g.mul q); simp only [mul_zero,add_zero] at t
    refine t.congr (fun s=>?_)
    let r:= zoomR P.par I s
    change (staffCov P β 4 _ _ _ s)+_= _; unfold staffCov; rw [sub_add_cancel]; unfold twoStaff partyValue; congr 2
    unfold crewFilm YM.WakeRoad.serve; rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero]; simp only [List.prod_cons,List.prod_nil,mul_one]; rfl
 have ht:=duet_poll D V.spatial Q HM a p V.budget V.offsite
 change Spine.WakePoll P _ (duoTarget O _ D) at ht; rw [show duoTarget O _ D=_ from tendsto_nhds_unique H he,show (fun s=>ballotDuet P V.faces (V.tests s) β I s)=_ from funext (table_here V β)] at ht
 refine ⟨fun i=> staffPoll p _ (V.spatial i).1 (V.spatial i).2 (V.budget i) HM W,ht,fun i s=>?_⟩
 let x:= staffWeight (zoomR P.par I s); let f:=localStaff (V.tests s i) 0 (V.faces i); change CovCover _ (x • household P.calibration (choiceWeave P β f 4 s)) ∧ _
 have u:= ready_local (V.tests s i) (0:Ballad.Twah.DirSpin) (V.faces i); have hv:= Staff.registration f (κFix β s) (temp (hat P.par.R.L P.par.x s)) P.calibration u
 refine ⟨fun n g y=> ?_, .smul _ (f.letterBudget _ P.calibration _ u)⟩; simp only [Pi.smul_apply,choiceWeave,twist_scalar,hv n g y]
#print axioms recipe
omit Q HM W
variable (P I)
def pinM (p:0<I):Morning P I where
    position:= ![corner P.pianist,0]
    tests:=fun s=> ![testSite P I s,0]
    faces:=fun _=> Prototype.goldF
    spatial:=fun _=> ⟨by decide,by decide⟩
    budget:=fun i=>by have h:= appointments (P:=P) I p; fin_cases i; exact h.1; exact h.2
    offsite:=by
       intro i j; fin_cases i <;> fin_cases j
       · exact fun _=>rfl
       · exact fun h=> (P.service_space h).elim
       · exact fun h=> (P.service_space h.symm).elim
       exact fun _=>rfl
omit p in
lemma priced (p:0<I): (pinM P I p).expect=P.supper:=by unfold expect; change shotR _ _ (X:=corner P.pianist-0) * speckleV _ _ _ (corner _-0)= _; rw [sub_zero]; rfl
abbrev covPct (V:Morning P I)(b:ℕ→ℝ)(x:P.Spectrum0 3)(j:Axis)(s:ℕ):=let σ:=P.singleState j s (P.otherSpectrum 3 j x); σ (V.ask b 0 s*V.ask b 1 s) - σ (V.ask b 0 s)*σ (V.ask b 1 s)

universe u₀
-- keep countably many other layout questions or polls on exactly these phases. phase quotas already bought by wakeElection & hold at pincorner before election
omit p
theorem momentsIssued (X:TintDemand)(M:ℕ):∃ (P:Spine)(K:P.Register)(E:ℝ), P.PreparedInvestment K E M ∧ PureForce.CakeL.SignedPoseBudget P ∧ P.QualifiedWakeReadout.{u₀} K ∧ P.PhysicalWakeGram ∧ ∀ (I:ℝ)(p:0<I)(f r:ℕ→ℕ), StrictMono f → StrictMono r →
    ∀ (J A:Type)[Countable J][Countable A](T:J→ ℕ→P.Test)(Z:J→ℂ), (∀ i, Spine.WakePoll P (T i) (Z i)) → ∀ V:A→Morning P I,
    ∃ (a b:ℕ→ℕ)(β:ℕ→ℝ), StrictMono a∧StrictMono b∧ Pooling P.run (P.period∘ P.projection.rows) (P.cutoff ∘ P.projection.columns) (f ∘ a) β ∧ ∀ U:P.Spectrum0 3→Prop, (∀ᵐ x∂P.pillars 3,U x)→ ∃ x, U x ∧ Spine.JointTuple.{u₀} P K x ∧ Spine.HoldRead P I (r ∘ b) x (corner P.pianist) 0 (testSite P I) 0 ∧
      (∀ i (j:Axis), Tendsto (fun s=>P.singleState j (r (b s)) (P.otherSpectrum 3 j x) (T i (r (b s)))) atTop (𝓝 (Z i))) ∧
      (let h(W:Morning P I):Prop:= ∀ j:Axis,Tendsto (W.covPct P I β x j ∘ r ∘ b) atTop (𝓝 W.expect) ∧ ∀ i, Tendsto (fun s=>P.singleState j (r (b s)) (P.otherSpectrum 3 j x) (W.ask β i (r (b s)))) atTop (𝓝 0)
       (∀ i,h (V i)) ∧ h (pinM P I p) ∧ (pinM P I p).expect=P.supper ∧ 0< ‖P.supper‖ /2 ∧ ∀ j:Axis,∀ᶠ s:ℕ in atTop, ‖P.supper‖/2 < ‖(pinM P I p).covPct P I β x j (r (b s))‖ ∧ ∀ x ∈ printedDeck P (r (b s)) (dinner P I true (r (b s))), ∀ y∈printedDeck P (r (b s)) (dinner P I false (r (b s))), 1/precisionAt P.par (r (b s)) ≤ x 3-y 3) :=by
 obtain ⟨P,K,E,G,H,T,F⟩:= Spine.wakeElectionWithPhysicalGram.{u₀} X M
 refine ⟨P,K,E,G,H,T,F,fun I p f r t k J A _ _ R z h V=>?_⟩
 obtain ⟨a,β,C,D⟩:= Pooling.fettle P.run P.history t
 let Z(x:Option A):Morning P I:=Option.elim x (pinM P I p) V
 let C'(x:Option A × Option (Fin 2))(s:ℕ):P.Test:=let i:=Z x.1;x.2.elim (i.ask β 0 s*i.ask β 1 s) (fun j=>i.ask β j s)
 let T'(x:Option A × Option (Fin 2)):ℂ:=x.2.elim (Z x.1).expect (fun _=>0)
 have h' (i:Option A × Option (Fin 2)): Spine.WakePoll P (C' i) (T' i):=by
    rcases i with ⟨i,_|j⟩; exact ((Z i).recipe G D p F).2.1; exact ((Z i).recipe G D p F).1 j
 let U:=Option A × Option (Fin 2); obtain ⟨b,kB,J'⟩:= T I p _ _ _ _ (J⊕U) r k (appointments I p) (Sum.elim R C') (Sum.elim z T') (fun i=>Sum.rec h h' i)
 refine ⟨a,b,β,C,kB,D,fun u v=>?_⟩
 obtain ⟨x,w,x',y,h₁⟩:= J' u v; have spin_all(i)(a:Axis): Tendsto (fun s=> P.singleState a (r (b s)) (P.otherSpectrum 3 a x) ((Sum.elim R C') i (r (b s)))) atTop (𝓝 ((Sum.elim z T') i)):=by simp_rw [P.single_agrees]; exact h₁ i
 refine ⟨x,w,x',y,fun i j=> spin_all (Sum.inl i) j,?_⟩
 intro q; have hp(i:Option A):q (Z i):=by
    intro j; have he(k):Tendsto (fun s=> P.singleState j (r (b s)) (P.otherSpectrum 3 j x) ((Z i).ask β k (r (b s)))) atTop (𝓝 0):=spin_all (Sum.inr (i,some k)) j
    have h0:Tendsto (fun s=> P.singleState j (r (b s)) (P.otherSpectrum 3 j x) ((Z i).ask β 0 (r (b s)) * (Z i).ask β 1 (r (b s)))) atTop (𝓝 (Z i).expect):=spin_all (Sum.inr (i,none)) j
    refine ⟨?_,he⟩; have hx:= h0.sub ((he 0).mul (he 1)); simp only [mul_zero,sub_zero] at hx; exact hx
 refine ⟨fun i=>hp (some i),hp none,priced ..,half_pos P.supper_money,fun j=>?_⟩
 have he:Tendsto (covPct P I (pinM P I p) β x j ∘r∘b) atTop (𝓝 ((pinM P I p).expect)):= (hp none j).1
 rw [priced] at he; exact (he.norm.eventually (lt_mem_nhds (half_lt_self P.supper_money))).and ((k.comp kB).tendsto_atTop.eventually (separated_decks I p))

#check @evening
#check @duet_poll
#check @recipe
#check @momentsIssued
#print axioms momentsIssued
end Morning
end GramSignal
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

