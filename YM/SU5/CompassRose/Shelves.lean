import YM.SU5.CompassRose.Atelier

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open WakeInvestment Gleam Gleam.Wake Regis.Wake
open Lamour (alleyR)
open scoped ContDiff

variable (P : Spine) (v : ℕ → ℕ) (z : ℕ × ℕ)
local notation "Y" => P.run
local notation "Λ" => P.par
local notation "K" => P.calibration
local notation "pᵥ" z:max => Rose.period P (v ((z:ℕ×ℕ).2))
local notation "cᵥ" z:max => Rose.cutoff P (v ((z:ℕ×ℕ).2))
local notation "O" z:max => orbitSize P v z
noncomputable abbrev ζbank := Lamour.alleyR (Dial.mateK (orbitSize P v z)) (flatSea Y z.1 (pᵥ z) (cᵥ z))
local notation "Z@" z:max => ζbank P v z
variable {E u₀ : ℝ}
lemma jet_shoot (a : Investment P.par E u₀) (d : ℕ) (B : Support (More (O z))) (c : ℝ)
    (X : FC (Single (O z))) (p : Cadre (modesIn _ B) d c X) :
    ‖(Z@ z) X‖ ≤ c*(sizeRent d B.card * flatTicket E^d) := by
  have he := noble_linear Y z.1 (pᵥ z) (cᵥ z) X
  rw [← show noble Y z.1 (pᵥ z) (cᵥ z) X = _ from he,←mul_assoc]
  let q := (p.output.expend le_rfl (mul_le_mul_of_nonneg_left (size_issue (n:=O z) (S:=B) le_rfl d) (pamphlet p)))
  exact le_trans (noble_bound Y _ _ _ X 0) (q.post _ (invest_W Y _ _ _ a 0 (by simp)) (flatT_pos a))

lemma jet_invariant (e : SU.E) (X : FC (Single (O z))) :
    (Z@ z) (twist (quantU (tradew (O z) fun _ => e)) X)=(Z@ z) X := by
  let W := pupil P z.1 (v z.2)
  let M := W.J.M; let i := pᵥ z; let s := z.1; let q := O z
  let g : Seat q → SU.E := fun _ => e
  let a := quantU (tradew q g); let x := flatSea Y z.1 i (cᵥ z); let y := Dial.mateK q
  have p : Guard (1:Pane q) (Λ).d := guard0 (Λ).dpos.le
  have he := Hive.honey_x (m:=Vale.mesh ((Y).ir i) (Λ).R.L s) (M:=M) ((Λ).W.pearl) ((Λ).V.note)
    ((Λ).J.gran.trans (((Y).voyage i).ownership s).size) (by rw [(Λ).kJ]; norm_num) p g
  rw [show gauge g (1:Pane q)=1 by ext1; simp [Lattice.gauge,g]] at he
  have hp : x = (acts a.val x) := he
  have ht : y = acts a.val y := (mastC g).symm
  have hZ : inner ℂ y (acts (twist a X) x)=inner ℂ y (acts X x) := by
    nth_rw 1 [ht,hp]; rw [←Fock.swivel]; exact act_unit_inner ..
  let g(Z : FC (Single q)) := (Z@ z) Z
  unfold ζbank; rw [←noble_linear,←noble_linear]; exact congrArg (fun t => t/inner ℂ y x) hZ
section shelves
-- Witnessed visibility at changing positions on ground trajectory. May carry any boat with
-- variable face-coordinate count that buys the permit. Compose only in a common room B.
universe u'
structure Foyer where
  faces : (ℕ × ℕ) → Type u'
  finite (z : ℕ × ℕ) : Fintype (faces z)
  anchor : ∀ z : ℕ × ℕ, Seat (O z)
  B : ∀ z : ℕ × ℕ, Support (More (O z))
  ship : ∀ z : ℕ × ℕ, Gleam.Wake.Vessel SU.group (More (O z)) (faces z)
  pedestal : Threading
  width : ℕ × ℕ → ℕ
  threshold : ℝ
attribute [instance] Foyer.finite

variable (S : Foyer.{u'} P v)
abbrev panelVal (e : ℕ × ℕ) := (S.faces e → ℝ) → FC (Single (O e))
local notation "gB" z:max => S.B z
local notation "H@" z:max => hat P.par.R.L P.par.x ((z:ℕ×ℕ).1)

structure LaunchFee : Prop where
  cards : Easy P (fun z => ((Fintype.card (S.faces z)):ℝ))
  deck_size : Easy P (fun z => ((gB z).card:ℝ))
  horizon : Easy P (fun z=> (S.width z:ℝ))
  positive : 0 < S.threshold
  small : S.threshold ≤ 1
  lives : ∀ᶠ z in bobbin, (S.ship z).Ship (gB z) (radiusB (H@ z)) ∧ (∀ j,cows j (gB z) (S.width z)) ∧
    |S.pedestal z| ≤ 2*bornQ P.par z.1

abbrev drawn (z : ℕ × ℕ) := WellDrawn Y z.1 (pᵥ z) (cᵥ z) S.threshold (gB z)
abbrev atDeck (z : ℕ × ℕ) := (S.ship z).material (S.pedestal z)
variable (F : ∀ e : ℕ × ℕ, panelVal P v S e) (X : ∀ z:ℕ × ℕ, Mark (orbitSize P v z))
structure Board (d m : ℕ) : Prop where
  credentials : ∃ x y : Threading, Easy P x ∧ Deep P y ∧
    ∀ᶠ z in bobbin, ∃ G, Hatch (gB z) (S.anchor z) (drawn P v S z) (atDeck P v S z) (X z) (F z) G (x z) (y z) d m

-- unsettled params x y captured implicitly by usage.
variable {d d' m m' : ℕ}
variable {P S F X}
namespace Board
variable {v} {S:Foyer P v} {F:∀e,panelVal P v S e} {X:∀z,Mark (orbitSize P v z)}
variable {G:∀ z,panelVal P v S z}{X':∀ z,Mark (orbitSize P v z)}
lemma mul (p : Board P v S F X d m) (q : Board P v S G X' d' m') :
    Board P v S (F*G) (X*X') (d+d') (m+m') := by
  obtain ⟨A,a,h,t,b⟩:=p.credentials; obtain ⟨C,c,u,w,e⟩:=q.credentials
  refine ⟨2*(A*C), a*C + A*c,Easy.mul (Loan.constant 2 P) (Easy.mul h u), (Easy.deep' u t).add (Easy.deep h w),?_⟩
  filter_upwards [b,e] with i t p; obtain ⟨c,h⟩:=p; obtain ⟨e,v⟩:=t
  exact ⟨e*c,v.mul h⟩
lemma smul (p : Board P v S F X d m) {z : ℕ × ℕ → ℂ} (u : Easy P (fun i=> ‖z i‖)) :
    Board P v S (fun i=> z i • F i) (fun i=> z i • X i) d m := by
  obtain ⟨A,a,h,t,b⟩:=p.credentials; refine ⟨_,_,Easy.mul u h,Easy.deep u t,b.mono fun i t=>?_⟩; obtain ⟨G,e⟩:=t; exact ⟨z i • G,e.smul _⟩
lemma unit : Board P v S 1 1 0 0 :=
  ⟨1,0,Loan.constant 1 P, ⟨⟨0, Eventually.of_forall fun i=>by change |(0:ℝ)| ≤ _; rw [abs_zero]; exact (book_pos ..).le⟩⟩, Eventually.of_forall fun _=> ⟨_, Hatch.unit ..⟩⟩
lemma walks {I:Type*}(U:I→∀ z,panelVal P v S z)(W:I→∀ z,Mark (O z))(L:List I)(h:∀ i∈L, Board P v S (U i) (W i) d m) : Board P v S (L.map U).prod (L.map W).prod (L.length*d) (L.length*m) := by
  induction L with
  | nil=>simpa only [List.map_nil,List.prod_nil,List.length_nil,zero_mul] using (Board.unit (S:=S))
  | cons i L p=> simpa only [List.map_cons,List.prod_cons,List.length_cons,Nat.succ_mul,add_comm (L.length * _)] using (h i List.mem_cons_self).mul (p (fun i v=>h i (List.mem_cons_of_mem _ v)))
end Board

variable (P)
-- expenditure after evaluation. no volume-degree powers in `S` change the constant I.
open CF.Buffered.Afterglow.Tower
local notation "R" A:max z:max => sPow P.par ((z:ℕ×ℕ).1) A

open Lamour.Bridge.Celeste.Clock
variable (S : Foyer.{u'} P v) (u : LaunchFee P v S)
include u
lemma shift_dues (d : ℕ) (E : ℝ) : Easy P fun z=> sizeRent d (S.B z).card * flatTicket E^d := by
  let V : ℝ := Fintype.card (SpinIdx × SU.Slot)
  let X(z) := ((S.B z).card:ℝ); let X' (z : ℕ × ℕ) := V
  have he:=Easy.mul u.deck_size (Loan.constant V P)
  have hp : Easy P (X*X'+1) := he.add (Loan.constant 1 P)
  convert Easy.mul (Loan.pow hp d) (Loan.constant (flatTicket E^d) P) using 1; ext z; change _=(X z*V+ (1:ℝ))^d*_; unfold sizeRent modeCap X V; push_cast; rfl

lemma Board.price {w E : ℝ} {f g : ℕ} {F : ∀ z,panelVal P v S z} {X:∀ z,Mark (O z)}
    (a : Investment P.par E w) (T : Board P v S F X f g) : ∀ᶠ I : ℝ in atTop, ∀ᶠ z in bobbin,
    ∃ J, J.S=S.B z ∧ J.x=X z ∧
    Broom Y z.1 (pᵥ z) (cᵥ z) (S.ship z) I S.threshold (S.pedestal z) (S.width z) f g J ((Z@ z) ∘ F z) := by
  obtain ⟨b,c,hb,hc,h⟩:=T.credentials
  let V(z):= sizeRent f ((S.B z).card)* flatTicket E^f
  let t : Easy P V := shift_dues P v S u f E -- arg order?
  obtain hp := Loan.scratched (Easy.deep' t hc)
  filter_upwards [Loan.secondary (Easy.mul hb t),Loan.secondary hb,Loan.secondary u.horizon,Loan.secondary u.deck_size, Loan.secondary u.cards] with I e g' k w o
  filter_upwards [e,g',k,w,o,h,u.lives,hp] with z e g' k w o p u hp
  obtain ⟨D,h⟩:=p
  let O':=S.anchor z; let J : Hookah (O z) := ⟨X z,S.B z,O'⟩
  let Φ := (Z@ z) ∘ D
  have hΦ (x : Pane (O z)) : ‖Φ x‖ ≤ R I z := (jet_shoot (X:=D x) P v z a f _ _ (h.sample x)).trans e
  let H := S.ship z; let Φ' := (Z@ z) ∘ F z
  have t0 := ‹LaunchFee P v S›.small
  refine ⟨J,rfl,rfl,h.first,h.bonds,fun x=>(h.full x).buy le_rfl g',u.2.1,k,w,Φ,⟨u.1,⟨?_,?_,?_⟩,o,t0,u.2.2,?_,?_,hΦ,?_⟩,?_⟩
  · exact ((Z@ z).toContinuousLinearMap.restrictScalars ℝ |>.contDiff).comp h.promise.bright
  · intro K' t x v'; exact (jet_shoot (X:=F z x) P v z a f _ _ (h.promise.worth K' t x v')).trans (le_trans (b:= b z*V z*K'^g) (le_of_eq (by unfold V; ring)) (mul_le_mul_of_nonneg_right e (pow_nonneg (zero_le_one.trans t) _)))
  · intro K' t x y v' w'; rw [comp_apply,comp_apply,←map_sub]; apply (jet_shoot P v z a f _ _ _ (h.promise.price K' t x y v' w')).trans; apply le_trans (b:= b z*V z*K'^g*‖x-y‖) (le_of_eq (by unfold V; ring)); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e (pow_nonneg (zero_le_one.trans t) _)) (norm_nonneg _)
  · exact ⟨(Z@ z).toContinuousLinearMap.continuous.measurable.comp h.texture,_,hΦ⟩
  · intro g u; unfold Φ Function.comp; rw [h.global, jet_invariant]
  · intro x p; rw [comp_apply,show Φ x=(Z@ z) (D x) from rfl,←map_sub]; exact (jet_shoot P v z a f _ _ _ (h.ends x p)).trans hp
  · intro x p; rw [noble_linear] -- goal subtraction estimate
    change ‖(Z@ z) _-(Z@ z) _‖ ≤ _; rw [←map_sub]; exact (jet_shoot P v z a f _ _ _ (h.crop x p)).trans hp

lemma Board.purchase {w E : ℝ} {f g : ℕ} {F : ∀ z,panelVal P v S z} {X:∀ z,Mark (O z)}
    (a : Investment P.par E w) (p : Dispatchers P.par) (q : Meritorious P.par) (l : StrictMono v)
    (T : Board P v S F X f g) : ∀ᶠ z in bobbin,
    ‖Journey.compass Y (pᵥ z) (cᵥ z) z.1 (X z)-seatT Y z.1 (pᵥ z) (cᵥ z) (S.ship z) ((Z@ z) ∘ F z) (S.pedestal z)‖ ≤ chip (hat P.par.R.L P.par.x z.1) (-3) := by
  obtain ⟨I,q',u'⟩ := ((T.price P v S u a).and (eventually_gt_atTop (0:ℝ))).exists -- order?
  unfold bobbin; rw [eventually_bind]; simp_rw [eventually_map]
  filter_upwards [bobbin_for.mp q', Yoke.sails.{u'} Y P.law P.history a p q f g u' u.positive u.small] with s q' h
  filter_upwards [l.tendsto_atTop.eventually h,q'] with n q v'
  obtain ⟨J,_,r,G⟩:=v'; rw [←r]; exact q.2.2 _ _ _ _ _ G
-- #print axioms Board.purchase
end shelves
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
