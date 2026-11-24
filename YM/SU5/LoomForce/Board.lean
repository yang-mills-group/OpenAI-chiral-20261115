import YM.SU5.LoomForce.SpinIncome
import YM.SU5.WindTorque.Turbine
/-!
# Buy the normalized Ward mixed moment slots on the physical regulator.

Use staff genealogy at every operand (even pure Tone operands use a geometric
staff for convenience in this version). Use exactly the universal Mark of Turbine.
Tone interfaces with SitSpin (CP1's HoldRead underlying stamps). Slots here already
issue at both the genuine R-scale normalization of the Spin seats (including
extra zoom scale from Lifted covers, note finish factor `fray`) and carrying
Gauge enhancement at two further zoom powers. `meterE`-sized costs will be
needed to make these estimates even across the compass & signed denominator
expenditures. Here Spin leading comparison at **all** such combined poses.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Next.Free Cube Tulip Scroll Spire Pastry RP
  Branch Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry
open Ballad Lifted EmberWind Pressure
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
     ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {I : Type*} (P : Preparation)

-- appointment-independent syntax and law. Publish with finite-Mark support in both gauges.
-- here plan price of list reissued **after** its arity and A & combined footprint exponent.
def spool (R : ℕ) (q : ℝ) (A : Staff) (b : ℕ) (ρ τ : ℝ) : Sewer → Papal.Weaver
  | .some x => (R:ℂ)^3 • SitSpin.raw A.u x A.spin.1 A.spin.2
  | .none => ((q:ℂ)*(R:ℂ)^3) • A.rungWeave ρ b τ

def ream (tag : I → Sewer) (L : List I) (R : ℕ) (q : ℝ) (A : I → Staff) (b : ℕ) (ρ τ : ℝ) :=
  (L.map fun i=> spool R q (A i) b ρ τ (tag i)).prod

omit P in
lemma spoon_scale (W : Cover) (L : Twah.DirSpin) (R : ℕ) (N : Side) (U : ColorL) :
    wrapCurrent W L R N U = (R:ℂ)^3 • wrapCurrent W L 1 N U := by rw [dgC, dgC, Nat.cast_one,one_pow,one_smul]

omit P in
lemma spool_live (R : ℕ) (q : ℝ) (A : Staff) (b : ℕ) (ρ τ : ℝ) (tag : Sewer) (N : Side)
    (X : Fields N) : spool R q A b ρ τ tag N X = mouthBasis R A.u A.spin (q • A.pearl ρ N b τ X.1) N tag := by
  cases tag
  · rw [spool,mouthBasis,map_smul, RCLike.real_smul_eq_coe_smul (K:=ℂ),Pi.smul_apply,Pi.smul_apply, A.onMark,spoon_scale A.u A.spin R]; rw [smul_smul]; rfl
  rfl

omit P in
lemma ream_live (R : ℕ) (q : ℝ)(A : I → Staff) (b : ℕ) (ρ τ : ℝ) (tag : I → Sewer) (L : List I)
    (N : Side)(X : Fields N) : ream tag L R q A b ρ τ N X = platter R
      (fun i=> (A i).u) (fun i=> (A i).spin) tag (fun i=> q • (A i).pearl ρ N b τ X.1) N L := by
  induction L with
  | nil=> rfl
  | cons i L ih=>
    change spool _ _ _ _ _ _ _ _ _ * ream tag L R q A b ρ τ N X = _; rw [spool_live,ih]; rfl

section WickPose

variable {P} {j:ℕ} (Y : P.Course (VolumeCape.Dream.Nimbus j)) (s i k:ℕ)
local notation "N" => Journey.side Y i s
local notation "S" => P.K.j
local notation "J" => (RootBook Y i k s).J.M
local notation "Eₓ" => noble Y s i k

omit Y in
private lemma keepSea {R':Type*}[LinearOrder R'][Fintype R']{x:Wave R'}{P:Op R'}(V:UNI R')(p:Sea P x): Sea (twist V P) (acts (quant V.val) x):=by refine ⟨?_,(act_unit_norm (quantU V) x).trans p.2⟩; change acts _ (acts (quantU V).val x)=_; rw [line_twist, ←Fock.swivel,p.1]; rfl -- Shams private method

-- constant-gauge comparison on Slot costs. needed even though using ind-cube
-- Young adjoints across appointments with different positions in finite reading.
lemma noble_orient (z : SU.E) (g : Seat N → SU.E) (w : ∀ a, g a=z) (F : FC (Single N)) :
    Eₓ (twist (quantU (tradew N g)) F)= Eₓ F := by
  let B:= spar S J (1:Pane N); let v:=flatSea Y s i k
  have he: Lattice.gauge g (1:Pane N)=1 := by funext i; simp [Lattice.gauge, w]
  let U:= quantU (tradew N g); let m:=mateK N
  have hp: twist (tradew N g) B=B := by
    unfold B; exact (P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _).covary (1:Pane N) g (guard0 P.dpos.le) |>.symm |>.trans (by rw [he])
  let x := acts U.val v
  have hx: Sea B x := hp ▸ keepSea (tradew N g) (preparedFlat Y s i k)
  have hm:acts U.val m=m:= mastC g
  have hh (W : Wave (Single N)): inner ℂ m (acts U.val W)= inner ℂ m W := by nth_rw 1 [←hm]; exact act_unit_inner .. -- name
  rw [noble_linear, noble_linear,alley_match (P:=B) (flat_post ..) (preparedFlat ..) hx]
  change (inner ℂ m (acts U.val v))⁻¹*inner ℂ m (acts (twist U F) x)= (inner ℂ m v)⁻¹*inner ℂ m (acts F v)
  unfold x; rw [←Fock.swivel,hh,hh]

lemma gaze_orient (p : Cover) (L : Twah.DirSpin) (R : ℕ) (x : ColorL) (tag : Sewer) (t : SU.E) :
    mouthBasis R p L (SU.group.adjoint t x) N tag =
      twist (quantU (tradew N (fun _ => t))) (mouthBasis R p L x N tag) := by
  cases tag
  · exact current_cov p L R x («N»:=N) (1,1) (fun _=>t)
  next z =>
    let A:= SitSpin.raw p z L.1 L.2
    unfold mouthBasis
    rw [twist_scalar]; exact congrArg ((R:ℂ)^3 • ·) ((SitSpin.voice z p L.1 L.2).2 N (fun _=>t) (1,1))

lemma gaze_plat (V : I → Cover) (L : I→ Twah.DirSpin) (R : ℕ) (tag : I → Sewer) (X : I → ColorL)
    (F : List I) (t : SU.E) :
    platter R V L tag (fun i => SU.group.adjoint t (X i)) N F=
      twist (quantU (tradew N (fun _=>t))) (platter R V L tag X N F) := by
  induction F with
  | nil => exact (map_one _).symm
  | cons u F ih=>
    unfold platter; simp only [List.map_cons,List.prod_cons]; rw [map_mul,gaze_orient Y s i]
    rw [show (List.map _ F).prod=_ from ih]; rfl

lemma orient_quote (p : evenPose Y s i) (V : I → Cover) (L : I→ Twah.DirSpin) (R : ℕ) (tag : I → Sewer) (X : I → ColorL)
    (F : List I) (t : SU.E) (H : Chart (loomZ I)) (e : H= pairPrice R V L N S J) :
    fullPay (componentV fun i => SU.group.adjoint t (X i)) H tag F = fullPay (componentV X) H tag F := by
  rw [e]; let q:= p.1; let r:= preparedFlat Y s i k; let j:= nontrivial_spin P
  rw [←on_docket R V L F _ r j q, ←on_docket R V L F X r j q]
  rw [←noble_linear,←noble_linear, gaze_plat Y s i ]; exact noble_orient Y s i k t _ (fun _=>rfl) _

lemma bought_noble (R : ℕ) (q : ℝ)(A : I → Staff) (b : ℕ) (ρ τ : ℝ) (tag : I → Sewer) (L : List I)
    (X : Fields N) (p : evenPose Y s i) (H : Chart (loomZ I))
    (e : H= pairPrice R (fun i=> (A i).u) (fun i=> (A i).spin) N S J) :
    Eₓ (ream tag L R q A b ρ τ N X) = fullPay
      (componentV fun i => q • (A i).pearl ρ N b τ X.1) H tag L := by
  rw [e,noble_linear,ream_live]; exact on_docket _ _ _ _ _ (preparedFlat Y s i k) (nontrivial_spin P) p.1 _

end WickPose

section
open Pannier.Chancel WakeInvestment Jewel
variable {oL : Side} (W:Staff) (R : ℕ) {q : ℝ} {b d w : ℕ} (ρ τ : ℝ)
  {o : Seat oL} (t:0≤τ) (g:0≤q) (u:W.Pays b w) (p:W.tenancy oL b Staff.clearance d o)
omit P
lemma spool_speak (q : ℝ) (t : Sewer) : Speak (spool R q W b ρ τ t):=by
  cases t with
  | some z => exact ((SitSpin.voice z W.u W.spin.1 W.spin.2).hushed _).2
  | none => intro N x y; simp only [spool, Pi.smul_apply, W.oneVox ρ b τ N x y, twist_scalar]
lemma speak_many (q : ℝ) (tag : I → Sewer) (L : List I) (A : I → Staff) :
    Speak (ream tag L R q A b ρ τ) := by
  induction L with
  | nil=> exact fun N g x=> (map_one _).symm
  | cons i L ih=>
    let C:= ream tag L R q A b ρ τ
    intro N x y; change spool _ _ _ _ _ _ _ _ _*C _ _= twist _ (spool _ _ _ _ _ _ _ _ _ * C _ _)
    rw [map_mul]; exact congrArg₂ (·*·) (spool_speak (A i) R ρ τ (b:=b) q _ N x y) (ih N x y)
include u
lemma spool_label (q : ℝ) (i : Sewer) (K : Calibration) :
    InTest K true (W.skyRent b) false (household K (spool R q W b ρ τ i)) := by
  cases i
  · exact (W.letterBudget ρ K τ u).smul _
  next z =>
    refine ((SitSpin.voice z W.u W.spin.1 W.spin.2).1.narrow _|>.widen |>.smul _).mono
      (singleton_subset_iff.mpr ?_)
    exact pav_mono (show b ≤ b+8 by omega) (u.node _)

include p
lemma spool_span (q : ℝ) (i : Sewer) (K:Calibration)(m:Side)(y:oL=K.c m) : AtSupport false
      (BlockP d o) (spool R q W b ρ τ i oL) := by
  subst oL; have he := spool_label W R ρ τ u q i K |>.support m
  apply he.mono; rw [← (u.withinP W _).1]; exact (Corona.halo_mono (show b+8 ≤ b+Staff.clearance+8 from by omega) (Subset.refl _)).trans p

def capBill (R : ℕ) (q ρ τ : ℝ) := ((R:ℝ)^3 * q *(Staff.regiment*(|ρ| *τ))) + (R:ℝ)^3*(Fintype.card SU.Slot:ℝ)
omit p u in
lemma capBill_pos (R : ℕ) (ρ : ℝ) (g : 0 ≤ q) (t : 0 ≤ τ) : 0 ≤ capBill R q ρ τ := by unfold capBill; have h:= Staff.regge; positivity
include t g
lemma spool_assert (X:Fields oL) (i:Sewer) : Cadre (modesIn _ (BlockP d o)) 2 (capBill R q ρ τ) (spool R q W b ρ τ i oL X):=by
  cases i
  · let A := ((q:ℂ)*(R:ℂ)^3)
    apply ((W.sizing u ρ X t p).scale A).buy le_rfl; unfold capBill; apply (le_add_of_nonneg_right (show 0 ≤ (R:ℝ)^3 * (Fintype.card SU.Slot:ℝ) by positivity)).trans' (le_of_eq ?_) ; unfold A; simp [Real.norm_eq_abs,abs_of_nonneg g,mul_left_comm,mul_comm]
  next z =>
    let A:= SitSpin.cadre z W.u oL W.spin.1 W.spin.2 X; let D:= (R:ℂ)^3
    have he: dBook oL {W.xo} ⊆ BlockP d o := by
      unfold dBook; rw [image_singleton]; apply singleton_subset_iff.mpr
      exact p (Corona.halo_mono (show b ≤ b+Staff.clearance+8 from by omega) (Subset.refl _) ((u.withinP W oL).2.1))
    apply ((A.cover (modes_monotone he)).scale D).buy le_rfl; unfold capBill; refine le_trans (le_of_eq ?_) (le_add_of_nonneg_left (show 0 ≤ _ by have hv:=Staff.regge; positivity))
    unfold D; simp

omit p u
variable (tag : I→ Sewer) (A : I→Staff) (uh:∀ i,(A i).Pays b w)
include uh
lemma full_assert (L : List I) (U : ∀ i,(A i).tenancy oL b Staff.clearance d o) (X:Fields oL):
    Cadre (modesIn _ (BlockP d o)) (2*L.length) ((capBill R q ρ τ)^L.length)
      (ream tag L R q A b ρ τ oL X) := by
  induction L with
  | nil=> simpa [ream] using Cadre.unit (s:=modesIn _ (BlockP d o))
  | cons i L ih=>
    rw [List.length_cons,pow_succ',Nat.mul_succ, add_comm (2*L.length)]
    exact Cadre.and_ (spool_assert (A i) R ρ τ t g (uh i) (U i) X (tag i)) ih
omit t g

lemma full_span (q:ℝ)(L : List I) (U : ∀ i,(A i).tenancy oL b Staff.clearance d o) (K: Calibration)(m:Side)(y:oL=K.c m) :
    AtSupport false (BlockP d o) (ream tag L R q A b ρ τ oL) := by
  induction L with
  | nil=> exact AtSupport.oneM _
  | cons i L ih=> exact (spool_span (A i) R ρ τ (uh i) (U i) q (tag i) K m y).mulM ih

def wholeSky (A : I → Staff) (b : ℕ) (L : List I) := (L.toFinset).biUnion fun i=> (A i).skyRent b
lemma ream_label (q:ℝ) (L : List I) (K : Calibration) :
    InTest K true (wholeSky A b L) false (household K (ream tag L R q A b ρ τ)) := by
  induction L with
  | nil => exact InTest.one
  | cons i L ih=>
    apply ((spool_label (A i) R ρ τ (uh i) q (tag i) K).mono ?_).mul (ih.mono ?_)
    · unfold wholeSky; rw [List.toFinset_cons, biUnion_insert]; exact subset_union_left
    unfold wholeSky; rw [List.toFinset_cons, biUnion_insert]; exact subset_union_right

end
#print axioms full_span
#print axioms ream_label
#print axioms full_assert
#print axioms orient_quote
#print axioms bought_noble
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
