import YM.SU5.WakeFields.FrameWake
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise

open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke.Jewel.Program
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis Gleam Tempest
open WakeInvestment Gleam.Wake
open Lamour Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
open Window Ballad Hiro EmberWind EmberWind.MixedCards
open EmberWind.Staff (Beacon)
open Regis.Wake (Paint)

variable (s i k : ℕ)
variable {x A B ρ α E v : ℝ} {J : Type*} [Fintype J]
variable (U : J → EmberWind.Staff) (D : J → MixedCards.Ticket) (L : List J)
local notation "Γ" => side Y i s
local notation "X_" t:max => hat P.R.L P.x t
local notation "Mana" => MixedCards.topFare
local notation "Bills" => 2* L.length
local notation "T" => SU.group.ColorIndex

abbrev brandR (x : ℝ) := 1+2*Real.sqrt x*temp x
lemma brand_near (x : ℝ) : 1 ≤ brandR x := le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Work.E04.temp_nonneg _))
lemma brand_hub (h : |ρ| ≤ 2*bornQ P s) : |ρ| * temp (X_ s) ≤ brandR (X_ s) :=
  (mul_le_mul_of_nonneg_right h (Work.E04.temp_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)

lemma measurable_pearl (U : EmberWind.Staff) (n : Side) (r) (ρ t) : Measurable (U.pearl ρ n r t) := by
  let s := setOf fun x : Pane n => pingS t (U.gateS r n) x
  let F : Pane n → ColorL := U.pearl ρ n r t
  change Measurable F
  rw [show F = s.indicator (U.edgeBudget ρ n) from rfl]
  exact (EmberWind.Staff.edge_budget_c U ρ).measurable.indicator ping_o.measurableSet

-- costs for geometry and fee uniform e not changing with n. simplified growth criterion.
abbrev cardEst (e:ℕ) := (e+e+1)^4
abbrev cardR (e:ℝ) := (e+e+1)^4
abbrev bankR (E : ℝ) (m : ℕ) (r : ℝ) := (r* (Fintype.card (SpinIdx × SU.Slot):ℝ)+1)^(2*m) * flatTicket E^(2*m)
lemma purchase_eq (e m : ℕ)(E : ℝ) : bankR E m (cardR (e:ℝ)) = standardTuition E m (cardEst e) := by
  unfold bankR cardR standardTuition cardEst sizeRent modeCap; push_cast; rfl
lemma cards_mon {x y : ℝ} (z:0≤x)(p:x≤y): cardR x ≤ cardR y := by unfold cardR; gcongr
lemma bankR_nonnegative (E m) (r:ℝ) (h:0≤r): 0 ≤ bankR E m r:= by unfold bankR; apply mul_nonneg; positivity; exact even_two_mul m |>.pow_nonneg _
lemma bank_mon (E m){x y : ℝ}(h:0 ≤ x)(u:x ≤ y) : bankR E m x ≤ bankR E m y :=by unfold bankR; apply mul_le_mul_of_nonneg_right; gcongr; exact even_two_mul m |>.pow_nonneg _
lemma cardBound (e : ℕ) (o : Seat n) : (BlockP e o).card ≤ cardEst e := by
  simpa [BlockP,cardEst] using Corona.halo_size ({o}:Finset (Seat n)) e

abbrev triad (x b : ℝ) := EmberWind.Staff.armRent b (skyline x) (brandR x) b
lemma triad_p (x b : ℝ) (v : 0≤b): 0≤ triad x b := by
  have hc:= SU.group.colorScale_pos; have hx:= skyline x; have hf: 0<skyline x:=chip_pos ..
  unfold triad Staff.armRent; have hg:= zero_lt_one.trans_le (brand_near x); positivity

lemma tempo (I : ℝ) (m : ℕ) (h : 0<I) (E : ℝ) (a : ℕ) (P : Preparation) :
    let A := (12*I+1)*(m+1)+4
    ∀ᶠ s in atTop, let x := hat P.R.L P.x s; let Q := sPow P s I; let T' := sPow P s A; let B := (Mana* brandR x)^m;
        2*Q ≤ T' ∧ cardR Q ≤ T' ∧ a ≤ T' ∧ Staff.clearance ≤ radiusB x ∧
        B ≤ T' ∧ bankR E m (cardR Q)*((Mana*toneFare)^m*(1+m*toneFare)) ≤ T' ∧
        bankR E m (cardR Q) * B ≤ T' ∧
        bankR E m (cardR Q) * ((m:ℝ) * B * triad x Q) ≤ scratch x := by
  intro A
  let q(x:ℝ) := BProof.coin x 0 I 0; let f(x:ℝ) := cardR (q x)
  have Q : Worth.Pays 0 I 0 q := Pays.whole ..
  let u:= ((Fintype.card (SpinIdx × SU.Slot)):ℝ)
  have F : Worth.Pays 0 (I*4) 0 f := by
    simpa only [Nat.cast_ofNat,zero_mul] using Pays.pot (Pays.plus (Pays.plus Q Q) (Worth.Pays.merit (constant 1) (Or.inr (Or.inl ⟨rfl,h⟩)))) 4
  let R(x:ℝ) := bankR E m (f x)
  have hn : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have B : Worth.Pays 0 (I*4*(2*m:ℕ)) 0 R := by
    have hg : Worth.Pays 0 (I*4) 0 (fun x:ℝ=> f x*u+1) := Pays.plus (Pays.right u F) (Worth.Pays.merit (constant 1) (Or.inr (Or.inl ⟨rfl,by linarith only [h]⟩)))
    simpa only [zero_mul] using Pays.right (flatTicket E^(2*m)) (Pays.pot hg (2*m))
  have c : Worth.Pays 0 1 0 brandR := by
    refine Pays.plus (Worth.Pays.merit (constant 1) (Or.inr (Or.inl ⟨rfl,zero_lt_one⟩)))
      (Pays.fix (Pays.scale 2 (whole 0 1 0)) ((eventually_gt_atTop (0:ℝ)).mono fun x p=> ?_))
    change 2*_ = 2* Real.sqrt x*temp x
    rw [Head.Garland.era x p,←BProof.thresh_eq p,BProof.thresh,mul_assoc,BProof.coin_mul]; norm_num
  let D(x:ℝ) := (MixedCards.topFare* brandR x)^m
  have Y : Worth.Pays 0 (m:ℝ) 0 D := by simpa only [zero_mul,one_mul] using Pays.pot (Pays.scale Mana c) m
  have pA : 0<A:=by unfold A; positivity
  have hY : (m:ℝ) < A:=by unfold A; nlinarith only [hn,h]
  have hB : I*4*(2*m : ℕ) + m < A := by unfold A; push_cast; nlinarith only [hn,h]
  have hC : I*4 < A:=by unfold A; nlinarith only [hn,h]
  let W : ℝ := (Mana*toneFare)^m*(1+m*toneFare)
  have F1 : Worth.Pays (-(120000:ℝ)/400000) (I+1) 0 (fun x=> triad x (q x)) := by
    simpa only [zero_add,add_zero] using Pays.times (Pays.times (Pays.scale (2*SU.group.colorScale) (Pays.plus Q (Pays.scale 4 Q))) (Pays.whole (-120000/400000) 0 0)) c
  have F2 := Pays.leap (p:=0) (q:=0) (w:=-(7:ℝ)/400000) (Pays.times B (Pays.times (Pays.scale (m:ℝ) Y) F1)) (Or.inl (by norm_num))
  filter_upwards [(turnover P).eventually (leap (p:=A) (w:=0) (q:=0) (Pays.scale 2 Q) (Or.inr (Or.inl ⟨rfl,by linarith only [hC,h]⟩))),
    (turnover P).eventually (leap (p:=A) (w:=0) (q:=0) F (Or.inr (Or.inl ⟨rfl,hC⟩))),grow_e A a pA P,(turnover P).eventually (Work.E08.eventual_radiusB Staff.clearance),
    (turnover P).eventually (leap (p:=A) (w:=0) (q:=0) Y (Or.inr (Or.inl ⟨rfl,hY⟩))),
    (turnover P).eventually (leap (p:=A) (w:=0) (q:=0) (Pays.right W B) (Or.inr (Or.inl ⟨rfl,by linarith only [hB,hn]⟩))),
    (turnover P).eventually (leap (p:=A) (w:=0) (q:=0) (Pays.times B Y) (Or.inr (Or.inl ⟨by norm_num,hB⟩))),
    (turnover P).eventually F2] with s p0 p1 p2 p3 p4 p5 p6 p7
  exact ⟨p0,p1,p2,p3,p4,p5,p6,p7⟩

#print axioms tempo
end Yoke.Jewel.Program
end YM.CF.Py.Rate.LocalLimit.Preparation
