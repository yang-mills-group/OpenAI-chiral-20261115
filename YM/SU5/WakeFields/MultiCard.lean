import YM.SU5.WakeFields.BodyWake
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
local notation "Wn" => EmberWind.Staff

lemma paint_more {F : (J→ℝ)→ℂ}{A A' : ℝ}{m}(p:Paint F m A)(g:A ≤ A') : Paint F m A' :=
  ⟨p.bright,fun K t x h => (p.worth K t x h).trans (mul_le_mul_of_nonneg_right g (by positivity)),
             fun K t x y h l => (p.price K t x y h l).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right g (pow_nonneg (zero_le_one.trans t) _)) (norm_nonneg _))⟩


lemma ship_scene (U : J → Wn) (V : Side) (r e w : ℕ)(o: Seat V)
    (u:∀ i,(U i).Pays r w) (p:∀ i,(U i).tenancy V r EmberWind.Staff.clearance e o) :
    (hallL U V).Ship (BlockP e o) EmberWind.Staff.clearance := by
  have he(z:materialL J)(t:Signed)(b:Site (More V)):
        touched ((hallL U V).ua z) ⊆ BlockP e o ∧ ((hallL U V).crew z t).length ≤ EmberWind.Staff.clearance ∧
        ((hallL U V).viewFace z t b).1 ∈ (BlockP e o).image (affine t b) :=
    EmberWind.Staff.withinShip (U z.1) _ _ rfl (u _) (p _) t b
  exact ⟨fun i => (he i 1 o).1, fun i t b => (he i t b).2.2, fun i t => (he i t o).2.1⟩

lemma measurable_beacon (V : Side) (U : Wn) (o : Seat V) (ρ : ℝ) (Θ : ℝ) (r : ℕ) : Measurable (fun x => Beacon U o (U.pearl ρ V r Θ x) x) := by
  let h := U.edgeBudget ρ V
  let t := setOf fun x:Pane V => pingS Θ (U.gateS r V) x
  let f := fun x:Pane V => Beacon U o (h x) x
  have hf : Continuous f := (Staff.collarAd_cont SU.group).comp (f:=fun x:Pane V => (travel x o (march o (U.scope V) 1),h x)) (Continuous.prodMk (Wilson.continuous_travel (G:=SU.group) _ o) (U.edge_budget_c _))
  rw [show (fun x:Pane V => Beacon U o (U.pearl ρ V r Θ x) x)=t.indicator f from ?_]
  · exact hf.measurable.indicator ping_o.measurableSet
  funext x; by_cases s:x∈t; · rw [Set.indicator_of_mem s,Staff.pearl,if_pos]; exact s -- maybe rfl goal
  rw [Set.indicator_of_notMem s,Staff.pearl,if_neg]; unfold Beacon; rw [map_zero]; exact s

lemma salaries (b:ℝ) (r e w : ℕ) (o : Seat Γ) (U:Wn) (u:U.Pays r w)
    (v:U.tenancy (side Y i s) r Staff.clearance e o) (t:(e:ℝ)≤b)(t':(w:ℝ)≤b)
    (p:α<1)(w':s≤Y.uv k)(h:|ρ| ≤ 2*bornQ P s) :
    let Q := X_ s
    let K := brandR Q
    let A := U.pearl ρ Γ r (temp Q)
    let F := U.cargoS Γ
    let V(x) := Beacon U o (A x) x
    (∀ x, ‖A x‖ ≤ K ∧ ‖V x‖ ≤ K) ∧
      Measurable V ∧
        (∀ x(g:Seat Γ→SU.E), V (Lattice.gauge g x) = SU.group.adjoint (g o) (V x)) ∧
        ∀ x, WellDrawn Y s i k α (BlockP e o) x →
          ‖F x ρ‖ ≤ K ∧ ‖A x-V x‖ ≤ triad Q b ∧ ‖V x-F x ρ‖ ≤ triad Q b := by
  intro Q K A F V; have H := Work.E04.temp_nonneg Q;
  have hZ:0≤b:=(Nat.cast_nonneg _).trans t
  have hU:= brand_hub s h; change |ρ| *temp Q ≤ K at hU
  have w0 : 0 ≤ |ρ| * temp Q:=mul_nonneg (abs_nonneg _) H
  refine ⟨fun x => ⟨(U.pearl_le u x H ρ).trans hU, (Gauge.norm_adjoint ..).le.trans ((U.pearl_le u x H ρ).trans hU) ⟩,
          measurable_beacon Γ U o ρ (temp Q) r, fun x g=>?_,fun x hz=>?_⟩
  · unfold V A; rw [U.dockGauge,Staff.Beacon.moves U]
  have hr : α * (RootBook Y i k s).p.threshold < temp Q := by
    have ht : (RootBook Y i k s).p.threshold=temp (X_ s):= (Papal.prices_plot Y s i k w').1 ▸ (Y.meter.boot s).1
    rw [←show _=temp Q from ht]; exact mul_lt_of_lt_one_left (RootBook Y i k s).p.threshold_pos p
  let X:= |ρ| * temp Q; let S:= skyline Q
  have Hv:= U.passage x o v hz.2 hr
  have hS : 0≤S := (chip_pos ..).le; have hc:=SU.group.colorScale_pos; let C:= 2* SU.group.colorScale
  have c:0≤C:=mul_nonneg zero_le_two hc.le
  obtain ⟨z,z₀⟩:= U.pearl_cost x u v ρ Hv hz.1 hS
  have zp: ‖A x-F x ρ‖ ≤ C*w*S*X := z
  have zq: ‖V x-A x‖ ≤ C*4*e*S*X := z₀
  have hY:zq=zq := rfl
  have he : C*w*S*X+C*4*e*S*X ≤ triad Q b := by
    unfold triad Staff.armRent
    change _≤ C*(b+4*b)*S*K
    have he : (w:ℝ)+4*e ≤ b+4*b := by gcongr
    calc _ = C*((w:ℝ)+4*e)*S*X := by ring
         _ ≤ _ := by gcongr
  rw [norm_sub_rev (A x)]
  exact ⟨(U.keeper_car u x Hv ρ).1.trans hU,(zq.trans ((le_add_of_nonneg_left (le_trans (norm_nonneg _) zp)).trans he)),
         (norm_sub_le_norm_sub_add_norm_sub _ (A x) _).trans ((add_le_add zq zp).trans ((add_comm ..).le.trans he))⟩

variable {m B R r w e : ℕ} {H:Real.exp 1≤P.x} {I : ℝ}
local notation "X" => hat P.R.L P.x s
abbrev lecture (I : ℝ) (m : ℕ) : ℝ := (12*I+1)*(m+1)+4
lemma lecture_pos (I m)(h:0<I): 0<lecture I m:=by unfold lecture; positivity
structure TempoDue (I A E:ℝ) (m a:ℕ) (s:ℕ) (P:Preparation) : Prop where
  fee : let x:=hat P.R.L P.x s; let Q:=sPow P s I; let T':=sPow P s A; let B:=(MixedCards.topFare*brandR x)^m;
    2*Q ≤ T' ∧ cardR Q ≤ T' ∧ a ≤ T' ∧ Staff.clearance ≤ radiusB x ∧
        B ≤ T' ∧ bankR E m (cardR Q)*((MixedCards.topFare*toneFare)^m*(1+m*toneFare)) ≤ T' ∧
        bankR E m (cardR Q) * B ≤ T' ∧
        bankR E m (cardR Q) * ((m:ℝ) * B * triad x Q) ≤ scratch x

lemma welcome (P:Preparation)(I:ℝ)(m : ℕ)(h : 0<I)(E : ℝ)(a : ℕ) : ∀ᶠ s in atTop, TempoDue I (lecture I m) E m a s P :=
  (tempo I m h E a P).mono (fun _ h => ⟨h⟩)

local notation "K₀" => (hallL U (side Y i s))
include H in
lemma multi_broom (pI:Investment P E v) (V:TempoDue I A E L.length (Fintype.card (materialL J)) s P) (o : Seat Γ)
    (p:∀ i,(U i).Pays r w)(t:∀ j,(U j).tenancy Γ r Staff.clearance e o)
    (v:(e:ℝ)≤ sPow P s I)(v':(w:ℝ)≤ sPow P s I)(Vi:s≤Y.uv k)(g:α<1)(hP:|ρ|≤2*bornQ P s) :
    Broom Y s i k K₀ A α ρ (2*e) (2*L.length) L.length
       (landQ Γ (concert U D L ρ r (temp (X_ s)) Γ) o e) (tint Y s i k U D L) := by
  let N := side Y i s
  let x := X_ s; let n:= L.length; let b := sPow P s I
  have hb : 0≤ b:= (BProof.coin_pos ..).le
  let T₁ := sPow P s A
  let f := terrain Y H -- H include
  let R := cardEst e; let C := BlockP e o; let Q(x':Pane N)(i:J):= (U i).pearl ρ N r (temp x) x'
  let F(x':Pane N)(i:J):= Beacon (U i) o (Q x' i) x'
  let G(x':Pane N)(i:J):=(U i).cargoS N x' ρ
  let W := tallyC Y s i k U D L
  let T' := standardTuition E n R; let K := brandR x; let hT:= tuition_nn E n R
  let A₁ := Mana*K; have hfK : 1 ≤ K := brand_near x; have he1:0 ≤ Mana*K := mul_nonneg MixedCards.fare_nn (zero_le_one.trans hfK)
  have heR: cardR (e:ℝ) ≤ cardR b := cards_mon (Nat.cast_nonneg _) v
  have hγ: 0 ≤ triad x b := triad_p x b hb
  have hr : C.card ≤ R := cardBound e o; have hz : (C.card:ℝ)≤cardR b := by
    suffices h₁ : (cardEst e:ℝ) = cardR (e:ℝ) from (Nat.cast_le.mpr hr).trans (h₁.trans_le heR)
    unfold cardEst cardR; push_cast; rfl
  have T'le : T' ≤ bankR E n (cardR b) := (purchase_eq e n E |>.symm).trans_le (bank_mon _ _ (by unfold cardR; positivity) heR)
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,t7⟩:= V.fee
  let ψ:= W ∘ F
  have hq(z:J): (U z).scope N∈C:= t z (Corona.halo_mono (show r ≤ r+Staff.clearance+8 from by omega) (Subset.refl _) (((p z).withinP (U z) N).2.1))
  have he(z:J):=salaries Y s i k b r e w o _ (p z) (t z) v v' g Vi hP
  have Hh(c:J → ColorL)(k:∀ i,‖c i‖≤K): ‖W c‖ ≤ sPow P s A:=
    (flavor_paid Y s i _ U D L pI C hq hr hfK k).trans ((mul_le_mul_of_nonneg_right T'le (pow_nonneg he1 _)).trans t6)
  have Hw(c c':J → ColorL)(l:∀ i,‖c i‖≤K)(u:∀ i,‖c' i‖≤K)(W₀:∀ i,‖c i-c' i‖≤triad x b) : ‖W c-W c'‖≤ scratch x:=
    (flavor_exchange Y s i _ U D L pI C hq hr hfK l u W₀ hγ).trans ((mul_le_mul_of_nonneg_right T'le (by positivity)).trans t7) -- fix b:=

  have σ(j x'): ‖F x' j‖≤K := ((he j).1 _).2
  have τ(j x'): ‖Q x' j‖≤K := ((he j).1 _).1
  refine ⟨broadVenue _ U D L ρ r (temp x) (tent Y H) _ (f (Y.ir i) s).symm o p t,
                   covariant_concert N U D L ρ r (temp x), ?_,fun j=>blocks_rest o e j,
                   (show ((↑(2*e):ℝ) ≤ _) from ?_),hz.trans t1,ψ,?_,?_⟩
  · intro y'; change Cadre (modesIn N C) _ T₁ (MixedCards.concert U D L ρ r (temp x) N y')
    rw [concert_eq]; exact (judged_color _ hfK U D L _ hq (fun i => τ i _)).buy le_rfl t4
  · push_cast; linarith only [v,t0]
  · change Batch Y s i k K₀ _ _ _ _ _ C ψ
    refine ⟨((ship_scene U N r e w o p t).raise (hallL U N) C (Subset.refl _) t3),
                      ?_,t2,g.le,hP,
               ⟨(sleek Y s i k U D L).continuous.measurable.comp (measurable_pi_lambda _ (fun i => (he i).2.1)), sPow P s A, fun i=> Hh _ (fun j=> σ j i)⟩,
                ?_,fun i=> Hh _ (fun j=> σ j i),?_⟩
    · have h := ready_color Y s i k U D L pI C hq hr
      have hf:0 ≤ toneFare:= zero_le_one.trans toneFare_pos; have ht:=MixedCards.fare_nn
      exact paint_more h ((mul_le_mul_of_nonneg_right T'le (show 0 ≤ (Mana*toneFare)^n*(1+n*toneFare) by positivity)).trans t5)
    · intro g z; unfold ψ Function.comp; rw [show F (Lattice.gauge g z) = fun i => SU.group.adjoint (g o) (F z i) from funext fun i => (he i).2.2.1 z g]; exact celebrity ..
    intro x' hh; rw [tint_material]; exact Hw (F x') (G x') (fun i=> σ i _) (fun i=> ((he i).2.2.2 x' hh).1) (fun i=> ((he i).2.2.2 x' hh).2.2)
  intro x' v
  change ‖noble Y s i k ((MixedCards.concert U D L ρ r (temp x)) N x')-ψ x'.1‖≤_
  rw [concert_eq]
  exact Hw (Q x'.1) (F x'.1) (fun i => τ i _) (fun i => σ i _) (fun i => ((he i).2.2.2 x'.1 v).2.1)


abbrev costMany (ρ:ℝ) := seatT Y s i k K₀ (tint Y s i k U D L) ρ

open Buffered.Afterglow.Tower
variable {ζι ζη π μ:ℕ→ℕ} {Φ0:ℕ→ Buffered.Family (tent Y H)→ℕ→ℂ}
    {E0:ℕ→ Buffered.Family (tent Y H)→ℂ}
    {D0:ℕ→ Buffered.Family (tent Y H)→ Buffered.Family (tent Y H)}
variable (Q : Universal Y H ζι ζη Φ0 E0) (K : Coherent (i:=ζι) (k:=ζη) (E:=E0) Y H D0 π μ)
local notation "iA" => ζι ∘ π
local notation "kA" => ζη ∘ μ
include Q K

theorem course {J : Type*} [Fintype J] (pI:Investment P E v)
    (W:Dispatchers P)(Z:Meritorious P) (p : 0 < I) (L : List J) :
    ∀ᶠ s:ℕ in atTop, ∀ᶠ x:ℕ in atTop,
      let i := iA x; let k := kA x; let V := side Y i s
      ∀ (U : J → EmberWind.Staff) (D : J → MixedCards.Ticket) {e r w : ℕ} {o : Seat V} {ρ : ℝ},
        (∀ i, (U i).Pays r w) →
        (∀ i, (U i).tenancy V r Staff.clearance e o) →
        (e:ℝ) ≤ sPow P s I → (w:ℝ) ≤ sPow P s I → |ρ| ≤2*bornQ P s →
          ‖Journey.compass Y i k s (MixedCards.concert U D L ρ r (temp (hat P.R.L P.x s)) V) - costMany Y s i k U D L ρ‖ ≤
            WakeInvestment.chip (hat P.R.L P.x s) (-3) := by
  filter_upwards [welcome P I L.length p E (Fintype.card (materialL J)), sails Y Q K pI W Z (2*L.length) L.length (lecture_pos I L.length p) (by norm_num: (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1)] with s h g
  filter_upwards [g,K.finance s] with x g v i k V U D e r w o ρ X' F z v' hu
  exact g.2.2 (2*e) (landQ V (MixedCards.concert U D L ρ r _ V) o e) ρ (hallL U V) (tint Y s i k U D L)
     (multi_broom Y s i k U D L (H:=H) pI h o X' F z v' v.enters (by norm_num) hu)
#print axioms course
end Yoke.Jewel.Program
end YM.CF.Py.Rate.LocalLimit.Preparation
