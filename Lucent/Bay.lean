import Lucent.Nacreous
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

open Pannier.Chancel Rous Pressure
open scoped Classical
variable {I:Type} [Fintype I] (W:I→Staff)

open Gleam.Wake
abbrev VesselR(n:Side):Vessel SU.group (More n) (Tint I) := ⟨fun t=>((W t.1).localFace n,t.2)⟩
abbrev hull (N:Side) (o:Seat N) (r:ℕ)(ρ t:ℝ)(U:Pane N)(p:I):SU.group.Color:= (W p).Beacon o ((W p).pearl ρ N r t U) U
abbrev cargo (N:Side)(ρ:ℝ)(U:Pane N)(p:I):SU.group.Color:= (W p).cargoS N U ρ
lemma hail (N:Side) (ρ:ℝ)(U:Pane N): (VesselR W N).material ρ U= hues (cargo W N ρ U):=rfl -- coeff ρ
variable {r w e:ℕ}
lemma rail_ship {N:Side}{o:Seat N}(p: rail W r w N o e): (VesselR W N).Ship (BlockP e o) Staff.clearance:= by
 let T:=VesselR W N; have h(j:Tint I):=(W j.1).withinShip T j rfl (p j.1).1 (p j.1).2; exact ⟨fun j=>(h j 1 o).1,fun j t b=>(h j t b).2.2,fun j t=>(h j t o).2.1⟩

variable (S:Stencil I)

-- Portside Lantern. Compare χ_t to it, it to material.
def light (o:Seat ℕ') (r:ℕ)(ρ t:ℝ) (U:Pane ℕ') : ℂ := icing Y s i k W S (hues (hull W ℕ' o r ρ t U))

variable (o:Seat (side Y i s)) (r:ℕ)(ρ t:ℝ)
lemma shining (p:Singing W S):GaugeInvariant (light Y s i k W S o r ρ t):=by
 intro g U
 have hv:hull W ℕ' o r ρ t (Lattice.gauge g U)= crown ℕ' W (fun _=>g o) (hull W ℕ' o r ρ t U):=by
   funext j; unfold hull; rw [(W j).dockGauge,Staff.Beacon.moves]; rfl
 have hp:=iced Y s i k W S (hull W ℕ' o r ρ t (Lattice.gauge g U)); have hu:=iced Y s i k W S (hull W ℕ' o r ρ t U); unfold light;
 rw [← hp,←hu,hv,p,constant_noble (g:=g o)]
variable {t r}

private lemma beacon_meas {n:Side}(o:Seat n)(r:ℕ)(L:Staff)(t:ℝ):
    Measurable (fun U:Pane n=> L.Beacon o (L.pearl ρ n r t U) U):=by
 let D:=fun U=>L.pearl ρ n r t U
 have hx: Measurable D:=by
    unfold D Staff.pearl
    exact Measurable.ite (ping_o (G:=SU.group) (X:=L.gateS r n) (e:=t)).measurableSet (L.edge_budget_c ρ).measurable measurable_const
 let V:=march o (L.scope n) 1; exact (Staff.collarAd_cont SU.group).measurable.comp (f:=fun x:Pane n=>(travel x o V,D x)) (((continuous_travel (G:=SU.group) V o).measurable).prodMk hx)

variable {M v B:ℝ} {m d:ℕ}
variable (p:Investment P M v)(q:S.degree m d)(line:rail W r w (side Y i s) o e)(f:0≤t)(l:|ρ| *t ≤ B)

lemma cover_hues (C:I→SU.group.Color)(b:∀ j,‖C j‖≤ B):Covers (hues C) B:=fun j=> (PiLp.norm_apply_le ..).trans (b j.1)
include line l f
lemma plot_caps (U:Pane ℕ') :
 Covers (hues (volley ℕ' W r ρ t U)) B ∧ Covers (hues (hull W ℕ' o r ρ t U)) B:=by
 have hp(j:I): ‖(W j).pearl ρ ℕ' r t U‖≤B:= ((W j).pearl_le (line j).1 U f ρ).trans l
 exact ⟨cover_hues _ hp,cover_hues _ (fun j=> (Gauge.norm_adjoint ..).le.trans (hp j))⟩
include p q
lemma lighted_range (U:Pane ℕ') :
 ‖light Y s i k W S o r ρ t U‖≤ candied S M m d*B^m:=iced_cost Y s i k W S p q ((mul_nonneg (abs_nonneg _) f).trans l) _ (plot_caps Y s i W o ρ line f l U).2

lemma light_env : RG.Envelope (light Y s i k W S o r ρ t):=by
 refine ⟨(iced_cont Y s i k W S).continuous.measurable.comp (measurable_pi_lambda (f:=fun U=> hues (hull W ℕ' o r ρ t U)) ?_),_,lighted_range Y s i k W S o ρ p q line f l⟩
 intro j
 exact (PiLp.continuous_apply 2 _ j.2).measurable.comp (beacon_meas ρ o r (W j.1) t)


lemma lighted_difference (x:Fields ℕ') (a:ℝ)(b:0≤a)(u:1≤B)
   (h:Tiny (BlockP e o) x.1 a)
   (g:∀ j,pingS t ((W j).gateS r ℕ') x.1): let K:=Staff.armRent e a (|ρ| *t) w; let R:=candied S M m d * B^m*K
  ‖noble Y s i k (kite r ρ t W S ℕ' x)- light Y s i k W S o r ρ t x.1‖≤ R ∧ ‖light Y s i k W S o r ρ t x.1-icing Y s i k W S ((VesselR W ℕ').material ρ x.1)‖ ≤ R:=by
 intro K R
 let V:=volley ℕ' W r ρ t x.1; let H:=hull W ℕ' o r ρ t x.1; let C:=cargo W ℕ' ρ x.1
 have hx(j:I): ‖C j‖ ≤ B ∧ ‖V j-H j‖≤K ∧ ‖H j-C j‖ ≤ K:= by
    obtain ⟨v1,v2⟩:=(W j).pearl_cost x.1 (line j).1 (line j).2 ρ (g j) h b
    refine ⟨((W j).keeper_car (line j).1 _ (g j) ρ).1.trans l, ?_, (norm_sub_le_norm_sub_add_norm_sub (H j) (V j) (C j)).trans ((add_le_add v2 v1).trans_eq ?_)⟩

    · rw [norm_sub_rev]; apply v2.trans; unfold K Staff.armRent; have ht:=SU.group.colorScale_pos
      have z:0 ≤ 2*SU.group.colorScale*w*a*(|ρ| *t):=by positivity
      nlinarith only [z]
    unfold K Staff.armRent; ring
 obtain ⟨v₁,v₂⟩:=plot_caps Y s i W o ρ line f l x.1
 have ht:=SU.group.colorScale_pos
 have hK:0≤K:=by unfold K Staff.armRent; positivity
 have hb(L J:I→SU.group.Color)(y:∀ j,‖L j-J j‖≤K): Adjoins (hues L) (hues J) K:= fun j=> (PiLp.norm_apply_le (L j.1 - J j.1) j.2).trans (y j.1)
 rw [kite,iced,hail];
 exact ⟨iced_sub Y s i k W S p q u v₁ v₂ (hb _ _ fun j=> (hx j).2.1) hK, iced_sub Y s i k W S p q u v₂ (cover_hues _ fun j=>(hx j).1) (hb _ _ fun j=>(hx j).2.2) hK⟩
#print axioms lighted_difference
