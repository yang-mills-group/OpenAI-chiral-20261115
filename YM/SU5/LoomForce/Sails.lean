import YM.SU5.LoomForce.CreditClock
/-!
# Buy the multi-Well apertures through the exact rents. Both pole and warmth.

No equality asserted between Wake color proxy Φ and the actual Seat,
except in the allowed range with SCRATCH error on **both** sides (gauge
component receipt vs. Φ and Θ-noble leading term vs Φ).
The sector choice afterward then uses exactly these poses and yields the
further estimates in this program. Include Staff direction even for a Tone
with its own mask footprint and body in those combined uses.
-/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Laurent Next.Free Cube Tulip Scroll Spire Pastry RP
     Branch Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Clock Hookah Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey
open Ballad EmberWind Pressure CF.Pannier.Chancel WakeInvestment Gleam.Wake
open Jewel
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
     ContDiff Classical
variable {I : Type*} [Fintype I]

abbrev scout (W : I → Staff) (n : Side) : Vessel SU.group (More n) (loomG I) :=
  ⟨fun i=> ((W i.1).localFace n,i.2)⟩

section budget
variable {P:Preparation} {j:ℕ} (Y : P.Course (VolumeCape.Dream.Nimbus j)) (s i k:ℕ)
  (W:I → Staff) {b e w:ℕ} {o:Seat (Journey.side Y i s)}
local notation "N" => Journey.side Y i s
local notation "S" => P.K.j
local notation "J" => (RootBook Y i k s).J.M
local notation "C5" => (Vale.hat P.R.L P.x s)
local notation "β" => Office
variable {A C T K ρ:ℝ} (tag:I→Sewer) (L:List I) (hc:0≤C)
variable (p:0<K) (hA:0<A) (paid:Office P T K A C L.length (booths tag L).length (Fintype.card (loomG I)) s)
  (a:(e:ℝ)≤ sPow P s K) (v:(w:ℝ) ≤ sPow P s K) (r:|ρ| ≤ 2*bornQ P s)
  (X:∀ i,(W i).Pays b w) -- capturing notation? W ok; β alias not dependent?
  (V:∀ t,(W t).tenancy (side Y i s) b Staff.clearance e o)
local notation "𝒞" => capBill
local notation "𝒬" => glow P A s
local notation "τ" => temp C5
local notation "hP" => BlockP e o

variable (Q:Chart (loomZ I)) (G:∀ i∈ booths tag L, ‖quoteSpin i Q‖ ≤ C)
local notation "𝒢" => lensPay Q tag L (glow P A s)

def armPrices (ρ : ℝ) (b:ℕ)(U:Pane N) (j:I): ColorL:= (W j).pearl ρ N b τ U
def blouse (ρ:ℝ)(b:ℕ)(o:Seat N)(U:Pane N)(j:I): ColorL:= (W j).Beacon o (armPrices Y s i W ρ b U j) U
abbrev beamVisit (Y : P.Course (VolumeCape.Dream.Nimbus j)) (s i:ℕ)(W:I → Staff)
    (Q : Chart (loomZ I))(tag:I→ Sewer)(L:List I)(A ρ:ℝ)(b:ℕ)(o:Seat (side Y i s)) (U:Pane (side Y i s)):ℂ :=
    lensPay Q tag L (glow P A s) (componentV (blouse Y s i W ρ b o U))

local notation "B_" X:max => blouse Y s i W ρ b o X
local notation "u0_" X:max => armPrices Y s i W ρ b X
local notation "Wφ" => beamVisit Y s i W Q tag L A ρ b o
include X
lemma mouth_venue (T:Pane N) : ‖componentV (blouse Y s i W ρ b o T)‖ ≤ |ρ| *τ:=by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg _) (Work.E04.temp_nonneg _))).mpr; intro h
  apply (PiLp.norm_apply_le (blouse Y s i W ρ b o T h.1) h.2).trans
  rw [blouse,Staff.Beacon,Gauge.norm_adjoint]
  exact (W h.1).pearl_le (X h.1) T (Work.E04.temp_nonneg _) _
include V a v
variable {α : ℝ} (t:α < 1)(h:s ≤ Y.uv k)
local notation "UL" => (scout W N).material ρ
local notation "S6" => sPow P s K
include t h
lemma dual_well (U:Pane N) (g: WellDrawn Y s i k α (BlockP e o) U) : let D:=|ρ| *τ
    let f:= armPrices Y s i W ρ b U
    let u:=componentV (B_ U)
    let K:= Staff.armRent (sPow P s K) (skyline C5) D (sPow P s K)
    ‖componentV f‖ ≤ D ∧ ‖UL U‖ ≤ D ∧
      ‖componentV f-u‖ ≤ K ∧ ‖u-UL U‖ ≤ K:=by
  intro D F u C'; let A5:= RootBook Y i k s; let C':= C'; let ℓ:= skyline C5
  have h':A5.p.threshold=τ:= (Papal.prices_plot Y s i k h).1 ▸ (Y.meter.boot s).1
  have ht: 0 ≤ D:= mul_nonneg (abs_nonneg _) (Work.E04.temp_nonneg _); let G0:=sPow P s K
  have hG:0≤ G0:=BProof.coin_pos ..|>.le; have hL:0 ≤ℓ:=(WakeInvestment.chip_pos ..).le; have hp:= SU.group.colorScale_pos
  have hc:0≤ C':=by change 0 ≤ 2*_*(G0+4*G0)*ℓ*D; positivity
  have hw(j:I): let E:=(W j).cargoS N U ρ; let Z:= (B_ U) j
        ‖F j‖ ≤ D ∧ ‖E‖ ≤ D ∧ ‖F j-Z‖ ≤ C' ∧ ‖Z-E‖ ≤ C' := by
    intro E Z
    have ht':= (W j).passage U o (V j) g.2 ((mul_lt_of_lt_one_left A5.p.threshold_pos t).trans_eq h')
    obtain ⟨e0,u0⟩:= (W j).keeper_car (X j) U ht' ρ
    obtain ⟨y,z⟩:= (W j).pearl_cost U (X j) (V j) ρ ht' g.1 hL
    have he: Staff.armRent e ℓ D w ≤ C':=by change _ ≤ Staff.armRent G0 ℓ D G0; unfold Staff.armRent; gcongr
    have hz: ‖Z-F j‖ ≤ 2*SU.group.colorScale*4*e*ℓ*D := z
    have hy: ‖F j-E‖ ≤ 2*SU.group.colorScale*w*ℓ*D := y
    have hφ: 2*SU.group.colorScale*w*ℓ*D + 2*SU.group.colorScale*4*e*ℓ*D ≤ C' := le_trans (le_of_eq ?_) he
    · exact ⟨u0.le.trans e0,e0,(norm_sub_rev ..).le.trans (hz.trans ((le_add_of_nonneg_left (by positivity)).trans hφ)), (norm_sub_le_norm_sub_add_norm_sub Z (F j) E).trans ((add_le_add hz hy).trans ((add_comm ..).le.trans hφ))⟩
    unfold Staff.armRent; ring
  let E(x:I):= (W x).cargoS N U ρ
  refine ⟨(pi_norm_le_iff_of_nonneg ht).mpr (fun i =>
    (PiLp.norm_apply_le (F i.1) i.2).trans (hw i.1).1), (pi_norm_le_iff_of_nonneg ht).mpr
      (fun i=> (PiLp.norm_apply_le (E i.1) i.2).trans (hw i.1).2.1),
    (pi_norm_le_iff_of_nonneg hc).mpr (fun i=> (PiLp.norm_apply_le (F i.1 - (B_ U) i.1) i.2).trans (hw i.1).2.2.1),
    (pi_norm_le_iff_of_nonneg hc).mpr (fun i=> (PiLp.norm_apply_le ((B_ U) i.1 - E i.1) i.2).trans (hw i.1).2.2.2)⟩

omit t h X V a v
-- no circular reference to integrability of the mark price: the lens functions
-- themselves are globally bounded, masks and holonomies use true measurable panes
open Scree
private lemma pearlMeas (B:Staff)(ρ t:ℝ)(n:Side)(o:Seat n)(b:ℕ) : Measurable
    (fun x:Pane n=> B.Beacon o (B.pearl ρ n b t x) x) := by
  let X (x : Pane n) := travel x o (Cube.march o (B.scope n) 1); have h:Measurable (B.pearl ρ n b t) := Measurable.ite (p:=pingS t (B.gateS b n)) (ping_o (X:=B.gateS b n) («e»:=t) (G:=SU.group)).measurableSet (B.edge_budget_c ρ).measurable measurable_const
  exact (Staff.collarAd_cont SU.group).measurable.comp (f:=fun x : Pane n=> (X x,B.pearl ρ n b t x)) ((show Continuous X from Wilson.continuous_travel ..).measurable.prodMk h)
omit [Fintype I] in
lemma blouse_meas (o:Seat N) (b : ℕ) (ρ:ℝ)(j:I) : Measurable (fun U:Pane N=> blouse Y s i W ρ b o U j):= pearlMeas (W j) ρ τ N o b

variable (up:evenPose Y s i)(eq: Q= pairPrice (zoomR P A s) (fun i=> (W i).u) (fun i=> (W i).spin) (Journey.side Y i s) P.K.j (RootBook Y i k s).J.M)
omit [Fintype I] in
lemma lens_base (U : I → ColorL) : 𝒬 • (componentV U) = componentV fun i=> 𝒬 • U i := rfl
include up eq
omit [Fintype I] in
lemma paying {o:Seat N} : GaugeInvariant (beamVisit Y s i W Q tag L A ρ b o):=by
  let n:=N; intro g x; unfold beamVisit lensPay; rw [lens_base,lens_base]
  let H := g o; let f := blouse Y s i W ρ b o
  have he: (fun i=> 𝒬 • f (Lattice.gauge g x) i)=(fun i=> SU.group.adjoint H (𝒬 • f x i)) := by
    funext j; unfold f blouse armPrices; rw [Staff.dockGauge,Staff.Beacon.moves,map_smul]
  exact (congrArg (fun a=>fullPay (componentV a) Q tag L) he).trans (orient_quote Y s i k up
    (fun i=> (W i).u) (fun i=> (W i).spin) _ tag _ L (g o) Q eq)

omit up eq
include X hc paid r G
local notation "ω" => tollMeter C 𝒬 L.length (booths tag L).length
lemma house_bounds (x:Pane N) : ‖Wφ x‖ ≤ sPow P s T := by
  have h := (meters (I:=I) C 𝒬 (sq_nonneg _) Q hc tag L G).worth
  let D := |ρ| * temp C5
  have ht:0 ≤ D:=mul_nonneg (abs_nonneg _) (Work.E04.temp_nonneg _)
  exact (h (1+D) (by linarith) (componentV (B_ x)) ((mouth_venue (ρ:=ρ) Y s i W X x).trans (by linarith))).trans
    (paid.metered ρ r).2.2.1

lemma ember_visit {o:Seat N} : Envelope (beamVisit Y s i W Q tag L A ρ b o):=by
  let u:= beamVisit Y s i W Q tag L A ρ b o
  let Aξ (x:Pane N):=componentV (blouse Y s i W ρ b o x)
  have he :Measurable Aξ:= measurable_pi_lambda _ (fun i'=> (PiLp.continuous_apply 2 (fun (_:kol)=>ℝ) i'.2).measurable.comp (blouse_meas Y s i W _ _ _ i'.1))
  exact ⟨(meters C 𝒬 (sq_nonneg _) Q hc tag L G).bright.continuous.measurable.comp he,
    sPow P s _,fun x=>house_bounds (o:=o) Y s i W tag L hc paid r X Q G x⟩
include V a v t h
lemma will_cover (x:Pane N) (g: WellDrawn Y s i k α (BlockP e o) x) :
    ‖𝒢 (componentV (u0_ x))-Wφ x‖ ≤ scratch C5 ∧ ‖Wφ x-𝒢 (UL x)‖ ≤ scratch C5 := by
  let z:= |ρ| *τ; let f:=1+z; let I':=tollMeter C 𝒬 L.length (booths tag L).length
  have hp := meters (I:=I) C 𝒬 (sq_nonneg _) Q hc tag L G
  obtain ⟨v,xp,dF,dV⟩:= dual_well Y s i k W a v X V t h x g
  have hu: 0 ≤ z:= mul_nonneg (abs_nonneg _) (Work.E04.temp_nonneg _)
  have hm : 1 ≤ f := le_add_of_nonneg_right hu
  have hc':0≤I':=hp.nonneg; have hc:0 ≤ I' * f^L.length:=by positivity
  let m:= paid.metered ρ r; have he:z≤f:=le_add_of_nonneg_left zero_le_one
  let B:= componentV (B_ x); have he': ‖B‖≤ f:= (mouth_venue Y s i W X x).trans he
  exact ⟨(hp.price f hm _ B (v.trans he) he').trans ((mul_le_mul_of_nonneg_left dF hc).trans m.2.2.2), (hp.price f hm B (UL x) he' (xp.trans he)).trans ((mul_le_mul_of_nonneg_left dV hc).trans m.2.2.2)⟩

-- full investment
local notation "R₀" => zoomR P A s
abbrev actual_rents (tag:I→Sewer) (L:List I) (T:ℝ)(W:I→Staff)(b e:ℕ)(ρ:ℝ)(o:Seat (side Y i s)) :=
    landQ N (ream tag L (zoomR P T s) (glow P T s) W b ρ τ N) o e
variable {H:Real.exp 1≤ P.x}
include H up eq
lemma Broom_tactic : Broom Y s i k (scout W N) T α ρ (2*e) (2*L.length) L.length
    (actual_rents Y s i tag L A W b e ρ o) 𝒢 := by
  let he(x:Pane N)(g: WellDrawn Y s i k α hP x):= will_cover Y s i k W tag L hc paid a v r X V Q G t h x g
  let μ:= paid.circus
  have hVT := paid.metered ρ r
  let u:= meters C 𝒬 (sq_nonneg _) Q hc tag L G
  refine ⟨full_span _ _ _ tag W X _ L V (tent Y H) (momentm Y i s) (terrain Y H _ s).symm,
    speak_many R₀ ρ τ 𝒬 tag L W N,
    fun x=>(full_assert R₀ ρ τ (Work.E04.temp_nonneg _) (sq_nonneg _) tag W X L V x).buy le_rfl hVT.1,
    fun i=> blocks_rest o e i, (μ.width₀ e a).trans paid.cells,
    ?_, Wφ, ?_, fun x h'=>?_⟩
  · refine le_trans (a:=↑(BlockP e o).card) ?_ ((μ.size e a).trans paid.cells)
    exact Nat.cast_le.mpr (by simpa only [BlockP,card_singleton,one_mul] using Corona.halo_size {o} e)
  · have hm (i:loomG I) (b: Signed) (v: Seat N):=(W i.1).withinShip (scout W N) i rfl (X i.1) (V i.1) b v
    have hL:(scout W N).Ship hP Staff.clearance := ⟨fun i=>(hm i 1 o).1, fun i t b=>(hm i t b).2.2, fun i t=>(hm i t o).2.1⟩
    exact ⟨hL.raise _ _ (Subset.refl _) μ.clearance, meterInc u le_rfl hVT.2.1, paid.seats, t.le, r,
       ember_visit Y s i W tag L hc paid r X Q G,paying Y s i k W tag L Q up eq,
       fun x=> house_bounds Y s i W tag L hc paid r X Q G x, fun x g=> (he x g).2⟩
  rw [show noble _ _ _ _ _= _ from bought_noble Y s i k R₀ 𝒬 W b ρ τ tag L x up Q eq]
  have hp: 𝒢 (componentV (u0_ x.1))=_ := (show _ = fullPay (componentV (fun i=> 𝒬 • (W i).pearl ρ N b τ x.1)) Q tag L from rfl)
  rw [← hp]; exact (he _ h').1

#print axioms Broom_tactic
end budget
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
