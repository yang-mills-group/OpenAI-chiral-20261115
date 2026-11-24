import YM.CF.BPress.Mosaic.Skein
import YM.CF.BPress.Mosaic.Token
import YM.CF.BPress.Primary.Dust
/-! spin $weak$ exponent using micro read including all through exact flags.. breaks even via Primary. Add weak total. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Mosaic.Pulse
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger
variable {N m s:Side}{B:BandWidth}{A:Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k:ℕ} {c q d t v ε e d' C D ζ δ τ u b:ℝ}
local notation "Ξ"=> Visit A R H
variable (V: Recipe (A:=A) T) (F:Rented R H X Y.d e k c)(Q:Stamp A R X Y)
variable {p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
variable (P:Edition Y)
-- thin family converted by Locale. choosing long-foot even for short OK. short read property at 7 budget.$
section parts
variable (ε)
abbrev state (x:Visit A R H):= party A R H x
abbrev chordY (ε:ℝ) (x:Visit A R H) (S:Support η):= δRest A X.W.M id (fun i=>P.logG i (ΓStage F Q (state x)) (grim R H X ε (state x).val)) S
def comG (x: Visit A R H):=∑ i:Support η,chordY F Q P ε x i -- order tune
def gaugeY (x:Visit A R H) :ℂ:= (Wage H V (state x).val:ℝ)-(↑ (∑ i,cold H V (state x).val i):ℂ) -- tune result subtraction
end parts
def costΖ(R:Hangar (More N))(D:BandWidth)(X:Sugar.Stage N)(b t v:ℝ):= MicCost R X D t*b + MicCost R X D t *v
variable {P V} (φ:RightsC X R H b) (K:Budgeting H V τ u D ζ δ C)(J: Mangrove R H V.M)(L:Passports Y T G h P p3 q d ε t v)(hT: Seer H R X k)(g:Fast H.y)(hε:0≤ε)
local notation "μγ"=> hT.charter.port
variable {F Q}
include φ L hT g hε
lemma hopeful (bT:b ≤t): Lift (MicCost R X B b *v) (comG ε F Q P):=by
 let U(i):= if currencyT A X.W.M (id i) then P.fee i else 0; let f(i:Support η)(x:Visit A R H):=chordY F Q P ε x i
 have hp(i):0≤U i:= ite_nonneg (L.grow.pos i) le_rfl; refine mirror φ ((L.grow.chill bT).subs (c:=U) hp (fun i=>by unfold U; split; rfl; exact L.grow.pos i)) (fun i g=> ?_) (?_ ) (fun i=>?_)
 · unfold U at g; split at g; next a=>
      let V:= L.fee_land i g; have hu:= Abyss.foot A X.W.M (L.fee_land i g) a -- tune
      refine ⟨hu,?_⟩; apply FeeT.general φ μγ V hu; intro s H' x y p; change f i x=f i y; unfold f chordY δRest; rw [if_pos a, if_pos a]; exact L.frost i _ _ _ _ (hasP hT H' p F Q) (Cam hT H' p F Q ε T.p.B)
   · contradiction
 · intro i x; change ‖f i x‖≤U i; unfold f U chordY δRest; split; exact L.turn _ _ _ (grim_p F Q hε (state x)); simp
 change Measurable (f i); unfold f chordY δRest; split; exact (L.cloud i _ _ (grim_m R X H Subtype.val measurable_subtype_coe) (Γ_m F Q)).comp (party_meas g); exact measurable_const -- tune grim_m needed explicit
include J K
omit L hε in
lemma gaugeK (tH:b ≤τ)(qH:b≤ΩJ H) : Lift (((payL R H V C + payJ R H b)+payE R H V ζ D) + MicCost R X B b*u) (gaugeY (H:=H) (R:=R) V):=by -- S size numerals PL
 apply ((((shelf K J g).plus (coastal K J φ g qH)).plus (traveler K J g)).plus (back_g K J φ g μγ tH)).sw; intro x; unfold gaugeY Wage Recipe.wage; push_cast; rw [sum_neg_distrib,sum_neg_distrib]; abel -- tune
end YM.CF.BPress.Mosaic.Pulse
#print axioms YM.CF.BPress.Mosaic.Pulse.hopeful
