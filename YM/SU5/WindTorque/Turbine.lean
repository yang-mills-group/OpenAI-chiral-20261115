import YM.SU5.WakeInvestment.Broom
import YM.SU5.WindTorque.Prelude
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
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
variable {z A c:ℝ}
local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Gleam Tempest
open scoped Topology ContDiff
local notation "θ" s:max => (Papal.xhood (P:=P) s)
local notation "N" s:max i:max => (side Y i s)
open MeasureTheory

open WakeInvestment Gleam.Wake
open Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
variable (s i k : ℕ)
local notation "X" s:max => hat P.R.L P.x s
local notation "χ" s:max c:max => WakeInvestment.chip (hat P.R.L P.x s) c
local notation "Θ" T:max=> tollR T
local notation "Υ" T:max=> tabμ T
local notation "wax" s:max=> (Υ (θ s))
local notation "ℓop" s:max i:max k:max t:max=> (WakeInvestment.weighted (spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))) t (flatShear Y s i k))

open Regis.Wake (Paint drip mute_mix muting mute_shrink mute_ceiling mute_same mute_smooth lipClay assay)
open ProbabilityTheory
/-! # Two local prerequisites of PB.4 at actual first Pane Mark expense -/
open Window
open Ballad Hiro
-- abbreviation in own namespace (e.g. Tiny, Size ambiguous)
namespace Jewel
local notation "Wind" => EmberWind.Staff
variable (W V:EmberWind.Staff)
open EmberWind
open Rous
local notation "■" s:max i:max k:max => RootBook Y i k s
local notation "♟" s:max i:max k:max => (RootBook Y i k s).p.threshold
variable {ρ : ℝ} {b r w e:ℕ}{H:Real.exp 1 ≤ P.x}
variable {o:Seat (side Y i s)}

abbrev landQ (n:Side)(G:Mark n)(o:Skye.Seat n)(b:ℕ): Hookah n:=⟨G, BlockP b o,o⟩
abbrev turret {j:Side} (q:ℝ)(r:ℕ)(t:ℝ)(o:Seat j) (e:ℕ):= landQ j (W.rungWeave q r t j) o e
abbrev double_bill {j:Side} (q:ℝ)(r:ℕ)(t:ℝ)(o:Seat j)(e:ℕ) := landQ j (W.rungWeave q r t j*V.rungWeave q r t j) o e

def spinCoupon (s i k:ℕ) (W V:Wind):ℂ:= Hiro.diced 1 W.u V.u W.spin V.spin (side Y i s) P.K.j (RootBook Y i k s).J.M
lemma noble_empty (A:EmberWind.Staff)(r:ℕ)(b t:ℝ)(q:evenPose Y s i)(U:Fields (N s i)): noble Y s i k (A.rungWeave t r b (N s i) U)=0:=by rw [noble_linear,A.onMark]; exact Hiro.heldVoid 1 _ _ q.1 (nontrivial_spin P) (preparedFlat Y s i k) _
lemma noble_civic (r:ℕ)(b t:ℝ)(q:evenPose Y s i)(U:Fields (N s i)): noble Y s i k (W.rungWeave t r b (N s i) U*V.rungWeave t r b (N s i) U) = spinCoupon Y s i k W V* (inner ℝ (W.pearl t _ r b U.1) (V.pearl t _ r b U.1):ℝ):=by
 rw [noble_linear,W.onMark,V.onMark]; exact Hiro.cherry 1 W.u V.u W.spin V.spin q.1 (nontrivial_spin P) (preparedFlat Y s i k) _ _
lemma deckVenue (W:EmberWind.Staff) (ρ:ℝ)(p:W.Pays r w)(t:ℝ)(q:Calibration)(m:Side)(y:n=q.c m) {o:Seat n} (l:Staff.tenancy W n r EmberWind.Staff.clearance e o) : AtSupport false (BlockP e o) (W.rungWeave ρ r t n):=by
 subst n; have ht:= (W.letterBudget ρ q t p).support m; apply ht.mono
 rw [← (p.withinP W (q.c m)).1]; exact (Corona.halo_mono (show r+8 ≤ r+Staff.clearance+8 from by omega) (Subset.refl _)).trans l

private lemma rollZero (A:ℝ)(p:0 ≤ A) : Paint (fun _:Staff.Tile→ℝ=> (0:ℂ)) 2 A:= ⟨contDiff_const,fun K H A v=>by simp; positivity,fun K H x y t l=>by simp; positivity⟩
local notation "CAP" n:max => (2*n:ℕ)
local notation "Ω" s:max=> sPow P s A

-- tile House. enough for all b/w from p^J; only late s uses. Note need `cap_ρ ≤ 2 √(X)` even for s reps with K powers chosen.
-- keep compiler uses geometry condition tenancy, not assuming it for any specific pairing before issuing.
def grass (I:ℝ):ℝ:= 16*(I+1)
structure CircusPrice (P:Preparation)(C I:ℝ)(s:ℕ) : Prop where
 size(e:ℕ)(p:(e:ℝ) ≤ sPow P s I): ↑((e+e+1)^4:ℕ) ≤ sPow P s (grass I)
 width₀(e:ℕ)(p:(e:ℝ) ≤ sPow P s I):((2*e:ℕ):ℝ) ≤ sPow P s (grass I)
 hold: 2*C*Staff.rackColor ≤ sPow P s (grass I)
 clearance: EmberWind.Staff.clearance ≤ radiusB (hat P.R.L P.x s)
 room: (Fintype.card Staff.Tile:ℝ) ≤ sPow P s (grass I)
 tally : ∀ ρ:ℝ, |ρ| ≤ 2*bornQ P s→ let t:=temp (hat P.R.L P.x s); let K:=|ρ| *t; C*K^2 ≤ sPow P s (grass I) ∧ Staff.regiment*K ≤ sPow P s (grass I) ∧ (Staff.regiment*K)^2 ≤ sPow P s (grass I) ∧ ∀ (e w:ℕ),(e:ℝ) ≤ sPow P s I→ (w:ℝ) ≤ sPow P s I→ C*(2*Staff.armRent e (skyline (hat P.R.L P.x s)) K w*K) ≤ scratch (hat P.R.L P.x s)
set_option linter.unusedVariables false in
private lemma wheel (q:ℝ)(c:0 ≤ q)(f:ℝ)(p:0 ≤ f) (z e w:ℝ)(g:0 ≤ e)(v:0 ≤ w) {x y a:ℝ}(hx:x ≤ e)(b: 0 ≤ x)(a0:0 ≤ a)(hy:y ≤ w)(h:0 ≤ y)(ha:a ≤ z) : q*(2*Staff.armRent x f a y * a) ≤ q*(2*Staff.armRent e f z w * z):=by unfold Staff.armRent; have hh:= SU.group.colorScale_pos; have hQ : 0 ≤ z:=a0.trans ha; gcongr
lemma CircusPrice.ready (P:Preparation)(C I:ℝ)(l:0 ≤ C)(p:0<I) : ∀ᶠ s in atTop,CircusPrice P C I s:=by
 let A:= grass I; let Y(x:ℝ) := BProof.coin x 0 I 0; have hp:Pays 0 I 0 Y:=whole ..; let k:=fun x=>2*Real.sqrt x*temp x; have hm:4*I < A:=by unfold A grass; linarith only [p]
 have hv:2 < A:=by unfold A grass; linarith -- indentation
 have hZ:Pays 0 1 0 k:=by
    refine Pays.fix (Pays.scale 2 (whole 0 1 0)) ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x p; unfold k; rw [Head.Garland.era x p,←BProof.thresh_eq p,BProof.thresh,mul_assoc,BProof.coin_mul]; norm_num
 let f':= Pays.scale (2*SU.group.colorScale) (plus hp (Pays.scale 4 hp));
 have he := leap (w:= -7/400000) (p:=0) (q:=0) (Pays.scale C (times (Pays.scale 2 (times (times f' (whole (-120000/400000) 0 0)) hZ)) hZ)) (Or.inl (by norm_num))
 let m:=Staff.regiment; have hx:=Pays.scale m hZ
 have h:= pot (plus (plus hp hp) (Worth.Pays.merit (constant 1) (Or.inr (Or.inl ⟨rfl,p⟩)))) 4;
 filter_upwards [(turnover P).eventually (leap (w:=0) (p:=A) (q:=0) h (Or.inr (Or.inl ⟨by norm_num,by push_cast; linarith only [hm]⟩))),(turnover P).eventually (leap (w:=0) (p:=A) (q:=0) (Pays.scale 2 hp) (Or.inr (Or.inl ⟨rfl,by linarith⟩))),grow_e A (2*C*Staff.rackColor) (by linarith) P, (turnover P).eventually (Work.E08.eventual_radiusB Staff.clearance),grow_e A (Fintype.card Staff.Tile) (by linarith) P, (turnover P).eventually (leap (w:=0) (p:=A) (q:=0) (Pays.scale C (pot hZ 2)) (Or.inr (Or.inl ⟨by norm_num,by simpa using hv⟩))), (turnover P).eventually (leap (w:=0) (p:=A) (q:=0) hx (Or.inr (Or.inl ⟨rfl,by linarith⟩))), (turnover P).eventually (leap (w:=0) (p:=A) (q:=0) (pot hx 2) (by simp [Worth.Earlier]; exact hv)), (turnover P).eventually_gt_atTop 1,(turnover P).eventually he] with s h v t l' t' κ κ' κ₀ w x
 let X':=hat P.R.L P.x s; let U:=Y X'; have h': 0 ≤ U:= (BProof.coin_pos ..).le; refine ⟨fun e p=>?_,fun e p=>?_,t,l',t',fun ρ t=>?_⟩
 · refine le_trans ?_ h; change ((↑((_+_+1)^4:ℕ)):ℝ) ≤ (U+U+1)^ (4:ℕ); push_cast; gcongr
 · refine le_trans ?_ v; push_cast; gcongr
 intro S K; let Z:= k X'; have hx:0 ≤ S:= Work.E04.temp_nonneg _; have hK:0 ≤ K:=mul_nonneg (abs_nonneg _) hx; have hp:K ≤ Z:=mul_le_mul_of_nonneg_right t hx
 have hf:Staff.regiment*K ≤ m*Z:=mul_le_mul_of_nonneg_left hp Staff.regge
 refine ⟨le_trans ?_ κ,hf.trans κ',le_trans ?_ κ₀,fun e W l' V=>?_⟩
 · change C* K^2 ≤ C*Z^2; gcongr
 · change (Staff.regiment*K)^2 ≤ (m*Z)^2; exact pow_le_pow_left₀ (mul_nonneg Staff.regge hK) hf 2
 exact le_trans (wheel C l _ (chip_pos ..).le Z U U h' h' l' (Nat.cast_nonneg _) hK V (Nat.cast_nonneg _) hp) x

variable {α I C:ℝ}(t:CircusPrice P C I s)(hu:0 ≤ C)
local notation "σV" s:max=> sPow P s I
local notation "η1" s:max i:max k:max => (RootBook Y i k s).J.M
variable (tW: W.tenancy (side Y i s) r Staff.clearance e o)(pW: W.Pays r w)(tV:V.tenancy (side Y i s) r Staff.clearance e o) (pV:V.Pays r w)
variable (h: evenPose Y s i) (ρ:ℝ)(hρ:|ρ| ≤ 2*bornQ P s)(paid:s ≤ Y.uv k)(g:α<1)
-- spend View. blur hP bound *uniform* costs geometric checks at torus (phases). E'=2e margin available. A exponent test $I$, Amp growth test $grass I$, do not reverse on payment.
private lemma orbit_members(e:ℕ)(o:Seat n): (↑(BlockP e o).card:ℝ) ≤ ↑((e+e+1)^4:ℕ):= Nat.cast_le.mpr (by simpa only [BlockP,card_singleton,one_mul] using Corona.halo_size {o} e)
include t hu h paid g hρ pW tW H
lemma peacock (τe:(e:ℝ) ≤ sPow P s I) :
      Broom Y s i k (Staff.twin W W (side Y i s)) (grass I) α ρ (2*e) 2 2 (turret W ρ r (temp (X s)) o e) (fun _=> (0:ℂ)) := by
 let n':= side Y i s; let T:=tent Y H; let h':= Staff.twin W W n'; let V:=BlockP e o; let ψ:= fun _ : Pane n' => (0:ℂ); let τ:= temp (hat P.R.L P.x s)
 let A:= ■ s i k; have he:A.p.threshold=τ:= (Papal.prices_plot Y s i k paid).1 ▸ (Y.meter.boot s).1; have hx:0 ≤ τ:= Work.E04.temp_nonneg _
 refine ⟨deckVenue W ρ pW τ T _ (terrain Y H (Y.ir i) s).symm tW, W.oneVox _ _ _ _,fun x=>(W.sizing pW ρ x hx tW).buy le_rfl (t.tally ρ hρ).2.1,fun j=>blocks_rest o e j,t.width₀ _ τe,(orbit_members e o).trans (t.size _ τe), ψ, ?_,fun x _=>?_⟩
 · have hz:0 ≤ scratch (X s):= (chip_pos ..).le; let C:=sPow P s (grass I); have hf:0 ≤ C :=(BProof.coin_pos ..).le
   change Batch Y s i k h' _ _ _ _ _ V ψ; refine ⟨(Staff.Pays.house W W pW pW tW tW).raise _ _ (Subset.refl _) t.clearance, rollZero _ hf,t.room,g.le,hρ,Girt.rite_c (0:ℂ),fun _ _=>rfl,fun x=>(norm_zero ..).le.trans hf,fun _ _=>?_⟩
   unfold ψ; rw [sub_self,norm_zero]; exact hz
 rw [noble_empty Y s i k W r τ ρ h x]; change ‖(0:ℂ)-0‖ ≤ _; rw [sub_self,norm_zero]; exact (chip_pos ..).le
include pV tV
lemma swallow (τe:(e:ℝ) ≤ sPow P s I)(τw:(w:ℝ) ≤ sPow P s I)(hW:‖spinCoupon Y s i k W V‖ ≤ C) :
    Broom Y s i k (Staff.twin W V (side Y i s)) (grass I) α ρ (2*e) 4 2 (double_bill W V ρ r (temp (X s)) o e) (Staff.matchHue (spinCoupon Y s i k W V)):= by
    let n':= side Y i s; let T:=tent Y H; let t':=temp (X s); let F:= turret W ρ r t' o e; let G:=turret V ρ r t' o e; let D:=BlockP e o; let P':=spinCoupon Y s i k W V; let R:=double_bill W V ρ r t' o e; let x:=hat P.R.L P.x s; let A:= ■ s i k
    have ht:A.p.threshold=t':= (Papal.prices_plot Y s i k paid).1 ▸ (Y.meter.boot s).1; have hb:0 ≤ t':= Work.E04.temp_nonneg _; let φ:= Staff.filmMatch W V P' n' o ρ t' t' r r; let a:=t.tally ρ hρ
    have hm(x:Pane n')(h:WellDrawn Y s i k α D x): let Y':=φ x; let z:= inner ℝ (W.pearl ρ n' r t' x) (V.pearl ρ n' r t' x); let ψ := Staff.matchHue P' ((Staff.twin W V n').material ρ x);
      ‖P'*(↑z:ℂ)-Y'‖ ≤ scratch (X s) ∧ ‖Y'-ψ‖ ≤ scratch (X s):=by
       have hp: α*A.p.threshold < t' := ht ▸ mul_lt_of_lt_one_left A.p.threshold_pos g; -- careful ht substitute
       let H₀:=|ρ| *t'; let L:=skyline (hat P.R.L P.x s); have hL:0 ≤ L :=(chip_pos ..).le; obtain ⟨b,c⟩:= Staff.film_gap W V P' pW pV tW tV ρ hb hL x h.1 (W.passage x o tW h.2 hp) (V.passage x o tV h.2 hp); have hz:0 ≤ H₀:= mul_nonneg (abs_nonneg _) hb; have ht: ‖P'‖ * (2*Staff.armRent e L H₀ w * H₀) ≤ scratch (X s):= (mul_le_mul_of_nonneg_right hW (by unfold Staff.armRent; have t:=SU.group.colorScale_pos; positivity)).trans (a.2.2.2 _ _ τe τw)
       exact ⟨b.trans ht,c.trans ht⟩
    have hf:=a.2.2.1; change Broom _ _ _ _ _ _ _ _ _ _ _ R _;
    refine ⟨(deckVenue W ρ pW t' T _ (terrain Y H (Y.ir i) s).symm tW).mulM (deckVenue V ρ pV t' T _ (terrain Y H (Y.ir i) s).symm tV), ?_,fun x=>(Cadre.and_ (W.sizing pW ρ x hb tW) (V.sizing pV ρ x hb tV)).buy (by decide) ((pow_two _).symm.le.trans hf),fun j=>blocks_rest o e j,t.width₀ _ τe,(orbit_members e o).trans (t.size _ τe),φ, ?_,fun x h'=>?_⟩
    · intro g x; change (F.x*G.x) _ = twist (quantU (tradew n' g)) (F.x x*G.x x); rw [Pi.mul_apply,map_mul]; exact congrArg₂ (· * ·) (W.oneVox ρ r t' n' g x) (V.oneVox ρ r t' n' g x)
    · change Batch _ _ _ _ _ _ _ _ _ _ D φ; refine ⟨(Staff.Pays.house W V pW pV tW tV).raise _ _ (Subset.refl _) t.clearance,?_,t.room,g.le,hρ,Staff.filmed W V P' ..,Staff.filmLayout W V P' o ρ t' t' r r,fun x=>(Staff.film_pay W V P' pW pV ρ t' hb o x).trans ((mul_le_mul_of_nonneg_right hW (sq_nonneg _)).trans a.1),fun x p=> (hm x p).2 ⟩
      have he:= Staff.paintIt P'; have hc:2*‖P'‖ *Staff.rackColor ≤ sPow P s (grass I):= t.hold.trans' (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by norm_num)) (Nat.cast_nonneg _)); exact ⟨he.bright,fun K b x p=>le_trans (he.worth K b x p) (mul_le_mul_of_nonneg_right hc (sq_nonneg _)),fun K b x y q p=>le_trans (he.price K b x y q p) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (norm_nonneg _))⟩
    · rw [show R.x x= W.rungWeave _ _ _ _ _*V.rungWeave _ _ _ _ _ from rfl, noble_civic Y s i k W V r t' ρ h x]; exact (hm x.1 h').1
#print axioms peacock
#print axioms swallow
end Jewel
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
