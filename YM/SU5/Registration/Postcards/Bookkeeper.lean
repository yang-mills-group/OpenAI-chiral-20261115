import YM.SU5.Registration.LineUp.SharpRaster
import YM.SU5.Registration.Postcards.Vacation
import YM.SU5.Registration.M13
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "G" => bands (P.seasons 3 ξ)
local notation "Ω" => P.vacuumEntry x
local notation "ζ" => P.heaven 3 ξ
local notation "κ" => Lead.Clan
open Swatch SatinWFixed
open _root_.YM.Boundary.Probe

open _root_.YM.SatinWFixed Carton
open _root_.YM.SatinWFixed Courts
open Seld.Poin (Each)
universe ν
variable {I:Type ν}{n:ℕ}(Q:I→P.Swatch)(u:∀ i,(Q i).WPermit x 3)
local notation "Λ"=> epaulets I
open YM.SatinWFixed.Passage
structure TravelReady (P:Spine) {I:Type ν} (Q:I→P.Swatch): Prop where
 desk : P.all_desk 3 (P.school Q)
 cards (n:ℕ)(t:Fin n→I×Bool): P.Paper 3 (Each n) (P.school Q ∘ t)
lemma TravelReady.along (p:P.TravelReady Q)(x:P.Spectrum0 3):∀ i,(Q i).WPermit x 3:=fun i=> (p.desk (i,true)).all x -- defeq?
variable (K:P.Register)(p:P.TravelReady Q)
local notation "Φ" => P.Spectrum0 3
variable (W₀: P.Spectrum0 3→WView (epaulets I))(F:P.Spectrum0 3→InkWaves (epaulets I))
 -- Moors. no repeating election needed even at a.e. use. ink authentic on each.
local notation "B!" x:max=> P.store x Q (p.along P Q x) -- binder order
local notation "μ"=>P.pillars 3
variable (h:∀ x: P.Spectrum0 3,InkPort (P.store x Q (p.along P Q x)) (F x) (W₀ x)) (v:Fin n→ epaulets I) (q:Points n)
local notation "K!" x:max=> (F x).entrance q
private lemma heat_books (A:P.Swatch)(h:P.ThresholdPrice 3 A)(u:∀ x:P.Spectrum0 3,A.WPermit x 3) (s:ℝ≥0)(t:0<s): ∃ C≥(0:ℝ),∀ x :P.Spectrum0 3, ‖(u x).atHeat s‖≤ C:=by
 obtain ⟨c,t,v⟩:= h s t; refine ⟨c,t,fun x=>?_⟩ -- t shadow!
 exact limit_ceiling (fun z=> ((u x).arriving s (by assumption) z).1) t (v.mono (fun _ y=>y x))
lemma customer_voter (u':epaulets I)(s:ℝ≥0)(t:0<s):∃ v≥(0:ℝ),∀ x:P.Spectrum0 3, ‖(B! x).bar s u'‖≤ v:=by
 induction u' using Finsupp.induction_linear with
 | zero => exact ⟨0,le_rfl,fun i=> (by simp)⟩
 | add y z hy hz=>
    obtain ⟨a,e,g⟩:=hy; obtain ⟨b,v,hu⟩:=hz; simp_rw [map_add]; exact ⟨a+b,add_nonneg e v,fun x=>(norm_add_le ..).trans (add_le_add (g x) (hu x))⟩
 | single i c=>
    obtain ⟨a,e,g⟩:= P.heat_books (P.school Q i) (p.desk i).threshold (fun x=> P.praise x Q i (p.along P Q x)) s t; simp_rw [ show Finsupp.single i c=c • pupil i from (by simp [pupil]),map_smul,norm_smul,P.scroll_pupil];
    exact ⟨‖c‖*a,mul_nonneg (norm_nonneg _) e,fun x=> mul_le_mul_of_nonneg_left (g x) (norm_nonneg _)⟩
private lemma sep_motion {Gz:Hilbert}(Z:OS.Semigroup Gz timeAxis){x:Gz}(g:Moored Z x)(v:OS.Cross timeAxis): Seld.M Z v.val x=x:=by
 let a:= g.space v.val; rw [show SEP timeAxis v.val=v from ?_] at a; exact a; apply Subtype.ext; change v.val-v.val timeAxis • basis timeAxis=v.val; simp only [show v.val timeAxis=0 from v.property,zero_smul, sub_zero]
lemma book_moor (x:P.Spectrum0 3)(d:P.lodestar 3 x) : Moors (B! x):=by
 intro y g; let Z:= (P.seasons 3 (P.advocate 3 x 3)); refine (P.heavenRank 3 _ (d 3) y).2 ⟨(heat_iff_edge 3 Z y).1 g.fixed,?_⟩
 intro v; exact Eq.trans (DFunLike.congr_fun (Seld.laneslot Z v).symm y) (sep_motion Z g v)
lemma book_series :∃ (F:Φ→InkWaves (epaulets I))(W:Φ→WView (epaulets I)),∀ x:Φ,InkPort (B! x) (F x) (W x):=by
 choose F W h using fun x:Φ=> InkPort.obtainF (B! x); exact ⟨F,W,h⟩
variable (f:q∈generic n)(g:q∈Wheeled n)
private lemma glyph_clock : q∈Wheeled n→ LightsCross 3 (Each n) (qua q):= fun p=> (List.pairwise_lt_finRange n).imp fun z=> p z
local notation "TQ" => Fin n→I× Bool
include f g
lemma entry_together (A: Fin n→I×Bool) : P.Passport 3 (Each n) (P.school Q ∘ A) (fun i x=> P.praise x Q (A i) (p.along P Q x)) (qua q) := p.cards n A (fun i x=> P.praise x Q (A i) (p.along P Q x)) _ (glyph_clock q g) (star_sited f) -- abbrev can't use variable proofs w/o include
omit f g
abbrev coupons (A: Fin n → I×Bool): ℂ:=∏ i:Fin n,(v i) (A i)
lemma expans (x:Φ): (K! x) v=∑ A∈seatPlan v, (coupons v A) • ((K! x) (pupil ∘ A)):= by
 let B(i:Fin n): Module.Basis (I×Bool) ℂ (epaulets I):=Finsupp.basisSingleOne; exact Multilabel.expansion B _ v
include h f g K
lemma customer_read_tour (A:Fin n→I×Bool): Continuous (fun x:Φ=> (K! x) (pupil ∘ A)):= by
 let t₁(i:Fin n)(x:Φ):= P.praise x Q (A i) (p.along P Q x); have hp(k:Φ):(F k).entrance q (pupil ∘ A) = P.EuCost k 3 (Each n) (fun i=>(t₁ i k).atHeat) (qua q):=by rw [← sweep_entrant]; exact (P.actual_wick k (u:=p.along P Q k) (Q:=Q) (q:=q) (Rz:=F k) (Wm:=W₀ k) (pz:=h k) (A:=A) g).symm
 simp_rw[hp]; exact P.continuum_statement 3 K (Each n) (P.school Q ∘ A) t₁ (qua q) (P.entry_together Q p q f g A) (star_sited f) (glyph_clock q g) (fun i _=> (p.desk (A i)).being)
omit f g
lemma register_album : Album (P.pillars 3) F (fun x=> P.store x Q (p.along P Q x)) (r_star I) := by
 refine ⟨fun x=>(h x).strict_mat,fun x=> P.preserves_income x Q _,P.customer_voter Q p,?_, (P.many_stars 3 K).mono (fun x d=> P.book_moor Q p _ d)⟩
 intro l k; let t:= ordered l; let a:=order_sal k.sal; let b:= perm_auction (order_cost _) k; let X':=idsOf t; let Y':=pointsOf t; unfold Figures AdmitMom; change Continuous fun x=> (F x).entrance Y' X';
 simp_rw [P.expans F X' Y']; exact continuous_finsetSum _ fun i _=> (continuous_const (y:=coupons X' i)).smul (P.customer_read_tour Q K p W₀ F h Y' ((auction_iff _).1 b) ((chrono_iff _).1 a) i)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.book_series
#print axioms Spine.book_moor
#print axioms Spine.register_album
#print axioms Spine.expans
#check Spine.expans
