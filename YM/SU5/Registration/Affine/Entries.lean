import YM.SU5.Registration.Heave.AirCarry
/-!
  # The Euclidean, late-consultation fields over our M4 map
  Unprojected ColorHil -> G uses coherence of this same elected character. G
  has powers w.r.t. actual physical clock, not arbitrary GNS Hilbert built per axis.
  Work with WPermit estimates on ANY stamped family with coefficients at its
  native printed height. Use to compute Schwinger prices and ordered transfer.
  Projection in pricing sharp readings from G is only qualified where authorized
  (`Ellis` & all-coordinate separations etc.).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
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
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
/-- Symbol with stamps including complex coefficient allowed. Use symbol both
as potentially scaled primitives for joint announcements and later these limits
are linear fields even if budgets prove only on each such stamped sequence
(with testing required for the whole family chosen for rotation). -/
structure Swatch (P:Spine) where
  fieldA : ℕ→P.Apron
  rate : ℕ→ℂ

namespace Swatch
variable {P} (A:P.Swatch)
local notation "Ξ"=>A.rate
local notation "κ" i:max=> (A.fieldA i).allowance P
abbrev ordinary (Z:ℕ→P.Apron) : P.Swatch:= ⟨Z,fun _=>1⟩
noncomputable def turn (l:Axis) : P.Swatch := ⟨fun i=> (A.fieldA i).kiss P l, fun i=> star (A.rate i)⟩
abbrev Finishes : Prop := ∀ j:Axis,Tendsto (fun i=> (A.fieldA i).allowance P j) atTop (𝓝 0)
noncomputable abbrev Wstage (l r:ℝ≥0)(i:ℕ) : (G).Op:= Ξ i • P.stageG a ξ (A.fieldA i) l r
structure WPermit :Prop where
 thin : A.Finishes
 budget : RisePrice (fun t i=> A.Wstage x a t t i)
 convergence (t:ℝ≥0)(h:0<t) : SatinRegistration.Travels (fun i=> A.Wstage x a t t i)
lemma Wstage_more (i:ℕ){l r s t:ℝ≥0}(h:(A.fieldA i).allowance P a≤l)(p:l≤r)(h':(A.fieldA i).allowance P a ≤ s)(p':s≤t): A.Wstage x a r t i= T₀ (r-l)* A.Wstage x a l s i * T₀ (t-s):=by
 unfold Wstage stageG; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,P.stage_more _ _ _ h p h' p',P.bank_both]
lemma Wstage_turn (i:ℕ)(s t:ℝ≥0) : (A.turn a).Wstage x a t s i= (A.Wstage x a s t i).adjoint:=by
 let z:= P.toStageG a ξ; let H':=(P.physicalEnergy a ξ).E; let p:=A.fieldA i; let w:= (A.fieldA i).allowance P a; let q:=p.kiss P a; let r:=A.rate i; have ht:q.engine P a ξ=(p.engine P a ξ).adjoint:= (p.peer P a ξ).symm -- orientation check
 have hv(U:(H).Op): z U.adjoint=(z U).adjoint:=by
    have he(v:(H).Op): z v=P.tableau a ξ 0 v:=by unfold tableau; rw [neg_zero,P.cart_zero]; rfl
    rw [he,he,P.boards_star]
 change star r • z (H' (t-w)*q.engine P a ξ * H' (s-w))=(r • z (H' (s-w)*p.engine P a ξ*H' (t-w))).adjoint
 rw [ContinuousLinearMap.adjoint.map_smulₛₗ r (z _),← hv,ht]
 simp only [← ContinuousLinearMap.star_eq_adjoint,star_mul]
 simp only [ContinuousLinearMap.star_eq_adjoint,H',(P.physicalEnergy a ξ).sym, mul_assoc]
 rfl -- tune
lemma WPermit.reflector (p:A.WPermit x a) : (A.turn a).WPermit x a:=by
 refine ⟨p.thin,?_,fun t g=>?_⟩
 · obtain ⟨k,C,h,v⟩:=p.budget; refine ⟨k,C,h,fun t g e=>?_⟩
   simpa only [Wstage_turn, ContinuousLinearMap.adjoint.norm_map] using v t g e
 obtain ⟨V,h⟩:= Flying.settles (p.convergence _ g); simp_rw [A.Wstage_turn ..]; exact h.adjoint.Cauchy
namespace WPermit
variable {x a A}
variable (p:A.WPermit x a)
include p in
lemma delivery : Delivery S (fun t=> A.Wstage x a t t):= by
 refine ⟨fun t h s=> ?_, fun t h y=>(p.convergence t h y).1,p.budget⟩
 have hh:t≤ t+s:= self_le_add_right ..
 refine ((p.thin a).eventually (gt_mem_nhds h)).mono fun i h=>?_ ; simpa only [add_tsub_cancel_left] using A.Wstage_more x a i (show (A.fieldA i).allowance P a < t from h).le hh (show (A.fieldA i).allowance P a < t from h).le hh
abbrev atHeat (p:A.WPermit x a) : ℝ≥0→ (G).Op:= p.delivery.accepts
abbrev atBoth (p:A.WPermit x a) : ℝ≥0→ℝ≥0→ (G).Op:= bothPads S p.atHeat
lemma arriving (s:ℝ≥0)(v:0<s): Flying (A.Wstage x a s s) (p.atHeat s):=by
 obtain ⟨V,h⟩:= Flying.settles (p.convergence s v);
 have hp:V=p.atHeat s:=by ext1 x; exact tendsto_nhds_unique (h x).1 (p.delivery.accepted s v x)
 rw [← hp]; exact h
lemma atBoth_def {s l r:ℝ≥0}(v:0<s)(u:s≤l)(w:s≤r): p.atBoth l r=T₀ (l-s)*p.atHeat s*T₀ (r-s):= arbitrary_pad S _ v u w p.delivery.isSound
lemma atBoth_turn (r s:ℝ≥0): (p.reflector x a A).atBoth r s=(p.atBoth s r).adjoint:=by
 have he:(p.reflector x a A).atHeat= (fun t=> (p.atHeat t).adjoint):= p.delivery.reverse (p.reflector x a A).delivery (fun s i=> (A.Wstage_turn x a i s s).symm)
 unfold atBoth bothPads; rw [←ContinuousLinearMap.star_eq_adjoint,star_mul,star_mul]; simp only [ContinuousLinearMap.star_eq_adjoint,(S).sym,mul_assoc]; rw [min_comm s r]; exact congrArg (fun (U:(G).Op)=> T₀ _ * (U * T₀ _)) (congrFun he (min r s)) -- or rw[he] not because proof irrelevance guesses in rhs p.atHeat when metavars? p differs because A.turn possibly defeq A via fields of x? inspect
lemma stage_limit {r s:ℝ≥0}{F G':ℕ→ℝ≥0}(h:0<r)(u:0<s)(v:Tendsto F atTop (𝓝 r))(t:Tendsto G' atTop (𝓝 s)) : Flying (fun i=> A.Wstage x a (F i) (G' i) i) (p.atBoth r s):=by
 let b:=min r s/2
 have hb:0<b:=half_pos (lt_min h u); have hl:b<r:= (half_lt_self (lt_min h u)).trans_le (min_le_left ..); have hd:b<s:=(half_lt_self (lt_min h u)).trans_le (min_le_right ..)
 rw [p.atBoth_def hb hl.le hd.le]
 refine Flying.late (((Flying.heat S (v.sub_const b)).multiply (p.arriving b hb)).multiply (Flying.heat S (t.sub_const b))) ?_
 filter_upwards [v.eventually (le_mem_nhds hl),t.eventually (le_mem_nhds hd),(p.thin a).eventually (ge_mem_nhds hb)] with i h u g
 exact (A.Wstage_more x a i g h g u).symm -- ge uses ≥? notation ge_mem_nhds hi maybe p∈ lower
end WPermit
end Swatch
/- Conveniences for using the M4 fields -/
open Swatch
-- purchase from M4. Include turn & any axis versions as given in M7.
variable (A:ℕ→P.Apron)
local notation "F"=> Swatch.ordinary A
lemma affine_cap (t:CapReady P x A) : (Swatch.ordinary A).WPermit x 3:=by
 have h(i:ℕ)(s:ℝ≥0):(F).Wstage x 3 s s i=P.manage x (A i) s:=by unfold Swatch.Wstage manage; rw [P.honestBridge]; exact one_smul ..
 refine ⟨fun j=> P.all_width_paid x _ _ t,?_,?_⟩
 · simp_rw [h]; exact t.2.2
 simp_rw [h]; exact t.2.1
lemma affine_heat (t:CapReady P x A) : (P.affine_cap x A t).atHeat=P.managed x A t:=by
 funext s; by_cases u:0<s
 · refine Flying.unique (P.affine_cap x A t|>.arriving s u) (Flying.late (P.received_moves x A s t u) ?_) -- tune
   exact Eventually.of_forall fun i=> (one_smul ℂ (P.stageG 3 (P.advocate 3 x 3) (A i) s s)).symm
 simp [WPermit.atHeat, managed, Delivery.accepts,u]
lemma affine_field (t:CapReady P x A) :
  let h:=(P.affine_cap x A t).delivery
  SatinRegistration.field (P.seasons 3 (P.advocate 3 x 3)) h.accepts (h.isSound) h.paid=P.pointField x A t:=by
 let g:= P.delivery_cap x A t; let h:=(P.affine_cap x A t).delivery
 have hz:h.accepts=g.accepts:= P.affine_heat x A t
 change SatinRegistration.field _ h.accepts _ _=SatinRegistration.field _ g.accepts _ _; congr
lemma affordable_everywhere (q:P.Funding x A) (l:List Axis):
    (Swatch.ordinary (fun i=>(A i).pivot P l)).WPermit x a:=by
 let f:= (fun i=>(A i).pivot P l); have hp(t:ℝ≥0)(i:ℕ):(ordinary f).Wstage x a t t i=P.stageG a ξ (f i) t t:= one_smul ..
 refine ⟨?_,?_,fun t h=>by change SatinRegistration.Travels (fun i=> (ordinary f).Wstage x a t t i); simp_rw [hp]; exact q.travels a l t h⟩
 · unfold Swatch.Finishes; intro j; have he (X:P.Apron): (X.pivot P l).allowance P j=X.allowance P j:= NNReal.eq (((X.pivot P l).width_real P j).symm.trans ((X.pivot_w j P l).trans (X.width_real P j)))
   change Tendsto (fun i=> ( (A i).pivot P l).allowance P j) _ _; simp_rw [he]; exact q.ft j
 obtain ⟨k,C,h,v⟩:= q.price a l; refine ⟨k,C,h,fun t u p=>?_⟩
 change ∀ᶠ i:ℕ in atTop,(t:ℝ)^k * ‖(ordinary f).Wstage x a t t i‖≤C; simp_rw [hp]; exact (v t u p).mono fun i t' => (mul_le_mul_of_nonneg_left (P.toG_cost a ξ _) (by positivity)).trans t'
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.Swatch.WPermit.stage_limit
#print axioms Spine.Swatch.WPermit.atBoth_turn
#print axioms Spine.affine_cap
#print axioms Spine.affine_field
#print axioms Spine.affordable_everywhere
