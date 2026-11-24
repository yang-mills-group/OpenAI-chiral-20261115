import ForceSatinCP4
import YM.SU5.SatinWard.Resolution.Celsius
import Velour.Crepe.Wiggle
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
namespace SlopeCharge
variable (P:Spine){j:Axis}{o:VelourBoard.Cell}{w s:ℕ} (H:0<w){σ:ℕ→ℕ}(Z:Tendsto σ atTop atTop) (g:P.NightCop)
local notation "K'" => P.calibration
local notation "Y₀" => P.run
local notation "N₀" => P.par.R.L
local notation "H₁" => P.large
local notation "tθ" => hat P.par.R.L P.par.x s
variable {m:ℕ}{θ:ℝ}(rate:ℝ) {S:Finset Cover} {U:ℕ→Buffered.Family P.calibration}
 (T:P.Test)(Q:BQueue S U (T.val)) (p:VelourBoard.Parcel P.calibration w o 0 S)
include g Z H p Q
lemma seats (v:o j=0)(t:Dapper K' o w tθ)(a:∀ᶠ k:ℕ in atTop, InkTag Y₀ m rate s (ΦWork P (σ k)) (ζWork P (σ k)) H₁ S (U k)) :
 ‖P.reading j s T‖ ≤ Real.exp (2*integralTill tθ):=by
 let h:=Q.landing; let θ:=Real.exp (2*integralTill tθ)
 have he:Between K' j 0 (ruler (K').B*(w:ℤ)) S:=by have u:=p j; unfold VelourBoard.Wall at u; simpa only [Pi.zero_apply, v, mul_zero,zero_add,mul_one] using u
 let f:=P.positiveVox j s S T h (fun y p=> (he y p).1); let e:P.Card j s w:=⟨f,S,h, he⟩; let X:=P.Box j s w H e
 have hz:Settle Y₀ H₁ s P.projection w U σ o θ:=by unfold Settle; exact a.mono fun i z d A B h=> InkTag.bill P.run m rate s _ _ H₁ z t p d h
 have hv:‖X‖ ≤ θ:= Presidential.boardPrice Y₀ H₁ P.law s P.projection j w U S σ Z θ (Real.exp_pos _) H o g p v hz _ e Q -- verify order.
 change ‖(P.reading j s T).val‖ ≤ θ; rw [P.at_label,show T=P.entryTest j s e from rfl,P.compresses j s w H]; refine ContinuousLinearMap.opNorm_le_bound _ (show 0≤ θ from (norm_nonneg _).trans hv) ?_; intro y; let z:= P.inHil j y; apply ((P.vacuum j).norm_orthogonalProjectionOnto_apply_le (X z)).trans; exact (ContinuousLinearMap.le_opNorm X z).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg z))
lemma dusting (a:∀ᶠ k:ℕ in atTop, InkTag Y₀ m rate s (ΦWork P (σ k)) (ζWork P (σ k)) H₁ S (U k))(t:Dapper K' o w tθ)(j:Axis) : ‖P.reading j s T‖ ≤ Real.exp (2*integralTill tθ):=by
 let T':=P.shifts j (-(o j)) T; let D:= fun i:Axis=> if i=j then 0 else o i; let u:=plow K' j (-(o j)) S
 let q:=fun i:ℕ=> relocate K' j (-(o j)) (U i)
 have h:BQueue u q T'.val:=Q.station j _; have he:VelourBoard.Parcel K' w D 0 u:=by
    intro i y v; obtain ⟨z,v',rfl⟩:= plow_stays K' j (-(o j)) S v; specialize p i z v'; simp only [SlabMark.moves]; unfold VelourBoard.Wall at p ⊢; dsimp only [D]; by_cases hj:i=j
    · subst j; simp only [ite_true]; constructor <;> linarith only [p.1,p.2]
    split_ifs; exact p
 rw [show P.reading j s T=P.reading j s T' from (P.shifted_read j s (-(o j)) T).symm]; exact seats P H Z g rate T' h he (if_pos rfl) t (a.mono fun i a=> InkTag.shift Y₀ _ _ _ _ _ _ a j _)
-- Now any claim settled with BQ.estate horizon tax.y.
omit H p Q
variable {F:ℕ→ Buffered.Family P.calibration} {K:P.Register} {b C:ℝ}{t:ℕ→ℝ}{r:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
 (h:CouncilGrant P K b C t σ r β)
omit g Z
variable (m) {z:ℂ}{f:ℕ→ℂ}
structure Costed (T:P.Test) (f:ℕ→ℂ)(F:ℕ→Buffered.Family P.calibration) (S:Finset Cover)(z:ℂ)(s:ℕ) (m:ℕ)(rate:ℝ)(σ:ℕ→ℕ): Prop where
 slope: Tendsto f atTop (𝓝 z)
 primitive: BQueue S F T.val
 inks: ∀ᶠ k:ℕ in atTop, AffordInk P.run m rate s (ΦWork P (σ k)) (ζWork P (σ k)) H₁ S (F k) (f k)

lemma texture : BQueue S U T.val→ Tendsto f atTop (𝓝 z) → ∀ α:ℂ, BQueue S (fun k=> Papal.SkyTax.caramel (f k) α (U k)) (Papal.SkyTax.caramel z α T.val):=by
 intro p f α; let r:=BQueue.stay (K:=K') (InTest.one (S:=S)) (C:=1) zero_lt_one (?v)
 case v=> exact fun t z=> show ‖(1:Fock.FC _)‖ ≤ (1:ℝ) from (norm_one).le
 exact cueSum r (cue_scale (cueSum p (cue_scale r _ _ f.neg)) _ _ tendsto_const_nhds)
variable {T}
include g h
omit Z
lemma funding (a:0<rate)(v:rate≤1):∀ᶠ s:ℕ in atTop,∀ (S:Finset Cover)(F:ℕ→Buffered.Family P.calibration)(T:P.Test)(f:ℕ→ℂ)(z:ℂ)(o:VelourBoard.Cell)(w:ℕ),
   Costed P T f F S z s m rate σ → Dapper K' o w (hat N₀ P.par.x s) → 0<w → VelourBoard.Parcel K' w o 0 S →
   ∀ (j:Axis)(y:P.Spectrum0 j), ‖P.singleState j s y T-z‖ ≤ wane (hat N₀ P.par.x s):=by
 let D':= h.purse.born ; let C':= D'.mail; let Y':=h.order.tendsto_atTop
 filter_upwards [ink_warm Y₀ b C m rate H₁ D'.shearPos C' a v,h.purse.tilt,h.channels,(LocalLimit.turnover P.par).eventually (Papal.roar m b),(LocalLimit.turnover P.par).eventually_gt_atTop 0] with s e u t r p S F T f z o w B z1 z2 z3 j y
 let t':=hat N₀ P.par.x s; let A:=forceDose t'; let G':=P.singleState j s y T-z; let J:=integralTill t'; have he:0<A:=Real.rpow_pos_of_pos p _; have hδ: 0<J:=Real.rpow_pos_of_pos p _
 obtain ⟨Z,u',v'⟩:= secant he G'; let G:= fun k=> Papal.SkyTax.caramel (f k) Z (F k); let tY:=texture P T B.primitive B.slope Z
 let V:P.Test:=1+ Z • (T+(-z) • 1)
 have g':∀ᶠ k:ℕ in atTop, InkTag P.run m rate s (ΦWork P (σ k)) (ζWork P (σ k)) H₁ S (G k):=by filter_upwards [B.inks,Y'.eventually (P.history.finance s)] with i a uo; exact e _ _ uo.enters uo.depth (u _ _ uo.depth uo.enters) (t _ _ uo.enters) _ _ _ a Z u'
 have hz: ‖1+Z*G'‖ ≤ Real.exp (2*J):=by
    have hx:P.singleState j s y V=1+Z*G':=by unfold V G';rw [map_add,map_smul,map_add,map_smul,smul_eq_mul,smul_eq_mul,P.single_state,P.reading_unit,map_one,mul_one]; rfl
    rw [← hx,P.single_state]; exact (NonUnitalStarAlgHom.norm_apply_le ..).trans (dusting P z2 Y' g rate V tY z3 g' z1 j) -- argument elaboration
 rw [v',←Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)] at hz
 have hy: 6*J≤1:=r.2.2.2.1
 have hh: |Real.exp (2*J)-1| ≤ 2*(2*J):=by simpa only [abs_of_nonneg (show 0≤ 2*J by positivity)] using Real.abs_exp_sub_one_le (x:=2*J) (by rw [abs_of_nonneg (show 0≤2*J by positivity)]; linarith)
 apply le_of_mul_le_mul_left _ he; change A*‖G'‖≤A*wane t'; linarith only [hz,hδ,(abs_le.mp hh).2,show 12*J≤ A * wane t' from r.2.2.2.2]
end SlopeCharge
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
