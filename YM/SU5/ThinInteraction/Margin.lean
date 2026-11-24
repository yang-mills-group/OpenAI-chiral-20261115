import YM.SU5.ThinInteraction.Anchor
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 220000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open YM.SatinThin
namespace Thinning
open Set Aria Six Casting
open scoped BigOperators
variable (P:Spine) (x:P.Spectrum0 3) (s n t:ℕ) (Z:Lead.Clan)
local notation "S" => P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "W" => ShopP P s n
local notation "T" => timeMesh P.par
local notation "d" r:max => offset false r
local notation "τ" => P.probeWidth s n 3
local notation "M" => P.singleState 3 t x
local notation "A" => P.FTest Z s n
local notation "Y" => P.RTest Z s n
namespace Portfolio
open OS.Semigroup Spectral
local notation "H" => P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "Ξ" => (S).ℚmeasure
local notation "Q" => (Ξ).region
local notation "E" => (S).E
local notation "v₀" => alk s n x Z false
local notation "U" => P.cartage 3 (P.otherSpectrum 3 3 x)
variable {P x s n Z}{a:ℝ}(p:Portfolio x s n a Z)
def expanded : H := ((p.amp:ℝ):ℂ) • Q p.purchases v₀
lemma by_heat : p.intended = E (twiceP P s n) p.expanded := by
  let y:=Q p.purchases; let w:= E (twiceP P s n); let k:ℂ:= p.amp
  exact Eq.trans (congrArg (fun x:H=>k • x) (commutes_at Ξ _ (p.purchases_meas) v₀ (YM.Six.rep_heat (S) _))) (map_smul w k (y v₀)).symm

def little : Set E4 := p.purchases ∩ squareTile p.k
lemma little_meas : MeasurableSet p.little := p.purchases_meas.inter (tile_meas p.k)
abbrev witness : H := ((p.amp:ℝ):ℂ) • Q p.little v₀
lemma witness_size : ‖p.witness‖=1 := norm_anchor Ξ _ p.little_meas v₀ p.positive
lemma witness_in : Q p.little p.witness=p.witness:= fix_squaring Ξ _ p.little_meas v₀ _
lemma witness_catch : Q p.little p.expanded = p.witness := by
  let v:= Q p.little; let a':ℂ:=p.amp
  exact (map_smul v a' (Q p.purchases v₀)).trans (congrArg (fun x:H=> a' • x) (squaring Ξ _ p.little_meas v₀ _ p.purchases_meas Set.inter_subset_left))
lemma little_time {w : E4} (v:w∈p.little): YM.time w ≤ (p.m:ℝ)+2:= v.1.2.2
lemma little_space {w : E4} (v:w∈p.little) (i:Fin 3): |YM.spatial w i - momentum p.k i|≤1 := by
  obtain ⟨he,hx⟩:=v.2 i; change |_ - ((p.k i:ℤ):ℝ)| ≤ _; apply abs_le.mpr; constructor <;> linarith
private def opAsk (i:Vantage) : (H).Op := pp p i • ((U i) * E (i 3).toNNReal)
private lemma spot (i:Vantage)(v:2*τ< i 3): aspect p i p.intended=p.opAsk i p.expanded := by
  let q:=E (transit P s n i); let r:= E (twiceP P s n); let z:= p.expanded; let t':=(U i)
  have hc: transit P s n i+twiceP P s n=(i 3).toNNReal:= by
    have h:=P.width_here s n 3; have hp:0< i 3:=by linarith
    ext; rw [NNReal.coe_add,transit,twiceP,Real.coe_toNNReal _ (sub_nonneg.mpr v.le), Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ hp.le]; ring
  have ht := merge H (S) _ _ _ z hc
  exact (congrArg (fun v:H=> pp p i • t' (q v)) p.by_heat).trans (congrArg (fun v:H=> pp p i • t' v) ht)
where
  merge (X:Hilbert)(V:OS.Semigroup X (3:Axis))(s n t:ℝ≥0)(x:X.space)(h:s+n=t): V.E s (V.E n x)= V.E t x := by rw [←ContinuousLinearMap.comp_apply,← V.time,h]
private lemma reinvoice (i:Vantage)(v:0≤ i 3) : (Ξ).Represents (YM.SatinThin.glow p.m (momentum p.k) (spacePart i) (i 3)) (p.opAsk i) := by
  let B:= YM.Six.rep_phasor (S) (spacePart i)
  let Q':= YM.Six.fade (i 3).toNNReal
  have he : (Ξ).Represents (YM.Six.phasor (spacePart i)) (U i) := Eq.mp (congrArg ((Ξ).Represents (YM.Six.phasor (spacePart i))) (P.cart_space x i).symm) B
  refine (he.mul (YM.Six.rep_heat _ _)|>.smul (pp p i)).congr fun w => Eventually.of_forall fun k=> ?_
  simp only [YM.SatinThin.glow, Pi.smul_apply,Pi.mul_apply,smul_eq_mul]
  rw [mul_assoc]; change pp p i * (_* ↑(Real.exp (-(((i 3).toNNReal:ℝ)*YM.time k)))) = pp p i * _; rw [Real.coe_toNNReal _ v]
lemma aspect_cont (v : H): Continuous (fun i=> aspect p i v):= by
  apply (pp_cont p).smul
  exact P.caravan 3 (P.otherSpectrum 3 3 x) id _ continuous_id (((S).continuousE v).comp (by unfold transit; fun_prop))
lemma supply (F:SampleDose)(v:H): Integrable (fun i:Vantage=> (F.val i:ℂ) • aspect p i v) := weightedMoney F H _ (aspect_cont p v)

-- Tex test footprint constraints; easy to pay them for a fixed SampleDose.
def LittleLayout (F:SampleDose): Prop := tsupport F.val ⊆ {i:Vantage| i 3 ≤ 2 ∧ ∀ j:Fin 3, |i j.castSucc| ≤ 1/16}

lemma real_floor (F:SampleDose) (e:roofed P s n F)(h:LittleLayout F){i:Vantage}(v:i∈ tsupport F.val) :
    Real.exp (-4)/2 ≤ (inner ℂ p.witness (aspect p i p.intended)).re := by
  have hs:= h v
  let A':= p.little; let L':= p.opAsk i; let C (x:H):= (inner ℂ p.witness x).re
  have he: 2*τ < i 3:= e i v; have ht : 0 ≤ i 3 := (mul_nonneg zero_le_two (P.width_here s n 3).le).trans he.le
  have hv : ∀ t∈ A',Real.exp (-4)/2 ≤ (YM.SatinThin.glow p.m (momentum p.k) (spacePart i) (i 3) t).re :=
    fun t v=> glow_floor p.m (momentum p.k) (spacePart i) t (i 3) ht hs.1 (p.little_time v) hs.2 (p.little_space v)
  exact (unit_floor Ξ p.little p.little_meas p.witness L' (p.reinvoice i ht) p.witness_in p.witness_size hv p.expanded p.witness_catch).trans_eq (congrArg C (p.spot i he).symm)
private lemma intoNorm (X:Hilbert)(x y:X)(e:‖x‖=1) : (inner ℂ x y).re ≤ ‖y‖:=
  Complex.re_le_norm _ |>.trans ((norm_inner_le_norm ..).trans_eq (by rw [e,one_mul]))
-- general compact real estimate
private lemma bill_floor (X:Hilbert)(F:SampleDose)(h:F.Normalized)(f:Vantage→X)(w:Continuous f)(v:X){b:ℝ} (p:∀ i∈ tsupport F.val,b≤ (inner ℂ v (f i)).re):
    b ≤ (inner ℂ v (∫ i:Vantage,(F.val i:ℂ) • f i)).re:= by
  let G(i:Vantage):= (F.val i:ℂ) • f i; let k(i:Vantage) := inner ℂ v (G i);
  have hi:Integrable G := weightedMoney F X f w
  have hv: Integrable k := (hi.const_inner v) -- tune
  rw [←integral_inner hi]; change b ≤ RCLike.re (K:=ℂ) (∫ i,k i); rw [←integral_re hv]
  have ht: b=∫ i:Vantage,F.val i*b:=by rw [integral_mul_const,h.2,one_mul]
  have hw : ∀ i:Vantage, F.val i*b ≤(k i).re := by
    intro i; unfold k G; rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; by_cases H₂ : i∈tsupport F.val
    · exact mul_le_mul_of_nonneg_left (p i H₂) (h.1 i)
    rw [image_eq_zero_of_notMem_tsupport H₂,zero_mul,zero_mul]
  exact ht.trans_le (integral_mono ((F.smooth.continuous.integrable_of_hasCompactSupport F.budget).mul_const b) hv.re hw)
lemma ideal_floor (F:SampleDose) (e:roofed P s n F)(h:LittleLayout F)(v:F.Normalized):
    Real.exp (-4)/2 ≤ ‖column p F p.intended‖ :=
    (bill_floor H F v _ (p.aspect_cont p.intended) p.witness (fun _ w=> p.real_floor F e h w)).trans (intoNorm H p.witness (column p F p.intended) p.witness_size)
#print axioms ideal_floor
end Portfolio
end Thinning
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
