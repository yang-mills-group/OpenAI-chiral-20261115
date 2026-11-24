import YM.SU5.Registration.Affine.Constellation
import YM.SU5.Registration.Affine.Collateral
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
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
variable (A:P.Swatch)
local notation "ν" i:max=> (A.fieldA i).allowance P a
local notation "η" i:max=> (A.fieldA i).realWidth P a
-- budget over x before Fourier/kinetic contour. At every positive t centers can get tolerance arbitrarily small; for full purchases include powers after that height. These weaker for CHANGING x with transfers already funded on individual. Use stronger WPermit or Funding for powers. Plant over all γ even though detector incl rate & stamp from the originally selected x's options.
def ThresholdPrice : Prop:=∀ t:ℝ≥0,0<t→OnTab atTop (fun i x=> A.Wstage x a t t i)
def ModSpaces : Prop:= A.Finishes ∧ ∀ (t:ℝ≥0),0<t→∀ r:ℝ,0<r→∃ (O:ℕ→Vantage)(D:∀ x:P.Spectrum0 3,(P.ManyF a (P.advocate 3 x a)).Op), Tendsto O atTop (𝓝 0) ∧ UpTo atTop (fun i x=> P.cane x a (A.Wstage x a t t i) (O i)) (fun _ x=>D x) r -- notation G clashes; edit
lemma cane_ofZero (B:(GOp x)) : P.cane x a B 0=B:=by unfold cane; rw [neg_zero, P.cart_zero]; exact (mul_one _).trans (one_mul _) -- `type unification` tune
lemma cane_distance (X Y:GOp x)(p:Vantage): dist (P.cane x a X p) (P.cane x a Y p) ≤ dist X Y:=by rw [dist_eq_norm,dist_eq_norm,show P.cane x a X p-P.cane x a Y p=P.cane x a (X-Y) p from (by unfold cane; rw [mul_sub,_root_.sub_mul])]; apply P.cane_norm
lemma stoves_price (t u:ℝ≥0)(B:(GOp x)) : ‖T₀ t*B*T₀ u‖≤‖B‖ := (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((S).shrinks _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks _))))
-- can use any single-axis approximants with spatial motion on just continuous part for the convergence (not requiring mean-norm continuity for such).
lemma ModSpaces.starts (h:P.ModSpaces a A) (t:ℝ≥0) (w:0<t): SatinRegistration.Travels (fun i=>A.Wstage x a t t i):=by
 apply Flying.via; intro ε e
 obtain ⟨p,D,v,k⟩:= h.2 t w ε e
 let Y(i:ℕ):= P.cane x a (D x) (-(p i)); refine ⟨Y,(P.cane_flies x a v.neg (Flying.still (D x))).Cauchy,k.mono fun i k=>?_⟩
 let z:= A.Wstage x a t t i; let u:=p i; unfold Y
 have hp:P.cane x a (P.cane x a z u) (-u)=z:=by rw [P.cane_join,neg_add_cancel,P.cane_ofZero]
 rw [←dist_eq_norm]; change dist z _ ≤ _; rw [←hp]; exact (P.cane_distance x a (P.cane x a z u) (D x) (-u)).trans (k x) -- rw `z` let.

-- max bound convenient for ALL pose options (and all spectrum). Nest* quant max. use ℕ Filter here atTop.
lemma threshold_scoop (h:P.ThresholdPrice a A)(v:A.Finishes) (f g:ℝ) {p:Vantage}(hl:f<p a)(hr:p a<g): ∃ C≥(0:ℝ), ∀ (q:ℕ→Vantage)(σ:ℕ→ℕ), Tendsto q atTop (𝓝 p) → Tendsto σ atTop atTop → AllBills (fun x=>GOp x) atTop (fun i x=> A.scoop P x a f g (q i) (σ i)) C:=by
 let d:= (p a-f).toNNReal; let d':=(g-p a).toNNReal; let y:= min d d'/2; have hz:0< min d d':= lt_min (Real.toNNReal_pos.mpr (sub_pos.mpr hl)) (Real.toNNReal_pos.mpr (sub_pos.mpr hr)); have hy:y<d:=(half_lt_self hz).trans_le (min_le_left ..); have hx:y<d':=(half_lt_self hz).trans_le (min_le_right ..); have pz:0<y:=half_pos hz
 obtain ⟨C,h,Hx⟩:= h y pz; refine ⟨C,h,fun q σ t u=> ?_⟩
 have he:= tendsto_pi_nhds.mp t a; have ha:Tendsto (fun i=>Real.toNNReal (q i a-f)) atTop (𝓝 d):=continuous_real_toNNReal.continuousAt.tendsto.comp (he.sub_const f); have hb:Tendsto (fun i=>Real.toNNReal (g-q i a)) atTop (𝓝 d'):= continuous_real_toNNReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=g)).sub he)
 filter_upwards [ha.eventually (le_mem_nhds hy),hb.eventually (le_mem_nhds hx),u.eventually ((v a).eventually (ge_mem_nhds pz)),u.eventually Hx] with i a₁ b₁ u₁ R₁ x
 rw [A.precision P x a f g (q i) (σ i) y u₁ ((Real.le_toNNReal_iff_coe_le' pz).1 a₁) ((Real.le_toNNReal_iff_coe_le' pz).1 b₁)]
 exact (P.stoves_price x a _ _ _).trans ((P.cane_norm x a _ _).trans (R₁ x))
lemma stoves_paidOne  : ‖(1:(P.ManyF a (P.advocate 3 x a)).Op)‖ ≤ 1:=by rw [←show T₀ 0=1 from (S).eZero]; exact (S).shrinks 0 -- notation macro x binder? collision! _ local x from variable above with foreign binding shadow; remove explicit x, use section variables.
-- equivalence between tolerance using centered W with separated cut charges & actual Raw.
lemma scoop_progress (h:P.ThresholdPrice a A) (v:A.Finishes) (f g:ℝ) {p:Vantage}(s:ℝ≥0)(s0:0<s)(hl:(s:ℝ)<p a-f)(hr:(s:ℝ)<g-p a) (q:ℕ→Vantage)(σ:ℕ→ℕ)(t:Tendsto q atTop (𝓝 p))(u:Tendsto σ atTop atTop):
 Agrees atTop (fun i x=>A.scoop P x a f g (q i) (σ i)) (fun i x=> (Θ' x).E (τ (p a-f)-s)*P.cane x a (A.Wstage x a s s (σ i)) (q i)*(Θ' x).E (τ (g-p a)-s)):=by
 let d:= τ (p a-f); let d':=τ (g-p a); have hz:s<d:=by apply NNReal.coe_lt_coe.mp; rw [Real.coe_toNNReal _ (s.prop.trans hl.le)]; exact hl
 have hz':s<d':=by apply NNReal.coe_lt_coe.mp; rw [Real.coe_toNNReal _ (s.prop.trans hr.le)]; exact hr -- will rw d private let? dsimp only [d]
 let X(i):= Real.toNNReal (q i a-f); let Y(i):= Real.toNNReal (g-q i a); have hc:=tendsto_pi_nhds.mp t a; have hx:Tendsto X atTop (𝓝 d):= continuous_real_toNNReal.continuousAt.tendsto.comp (hc.sub_const f); have hy:Tendsto Y atTop (𝓝 d'):=continuous_real_toNNReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=g)).sub hc)
 let S'(x):=P.seasons a (Θ x a); let B(i:ℕ)(x):=P.cane x a (A.Wstage x a s s (σ i)) (q i)
 obtain ⟨C,pC,hC⟩:= h s s0; have hp:OnTab atTop (fun i x=>B i x):=⟨C,pC,(u.eventually hC).mono fun i h x=> (P.cane_norm ..).trans (h x)⟩
 let V₁(i:ℕ)(x):= (S' x).E (X i-s); let V₂(i:ℕ)(x):= (S' x).E (Y i-s)
 have ht: Agrees atTop V₁ (fun _ x=> (S' x).E (d-s)):=same_heat S' (tsub_pos_of_lt hz) (hx.sub_const s); have ht': Agrees atTop V₂ (fun _ x=> (S' x).E (d'-s)):=same_heat S' (tsub_pos_of_lt hz') (hy.sub_const s)
 refine (of_eq (Y:=V₁*B*V₂) (?_)).trans (((ht.prod (Agrees.refl B) (OnTab.keeps1 S' _) hp)).prod ht' ((OnTab.keeps1 S' (fun i=>X i-s)).prod hp) (OnTab.keeps1 S' _)) -- unification Tune
 filter_upwards [hx.eventually (le_mem_nhds hz),hy.eventually (le_mem_nhds hz'), u.eventually ((v a).eventually (ge_mem_nhds s0))] with i h v g₁; exact funext fun x=> A.precision P x a f g (q i) (σ i) s g₁ ((Real.le_toNNReal_iff_coe_le' s0).1 h) ((Real.le_toNNReal_iff_coe_le' s0).1 v)
lemma cane_special (u v:Vantage)(h:∀ b:Axis,b≠a → u b=v b)(A:(P.ManyF a (P.advocate 3 x a)).Op) : P.cane x a A u=P.cane x a A v:=by
 -- only space . cart_mates private, use definition
 have he:∀ u v:Vantage,(∀ b:Axis,b≠a → u b=v b) → pc u=pc v:=by
    intro p q t; refine congrArg ((P.voyageF a ξ).aviation _ _) (funext ?_); intro i; exact t i.val i.property
 unfold cane; rw [he _ _ h,he (-u) (-v) fun i t=>congrArg (fun x:ℝ=> -x) (h _ t)]
lemma clock_enough (u v:ℝ)(e:ℝ) (hl:u<e)(hr:e<v): ∃ s:ℝ≥0,0<s∧(s:ℝ)<e-u ∧ (s:ℝ)<v-e:=by
 let r:=min (e-u) (v-e); have he:0<r:=lt_min (sub_pos.mpr hl) (sub_pos.mpr hr); have ht:0<r/2:=half_pos he
 refine ⟨⟨_,ht.le⟩,ht,(half_lt_self he).trans_le (min_le_left ..),(half_lt_self he).trans_le (min_le_right ..)⟩
lemma move_time_ok (p0:P.ThresholdPrice a A)(v:A.Finishes)(f g:ℝ){p:Vantage}(h:f<p a)(t:p a<g){q q':ℕ→Vantage}{σ:ℕ→ℕ}(s:Tendsto σ atTop atTop)(l:Tendsto q atTop (𝓝 p))(r:Tendsto q' atTop (𝓝 p))(u:∀ᶠ i in atTop,∀ b:Axis,b≠a→ q i b=q' i b): Agrees atTop (fun i x=> A.scoop P x a f g (q i) (σ i)) (fun i x=> A.scoop P x a f g (q' i) (σ i)):=by
 obtain ⟨w,t',u',v'⟩:= clock_enough f g (p a) h t
 refine (P.scoop_progress a A p0 v f g w t' u' v' q σ l s).trans ((SatinRegistration.of_eq (?_)).trans ((P.scoop_progress a A p0 v f g w t' u' v' q' σ r s).symm))
 filter_upwards [u] with i w'; funext x; rw [P.cane_special x a _ _ w'] -- use funext & rw before ext clm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.move_time_ok
#print axioms Spine.scoop_progress
#print axioms Spine.threshold_scoop
#print axioms Spine.ModSpaces.starts
