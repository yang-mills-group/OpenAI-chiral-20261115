import YM.SU5.Registration.Affine.Entries
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
/-! # Fixed-cut overlap computations -/
abbrev cane (A:(G).Op)(p:Vantage) : (G).Op:= pc p * A * pc (-p)
lemma cane_scaled (B:(G).Op)(p:Vantage)(z:ℂ) : z • P.cane x a B p=P.cane x a (z • B) p:=by unfold cane; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
lemma cane_join (p r:Vantage)(A:(G).Op): P.cane x a (P.cane x a A r) p=P.cane x a A (p+r):=by
 have h(u v:Vantage): pc (u+v)=pc u*pc v:= P.cart_paves ..
 unfold cane; rw [h,show -(p+r)= -r+-p by abel,h]; simp only [mul_assoc]
lemma cane_time (b c:ℝ≥0)(A:(G).Op)(p:Vantage): T₀ b * P.cane x a A p * T₀ c=P.cane x a (T₀ b * A * T₀ c) p:=by
 have h(p:Vantage)(t:ℝ≥0): T₀ t * pc p= pc p * T₀ t:= by ext1 v; exact P.warm_drive ..
 unfold cane; simp only [mul_assoc]; rw [← h,← mul_assoc (T₀ b),h p b]; simp only [mul_assoc] -- tune
lemma cane_norm (A:(G).Op)(p:Vantage): ‖P.cane x a A p‖≤ ‖A‖:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (P.cart_pay ..)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (P.cart_pay ..))))
lemma cane_projection (B:(H).Op)(p:Vantage): P.cane x a (P.toStageG a ξ B) p=P.tableau a ξ p B:= by ext1 v; rfl
lemma cane_adjoint (A:(G).Op)(p:Vantage): (P.cane x a A p).adjoint = P.cane x a A.adjoint p:=by unfold cane; rw [←ContinuousLinearMap.star_eq_adjoint,star_mul,star_mul]; simp only [ContinuousLinearMap.star_eq_adjoint,P.cart_reverses,neg_neg,mul_assoc]
lemma cart_aims {p:ℕ→Vantage}{q:Vantage}(h:Tendsto p atTop (𝓝 q)): Flying (fun i=> pc (p i)) (pc q):=by
 intro v; refine ⟨((P.cart_cont ..).tendsto _).comp h,?_⟩
 simp only [P.cart_reverses]; exact ((P.cart_cont ..).tendsto _).comp h.neg
lemma cane_flies {p:ℕ→Vantage}{q:Vantage}(h:Tendsto p atTop (𝓝 q)){U:ℕ→(G).Op}{A:(G).Op}(v:Flying U A): Flying (fun i=> P.cane x a (U i) (p i)) (P.cane x a A q) := ((P.cart_aims x a h).multiply v).multiply (P.cart_aims x a h.neg)

-- positivity slack cut. Ray points can have coincidences in OTHER axes in this purchase; price only inside one chronological chart. For real Eu use exactly Serenity time-axis. Need no spatial cone for any such cut.
local notation "τ" p:max=>Real.toNNReal (p:ℝ)
def Swatch.scoop (A:P.Swatch)(l r:ℝ)(p:Vantage)(i:ℕ): (G).Op:= A.rate i • P.pillar a ξ (A.fieldA i) l r p
lemma Swatch.scoop_reads (A:P.Swatch)(l r:ℝ)(p:Vantage)(i:ℕ)(h:l≤p a)(t:p a≤r): A.scoop P x a l r p i=P.cane x a (A.Wstage x a (τ (p a-l)) (τ (r-p a)) i) p :=by
 let B:=A.fieldA i; let b:= B.allowance P a
 let s:=p a-l; let u:=r-p a;
 let w:= Real.toNNReal; have he (s:ℝ)(h:0≤ s): w s-b=w (s-b):= by unfold w; rw [NNReal.sub_def, Real.coe_toNNReal s h]
 let L:= τ (s-b); let R:=τ (u-b); let X:= P.toStageG a ξ (B.engine P a ξ)
 rw [Swatch.Wstage,← cane_scaled]; unfold Swatch.scoop; congr 1
 unfold pillar stageG stageH; rw [P.bank_both]
 let f:=Apron.time_panel P a p (A.fieldA i); let g:=Apron.time_edge P a p (A.fieldA i)
 change T₀ (Real.toNNReal (f-l)) * (P.tableau a ξ p (B.engine P a ξ) * T₀ (Real.toNNReal (r-g)))=P.cane x a (T₀ (w s-b)*X*T₀ (w u-b)) p
 rw [he s (sub_nonneg.mpr h),he u (sub_nonneg.mpr t),← P.cane_time,←mul_assoc,show f-l=s-b from ?_,show r-g=u-b from ?_,← P.cane_projection]; try rfl
 swap
 · unfold s b B f Apron.time_panel; rw [Apron.width_real]; abel
 unfold u b B g Apron.time_edge; rw [Apron.width_real]; abel
lemma Swatch.precision (A:P.Swatch)(l r:ℝ)(p:Vantage)(i:ℕ)(w:ℝ≥0)(h:(A.fieldA i).allowance P a ≤ w)(t:(w:ℝ)≤p a-l)(u:(w:ℝ)≤ r-p a): A.scoop P x a l r p i= (T₀ (τ (p a-l)-w))*P.cane x a (A.Wstage x a w w i) p * T₀ (τ (r-p a)-w):=by
 rw [A.scoop_reads P x a l r p i (sub_nonneg.mp (w.prop.trans t)) (sub_nonneg.mp (w.prop.trans u)), A.Wstage_more x a i h (NNReal.le_toNNReal_of_coe_le t) h (NNReal.le_toNNReal_of_coe_le u),P.cane_time] -- name h tune.

-- now the moment cut, limit, definition at cuts + portability
open Swatch
def orbitCut (A:ℝ≥0→(P.ManyF a (P.advocate 3 x a)).Op)(l r:ℝ)(p:Vantage) : (G).Op:= P.cane x a (bothPads S A (τ (p a-l)) (τ (r-p a))) p
abbrev Swatch.WPermit.sees {A:P.Swatch}(h:A.WPermit x a)(l r:ℝ)(p:Vantage): (G).Op:= P.orbitCut x a h.atHeat l r p
lemma Swatch.WPermit.pose {l r:ℝ}{p:Vantage}(b:ℕ→Vantage)(hl:l<p a)(hr:p a<r)(t:Tendsto b atTop (𝓝 p)){A:P.Swatch}(h:A.WPermit x a): Flying (fun i=> A.scoop P x a l r (b i) i) (h.sees P x a l r p):=by
 let s:=p a-l; let u:=r-p a; have hv:= tendsto_pi_nhds.mp t a; let X(i:ℕ):=Real.toNNReal ((b i) a-l); let Y(i:ℕ):=Real.toNNReal (r-(b i) a)
 have hx:Tendsto X atTop (𝓝 (τ s)):= continuous_real_toNNReal.continuousAt.tendsto.comp (hv.sub_const l)
 have hy:Tendsto Y atTop (𝓝 (τ u)):= continuous_real_toNNReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=r)).sub hv)
 apply Flying.late (P.cane_flies x a t (h.stage_limit (Real.toNNReal_pos.mpr (sub_pos.mpr hl)) (Real.toNNReal_pos.mpr (sub_pos.mpr hr)) hx hy))
 filter_upwards [hv.eventually (le_mem_nhds hl),hv.eventually (ge_mem_nhds hr)] with i a b -- b collision
 exact (A.scoop_reads P x _ l r _ i a b).symm -- tune
lemma orbitCut_precise (A:ℝ≥0→(P.ManyF a (P.advocate 3 x a)).Op)(h:SatinRegistration.Sound (P.seasons a (P.advocate 3 x a)) A)(l r:ℝ)(p:Vantage)(s:ℝ≥0)(v:0<s)(x':s ≤ Real.toNNReal (p a-l))(y:s ≤ Real.toNNReal (r-p a)): P.orbitCut x a A l r p=T₀ (τ (p a-l)-s)*P.cane x a (A s) p*T₀ (τ (r-p a)-s):=by unfold orbitCut; rw [arbitrary_pad _ _ v x' y h, cane_time]
lemma orbitCut_flies (A:ℝ≥0→(P.ManyF a (P.advocate 3 x a)).Op)(h:SatinRegistration.Sound S A){p:ℕ→Vantage}{w:Vantage}(t:Tendsto p atTop (𝓝 w)){r s:ℝ}(hl:r<w a)(hr:w a<s): Flying (fun i=> P.orbitCut x a A r s (p i)) (P.orbitCut x a A r s w):=by
 let d:= τ (w a-r); let d':=τ (s-w a); have hv:=tendsto_pi_nhds.mp t a; let X(i:ℕ):= Real.toNNReal (p i a-r); let Y(i:ℕ):=Real.toNNReal (s-p i a); have hx:Tendsto X atTop (𝓝 d):= continuous_real_toNNReal.continuousAt.tendsto.comp (hv.sub_const r); have hy:Tendsto Y atTop (𝓝 d'):= continuous_real_toNNReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=s)).sub hv)
 let z:= min d d'/2; have hp:0< min d d':= lt_min (Real.toNNReal_pos.mpr (sub_pos.mpr hl)) (Real.toNNReal_pos.mpr (sub_pos.mpr hr)); have hz:z<d:= (half_lt_self hp).trans_le (min_le_left ..); have hz':z<d':=(half_lt_self hp).trans_le (min_le_right ..); have z0:0<z:=half_pos hp
 rw [P.orbitCut_precise x a A h r s w z z0 hz.le hz'.le]
 apply Flying.late (((Flying.heat S (hx.sub_const z)).multiply (P.cane_flies x a t (Flying.still (A z)))).multiply (Flying.heat S (hy.sub_const z)))
 filter_upwards [hx.eventually (le_mem_nhds hz),hy.eventually (le_mem_nhds hz')] with i c v
 exact (P.orbitCut_precise x a A h r s (p i) z z0 c v).symm
lemma turn_cut (A:P.Swatch)(l r:ℝ)(p:Vantage)(h:A.WPermit x a) : (h.reflector x a A).sees P x a (-r) (-l) (opposeR a p) = (h.sees P x a l r p).adjoint:= by
 let v:=(p a-l).toNNReal; let t:=(r-p a).toNNReal
 unfold WPermit.sees orbitCut; rw [P.cane_adjoint]; rw [show opposeR a p a- -r=r-p a from ?_,show -l-opposeR a p a=p a-l from ?_]; swap
 · rw [show opposeR a p a = -p a from if_pos rfl]; abel
 swap; · rw [show opposeR a p a = -p a from if_pos rfl]; abel
 let B:=h.atBoth v t
 change P.cane x a ((h.reflector x a A).atBoth t v) (opposeR a p)= P.cane x a B.adjoint p
 rw [h.atBoth_turn]; unfold cane opposeR; simp only [← mirrorΩ_neg,P.cart_mirror]; try rfl

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
