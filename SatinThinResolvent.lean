import SatinThinRadiant
import YM.SU5.Circuit.Concert
set_option maxHeartbeats 1050000
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
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/
variable {z A c:ℝ}




open Regis Head.Garland Head.Etch Lamour.Bridge Celeste Clock Hookah Hookah.Blaze

open Papal -- needed addgap namespace
set_option linter.unusedVariables false
-- probes fare template incumbent
variable (z:PlaqAxes→ℝ) {I:Type}[Fintype I]
local notation "xθ" s:max=>hat P.R.L P.x s
local notation "ρ" s:max=>Real.sqrt (hat P.R.L P.x s)
local notation "ℰ" s:max=> meterC (xθ s)
variable {A B b:ℝ} (E':Trip I)(K H:ℕ→ℕ) (P_ :Real.exp 1≤ P.x)
variable (a:ℝ)
variable {K H} {T:ℕ→Buffered.Family (tent Y P_)→ℕ→ℂ}{E:ℕ→ Buffered.Family (tent Y P_) →ℂ}(V:Universal Y P_ K H T E)
open Regis Circuit Head.Brecht
open YM.Stationary (Gaia)
-- Trips ready including aggregation geometry.
abbrev loneTrip (x:Cover)(s:Signed:=1):Trip Unit:=⟨fun _=>x,fun _=>s⟩
def tapeBoth {I J:Type}(T:Trip I)(V:Trip J):Trip (I⊕J):=⟨Sum.elim T.loc V.loc, Sum.elim T.orient V.orient⟩
abbrev twinTrip (x y:Cover)(s t:Signed:=1):Trip Bool:=⟨fun i=> if i then x else y,fun i=> if i then s else t⟩
lemma twin_ok(x y:Cover)(s t:Signed): (twinTrip x y s t).tryN n=zipBoth (wrap n x) (wrap n y) s t:= by unfold Trip.tryN twinTrip zipBoth; congr 1; funext i; cases i<;> rfl
lemma twin_book (x y:Cover)(s t:Signed)(u:ℝ)(n:Side): (twinTrip x y s t).issued z u n=(loneTrip x s).issued z u n*(loneTrip y t).issued z u n:=by funext Y; unfold Trip.issued pension; rw [twin_ok]; dsimp only [Hookah.chalkOp]; unfold Hookah.Blaze.silk; simp only [Fintype.prod_bool, Fintype.prod_unique,zipBoth,↓reduceIte,Bool.false_eq_true, Pi.mul_apply]; push_cast; rw [mul_smul]; simp_rw [Algebra.smul_mul_assoc, one_mul]; rfl -- tune
lemma twin_mem_left(x y:Cover)(s t:Signed): (loneTrip x s).canvasC ⊆ (twinTrip x y s t).canvasC:=by intro i h; refine (twinTrip x y s t).touchedC true (?_); obtain ⟨j,q,v⟩:= mem_biUnion.mp h; exact v
lemma twin_mem_right(x y:Cover)(s t:Signed): (loneTrip y t).canvasC ⊆ (twinTrip x y s t).canvasC:=by intro i h; apply (twinTrip x y s t).touchedC false; obtain ⟨j,q,v⟩:= mem_biUnion.mp h; exact v
open BProof
variable {R:ℕ→ℝ}{x y:ℕ→ Cover}{w:Gaia}(p:∀ i,0<R i)(zR:Tendsto R atTop atTop)(hv:Tendsto (fun i:ℕ=>Onyx.riseX (R i) (x i-y i)) atTop (𝓝 w))(hw:w≠0) (k:Tendsto (fun i:ℕ=> R i^8/trailℓ A (hat P.R.L P.x i)) atTop (𝓝 0))
local notation "Tr"=>twinTrip
local notation "τZ"=> P.K.top.clip
local notation "B₀"=>spectrumℓ z SU.group w
local notation "Πz"=> (meritG z)^2 * tollK τZ SU.group -- tune namespace
local notation "dθ" s:max=> trailℓ A (xθ s)
open Cliplet
include V
abbrev paperN := meritG z * glamourK P.K.top.clip SU.group -- P accessible? autoLean
omit V in
lemma paperN_pos (P:Preparation):0≤paperN (P:=P) z:=by unfold paperN glamourK meritG; positivity -- namespace
lemma lift_priceZ (s:ℕ)(x:Cover) : |ultimate Y z (loneTrip x) K H a s| ≤ paperN (P:=P) z:=by
 refine le_of_tendsto (ultimate_guess Y z (loneTrip x) K H a s).2.abs (Eventually.of_forall fun i=>?_);
 apply le_of_tendsto (scribe_here Y z (loneTrip x) H a s (K i)).2.abs
 apply Nat.hyperfilter_le_atTop; filter_upwards [V.pick.grow_k.tendsto_atTop.eventually (ferry_later Y s (K i))] with j h;
 let u:=overlay Y s (K i) (H j); let k:=trailℓ a (xθ s); let v:=V; let N:=More (count Y s (K i)); let L:= P.V.L; let F:=Y.uv (H j)-s;
 change |singleV (L.mood F) (L.tied F) z u (coin_pos (xθ s) 0 a 0) (wrap N x)|≤_
 apply single_tariff; have ht:= actual_span Y s (K i) (H j); unfold u; rw [afforded Y s (((Real.exp_pos 1).trans_le P_).trans_le (Vale.crown P.R.L P.x s)) _ _ h.enters,abs_of_pos]; exacts [ht.2, ((by norm_num : (0:ℝ)<1/2).trans_le ht.1)]
omit V
private lemma lean_flux {P Q:ℂ}{f g h d:ℕ→ℝ}{x y z w:ℝ}(B:Tendsto f sceneL (𝓝 x))(G₁:Tendsto g sceneL (𝓝 y))(H:Tendsto h sceneL (𝓝 z))(D:Tendsto d sceneL (𝓝 w)): Tendsto (fun i=> ‖Horo P Q (f i) (g i) (h i) (d i)‖) sceneL (𝓝 ‖Horo P Q x y z w‖):= Filter.Tendsto.norm (((Complex.continuous_ofReal.continuousAt.tendsto.comp (B.sub (G₁.mul H))).const_mul P).sub (((Complex.continuous_ofReal.continuousAt.tendsto.comp D).pow 4).mul_const Q)) -- from Papal
include k p zR hv hw V P_
-- budget overlay not quotient; normalization same character
lemma mPowered (ε:ℝ) (u:0<ε) : ∀ᶠ s in atTop, let b':ℂ:= (R s:ℂ)^8; let μ:= ultimate Y z (Tr (x s) (y s)) K H A s; let w:= ultimate Y z (loneTrip (x s)) K H A s;
           ‖Horo b' B₀ μ w (ultimate Y z (loneTrip (y s)) K H A s) (Aster Y K H s)‖ ≤ ε :=by
 have he:= k.const_mul (Πz); rw [mul_zero] at he; let K':= P.K; let V':= P.V
 filter_upwards [he.eventually (ge_mem_nhds (show (0:ℝ)< ε/2 by positivity)), radial_rate τZ V'.W.parcel K'.width (zero_lt_one.trans_le V'.up) p zR hv hw z (ε/32) (by positivity) SU.group] with s ht hz b' μ w'
 let X:= x s; let Y':= y s; let d:=Tr X Y'; let f:=loneTrip X; let T:=loneTrip Y'; let W:=loneTrip Y'
 apply le_of_tendsto (lean_flux (P:=b') (Q:=B₀) (ultimate_guess Y z d K H A s).2 (ultimate_guess Y z f K H A s).2 (ultimate_guess Y z W K H A s).2 (astral Y K H s).2)
 apply Nat.hyperfilter_le_atTop; filter_upwards [((count_la Y s).comp V.pick.grow_i.tendsto_atTop).eventually hz] with i e
 apply le_of_tendsto (lean_flux (P:=b') (Q:=B₀) (scribe_here Y z d H A s (K i)).2 (scribe_here Y z f H A s (K i)).2 (scribe_here Y z W H A s (K i)).2 (tint_height Y H s (K i)).2);
 apply Nat.hyperfilter_le_atTop; filter_upwards [V.pick.grow_k.tendsto_atTop.eventually (ferry_later Y s (K i))] with j v
 let L:=P.V.L; let t:=overlay Y s (K i) (H j); let N':=count Y s (K i); let N:=More N'; let F:=Y.uv (H j)-s; let Z:=L.H F; let X₀:=wrap N X; let Y₀:=wrap N Y';
 let σ:ℝ:=bothV (L.mood F) (L.tied F) z t (trainℓ A (xθ s)) X₀ Y₀; let γx:= loftCall Y z f A s (K i) (H j); let γy:= loftCall Y z W A s (K i) (H j)
 have hp : Even N.val:= by unfold N; exact ⟨N'.val,by change N'.val*2=_; omega⟩ -- tune
 have hF:= L.roof F; have hg:= (afforded Y s (((Real.exp_pos 1).trans_le P_).trans_le (Vale.crown P.R.L P.x s)) (K i) (H j) v.enters).symm; change actual Y s (K i) (H j)=t at hg; have hx:= actual_span Y s (K i) (H j); rw [hg] at hx; have hZ : |t|≤2:= by rw [abs_of_pos ((by norm_num : (0:ℝ)<1/2).trans_le hx.1)]; exact hx.2
 have hb: ‖b' * Starℓ z X Y' SU.group Z N-(B₀:ℂ)‖ ≤ ε/32:=by rw [← dist_eq_norm]; exact e Z hF.1 (hF.2.1 _)
 let A':=(t:ℂ)^4; let W':=Starℓ z X Y' SU.group Z N; let q:ℂ:= ((σ-γx*γy:ℝ):ℂ); have hq: ‖q-A'*W'‖≤ (meritG z)^2 * (tollK (τZ) SU.group/(dθ s)):=by
    exact assigned _ _ (hF.2.1 N) hF.1 K'.width z t (trainℓ A _) X₀ Y₀ hp hZ -- cp
 have h0: ‖b'‖=R s^8:=by unfold b'; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg (p s).le]
 have hl : ‖A'‖ ≤ 16:=by unfold A'; rw [norm_pow,Complex.norm_real,Real.norm_eq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hZ _).trans_eq (by norm_num)
 change ‖Horo _ _ (loftCall Y z (Tr X Y') A s (K i) (H j)) γx γy _‖ ≤ _; rw [hg,show loftCall Y z (Tr X Y') A s (K i) (H j)=σ from (?_)]
 · change ‖b'*q-A'* B₀‖≤ε; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (A'*(b'*W')) _); refine le_trans (add_le_add (?_:‖b' * q-A'*(b'*W')‖≤ ε/2) (?_:‖A'*(b'*W')-A'*B₀‖≤ ε/2)) (by linarith only [u]); swap
   · rw [← mul_sub, norm_mul]; refine (mul_le_mul hl hb (norm_nonneg _) (by norm_num)).trans_eq ?_; ring
   rw [mul_left_comm A',←mul_sub,norm_mul,h0]; refine (mul_le_mul_of_nonneg_left hq (by have ht:= p s; positivity : 0≤R s^8)).trans (ht.trans' ?_); apply le_of_eq; ring
 unfold loftCall; rw [twin_ok]; rfl
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.mPowered
