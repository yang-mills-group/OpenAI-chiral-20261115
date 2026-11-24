import YM.SU5.Cordial.Scepter
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
/-! # Hankel estimates repay marginal continuity inside this UV resolution.
 No passage to different study/vacuum data! Lift through other axes on this observation.
 Strict separation using actual SUPPORT at its stencil; no need diagonal limit to get this. -/
open OS.Semigroup (F)
open OS.Semigroup.Balloon
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "κ" => P.calibration
local notation "B" => P.par.block
local notation "M" => timeMesh P.par
local notation "Γ" => marks M
local notation "N₀" => notch M
local notation "ε" => YM.basis (3:Axis)
local notation "ι" => k.val
local notation "ℓ" => P.calibration.ℓ
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.physicalEnergy 3 (β)
local notation "V" => P.ColorHil 3 (β)
local notation "χ" => P.otherSpectrum 3 k.val (β)
local notation "W" => P.ColorHil (ι) (χ)
local notation "Λ" => P.physicalEnergy (ι) (χ)
local notation "Ψ" => P.voyageF 3 (β)
local notation "y" s:max i:max=> P.shard x Z s i
local notation "U" => (Ψ).crew k
local notation "P₁" i:max n:max => P.shifts k.val i (P.stockS Z (P.flash n))
local notation "P₂" i:max n:max => P.reflectTest k.val (P.reflectTest 3 (P₁ (-i) n))
def beamCut (u:Γ)(b:ℤ):Γ:= u-(N₀ s b+ N₀ s b)
def viewer (u:Γ)(n:ℕ):= inner ℂ (P.shard x Z s n) ((U).play u (P.shard x Z s n))
lemma view_cut (u:Γ)(t:ℤ)(v:0≤(P.beamCut s u t:ℝ))(n:ℕ)(p:P.birthF k.val s (P₁ t n))(w:P.birthF k.val s (P₂ t n)):
 P.viewer x Z k s u n=inner ℂ (P.viewF k.val (χ) s w) ((Λ).E (Real.toNNReal (P.beamCut s u t:ℝ)) (P.viewF k.val (χ) s p)):=by
 let a:=P.beamCut s u t; let b:=N₀ s t; exact (congrArg (fun z=> P.viewer x Z k s z n) (show u=a+(b+b) from (sub_add_cancel ..).symm)).trans (P.marginal x Z k s a v t n p w)
lemma kept_margin (u:Γ)(t:ℤ)(v:0<(P.beamCut s u t:ℝ))(n:ℕ)(p:P.birthF k.val s (P₁ t n))(w:P.birthF k.val s (P₂ t n)):
 inner ℂ (P.shard x Z s n) ((U).play u ((U).pi_c (P.shard x Z s n)))= P.viewer x Z k s u n:=by
 let f:= innerSL ℂ (P.shard x Z s n); let g(z:Γ):ℝ:= P.beamCut s z t; have hg:Continuous g:=by unfold g beamCut; fun_prop
 let P'(z:Γ):= inner ℂ (P.viewF k.val (χ) s w) ((Λ).E (g z).toNNReal (P.viewF k.val (χ) s p)); have HP:Continuous P':= continuous_const.inner ((Λ).continuousE _|>.comp (continuous_real_toNNReal.comp hg))
 have ht:ContinuousAt (fun i=>f ((U).play i (P.shard x Z s n))) u:= HP.continuousAt.congr ((hg.continuousAt.tendsto.eventually (le_mem_nhds v)).mono fun i h=>(P.view_cut x Z k s i t h n p w).symm)
 exact (U).retains_at f (P.shard x Z s n) u ht
-- notational currency small results
variable {P x c r}
variable (A:Launch P c r) {d:ℕ→ℝ} (Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
local notation "Φ" i:max=> (y (c i) (r i))
local notation "ρ" i:max=> P.dew (c i) (r i)
local notation "π"=> (U).pi_c
local notation "ν" u:max i:max => (P.viewer x Z k (c i) u (r i))
variable (P) (c r) (δ τ : ℕ → marks (timeMesh P.par)) (u:ℝ)
def attendsSky : Prop:= Tendsto (fun i=>((δ i):ℝ)/ρ i) atTop (𝓝 u)
variable {P c r u}
include A
private abbrev drift (t:ℕ→ℤ)(r:ℕ):Γ:=P.beamCut (c r) (δ r) (t r)
lemma aboutTurn {b:ℕ→ℤ}(t:0<u)(v:P.bargain r b (u/3))(w:P.attendsSky c r δ u):
 Tendsto (fun i=> ((drift (P:=P) (c:=c) δ b i:Γ):ℝ)/(ρ i)) atTop (𝓝 (u/3)) ∧ ∀ᶠ i:ℕ in atTop,0< (drift (P:=P) (c:=c) δ b i:ℝ):=by
 let f(i):= (drift (P:=P) (c:=c) δ b i:Γ); have ht :=P.priceV c r b (u/3) v A.unitSize; have he:= w.sub (ht.add ht); rw [show u-(u/3+u/3)=u/3 by ring] at he
 have hu:Tendsto (fun i=> ((f i):ℝ)/(ρ i)) atTop (𝓝 (u/3)):= he.congr fun i=> by simp only [f]; rw [drift, beamCut,AddSubgroup.coe_sub, AddSubgroup.coe_add,sub_div,_root_.add_div] -- reverse
 refine ⟨hu,(hu.eventually (lt_mem_nhds (by positivity : 0<u/3))).mono fun i g=> ?_⟩
 have hd:0<ρ i:= P.dew_pos _ (A.unitSize i); exact (by simpa only [zero_mul] using ((lt_div_iff₀ hd).mp g) : 0<((f i):ℝ))
include Y p
private abbrev midpoint (z:ℝ)(r:ℕ):ℤ:=P.roundingR r (z/3)
lemma persisted (h:P.attendsSky c r δ u)(t:0<u):∀ᶠ i in atTop, inner ℂ (Φ i) ((U).play (δ i) (π (Φ i)))=ν (δ i) i:=by
 let f(i):=P.roundingR (r i) (u/3); have he:P.bargain r f (u/3):= P.intendR r (u/3) A.eager
 let a:= seats_book Z k A Y p (show 0<u/3 by positivity) he; have hx:= a.choose_spec.2; filter_upwards [hx, (aboutTurn A δ t he h).2] with i w hi; exact P.kept_margin x Z k (c i) (δ i) (f i) hi (r i) w.1 w.2.1
lemma unity_point (p₁:P.attendsSky c r δ u)(p₂:P.attendsSky c r τ u)(t:0 < u): Tendsto (fun i=> ν (δ i) i- ν (τ i) i) atTop (𝓝 0):= by
 let f(i):=P.roundingR (r i) (u/3); have e:0<u/3:=by positivity
 have he:P.bargain r f (u/3):= P.intendR r (u/3) A.eager; let a := (seats_book Z k A Y p e he).choose; have hx:= (seats_book Z k A Y p e he).choose_spec; have hv:0<a:= hx.1
 have ha : ∀ i:ℕ,0<ρ i:= fun i=>P.dew_pos _ (A.unitSize i)
 let Q (t:ℕ→Γ)(i):ℝ:=P.beamCut (c i) (t i) (f i); let ClockF (t:ℕ→Γ)(i):ℝ≥0:= Real.toNNReal (Q t i); obtain ⟨hb,H⟩:= aboutTurn A δ t he p₁; obtain ⟨hc,U'⟩:= aboutTurn A τ t he p₂
 have ht (t:ℕ→Γ) (c':P.attendsSky c r t u) : Tendsto (fun i=> ( (ClockF t i:ℝ) / ρ i)) atTop (𝓝 (u/3)) := by
    obtain ⟨x,h⟩:= aboutTurn A t (show 0<u by assumption) he c'; exact x.congr' (h.mono fun i v=> (congrArg (· /ρ i) (Real.coe_toNNReal _ v.le)).symm)
 rw [tendsto_zero_iff_norm_tendsto_zero]; apply Metric.tendsto_nhds.mpr; intro z h
 have hq:0<z/2/a:=by positivity
 filter_upwards [hx.2,H,U', uniform_price Λ ha (ht δ p₁) (ht τ p₂) e a (z/2/a) hq] with i hu ht₀ hz hT
 let W₁:= P.viewF k.val (χ) (c i) hu.1; let W₂:= P.viewF k.val (χ) (c i) hu.2.1; let U₁:= (Λ).E (ClockF δ i) W₁-(Λ).E (ClockF τ i) W₁; have hb:‖W₂‖≤a:= hu.2.2.2 _; have hc:‖U₁‖≤ z/2/a:= hT W₁ (hu.2.2.1 _)
 have hh: ν (δ i) i - ν (τ i) i=inner ℂ W₂ U₁ := by
    exact (congrArg₂ (· - ·) (P.view_cut x Z k (c i) (δ i) _ ht₀.le (r i) hu.1 hu.2.1) (P.view_cut x Z k (c i) (τ i) _ hz.le (r i) hu.1 hu.2.1)).trans (inner_sub_right ..).symm
 simp only [Real.dist_eq,sub_zero,abs_norm,hh]; apply lt_of_le_of_lt (b:=z/2) _ (half_lt_self h); exact (norm_inner_le_norm _ _ |>.trans (mul_le_mul hb hc (norm_nonneg _) hv.le)).trans_eq ((mul_comm a _).trans (div_mul_cancel₀ (z/2) hv.ne'))
omit A Y p in
lemma unpaid_move : P.bargain r (fun _=>0) 0 := tendsto_const_nhds.congr fun i=> by simp [crewB,Heat.gaugeShift]
-- avoid rewriting operator equality at difficult instances
omit A Y p in
private lemma initialization (i:ℕ)(n:ℕ) : (S).E (whenly M (c i) 0) (y (c i) n)=(y (c i) n):=(congrArg (fun t:ℝ≥0=>(S).E t (y (c i) n)) (when_zero ..)).trans (DFunLike.congr_fun (S).eZero _)
omit A Y p in
private lemma initialization1 (i:ℕ)(D:ℤ)(n:ℕ): (Ψ).raw [k] (fun _=> N₀ (c i) D) (((S).E (whenly M (c i) 0)) (y (c i) n))= (U).play (N₀ (c i) D) (y (c i) n):=by
 let f:Street→Γ:=fun _=> N₀ (c i) D; exact (congrArg ((Ψ).raw [k] f) (initialization (x:=x) (c:=c) Z i n)).trans rfl
lemma pledge (D:ℕ→ℤ)(H:P.bargain r D u): Tendsto (fun i=> ν (N₀ (c i) (D i)) i) atTop (𝓝 (ovoid Z 0 (u • streak k))) := by
 have he:= penetration Z [k] A Y p (fun _=>0) 0 le_rfl (fun _ i=> D i) (fun _=>u) (fun _ _=>H) (unpaid_move (P:=P) (r:=r));
 have ht:palace [k] (fun _=>u)=u • streak k:= by rw [palace_one,show palace [] _=(0:Bank) from rfl,add_zero];
 let a:=ovoid Z 0 (palace [k] fun _=> u)
 let b:=ovoid Z 0 (u • streak k); have hh:a=b:=congrArg (ovoid Z 0) ht
 have hx:Tendsto (fun i=> ν (N₀ (c i) (D i)) i) atTop (𝓝 a):= he.congr fun i=> congrArg (inner ℂ (Φ i)) (initialization1 (c:=c) (x:=x) Z k i (D i) (r i))
 change Tendsto _ _ (𝓝 b); rw [←hh]; exact hx
lemma matchesM (p₁:P.attendsSky c r δ u)(t:0<u): Tendsto (fun i=> ν (δ i) i) atTop (𝓝 (ovoid Z 0 (u • streak k))) := by
 let F(i):= P.roundingR (r i) u; let g(i):Γ:= N₀ (c i) (F i); have he:=(P.intendR r u A.eager); have hp:P.attendsSky c r g u:=P.priceV c r F u he A.unitSize; let v:=unity_point Z k A Y p δ g p₁ hp t; have he:= v.add (pledge Z k A Y p F he); rw [zero_add] at he; exact he.congr fun i=> sub_add_cancel _ _
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.persisted
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.attendsSky
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.matchesM
