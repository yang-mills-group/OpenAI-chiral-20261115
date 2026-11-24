import YM.SU5.Cordial.Neighbor
import YM.SU5.Cordial.Spritz
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
-- along whole canonical spatial space. ensemble costs hold
local notation "Φ" i:max=> (y (c i) (r i))
local notation "ρ" i:max=> P.dew (c i) (r i)
local notation "π"=> (U).pi_c
local notation "G"=>P.ManyF 3 (β)
local notation "Ψ'"=>P.seasons 3 (β)
local notation "π'"=>P.wealth 3 (β)
local notation "λ'"=>P.enter 3 (β)
local notation "φ" i:max=> P.lucid x Z (c i) (r i)
/-! # Together in any Euclidean position (zoom R). Equality of asymptotics after
 unaliasing. Applies to sequences as well for zoom-heights. -/
abbrev pan (p:Bank) (n:ℕ) : Street→ℤ:= fun i=> P.roundingR (r n) (reveal i p)
abbrev pit (p:Bank) (n:ℕ) : Street→Γ:= fun i=> N₀ (c n) (P.pan r p n i)
abbrev dimensionS (A: ℕ→ℝ≥0) (t:ℝ) : Prop:= Tendsto (fun i=>(A i:ℝ)/(ρ i)) atTop (𝓝 t)
abbrev horizon (p:Bank)(n:ℕ):= P.mountain (P.pit c r p n)
private lemma light_repay (X Y: V) : inner ℂ ((π') X) ((π') Y)= inner ℂ (P.visitors 3 (β) X) Y:= by
 let g:= P.visitors 3 (β); change inner ℂ (g X) (g Y) = _; let D:=P.Viewers 3 (β);
 -- use adj formula but expensive
 have hc: g.adjoint=g:=Alliance.symmetricstack ..; have he: g (g X)=g X:=Alliance.grounded _ _ ((Ψ).planted (look 3) X); exact (ContinuousLinearMap.adjoint_inner_left g Y (g X)).symm.trans (congrArg (inner ℂ · Y) ((DFunLike.congr_fun hc _).trans he))
variable {P x r c}(A:Launch P c r){d:ℕ→ℝ}(Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
local notation "Δ"=>ovoid Z 0 0
-- characterize Laplace transform of spatial
include A Y p
private lemma shard_bill : Limited V (fun i=> Φ i):= OS.Semigroup.Balloon.hasLimit (H:=V) (horn_norm Z A Y p) -- name
private lemma lucid_bill : Limited G (fun i=>φ i):= by
 obtain ⟨k,h⟩:=shard_bill Z A Y p
 exact ⟨k,h.mono fun i v=> le_trans (P.bank_cost 3 (β) (Φ i)) v⟩
private lemma highBeam (v:Bank) {z:ℝ}(q:0≤z)(D:ℕ→ℕ)(w:P.bargain r (fun i=>(D i:ℤ)) z): let T i:= whenly M (c i) (D i); Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (P.horizon c r v i) ((Ψ').E (T i) (φ i)))) atTop (𝓝 (ovoid Z z v)):=by
 let g(i:Street):=v.val i.val; let f(i:Street)(n:ℕ):=P.pan r v n i; let X(i):=P.pit c r v i; let ZK(n):= φ n
 let SP:= Ψ'; let J:= look (3:Axis); intro T
 have h : ∀ i:Street,P.bargain r (f i) (g i):=fun i=> P.intendR r (g i) A.eager
 let qX (i:ℕ):=(Ψ).raw J (X i) ((S).E (T i) (Φ i))
 let Hc(z):= ovoid Z z (palace J g)
 have he:Tendsto (fun i=>inner ℂ (Φ i) (qX i)) atTop (𝓝 (ovoid Z z v)):= by have he:Tendsto _ _ (𝓝 (Hc z)):= penetration Z J A Y p D z q (fun i n => f i n) g (fun i _=>h i) w; have ht:Hc z=ovoid Z z v:= congrArg (ovoid Z z) (palace_exact v); exact ht ▸ he
 have hh(i:ℕ): SP.U (P.horizon c r v i) (SP.E (T i) (ZK i))= (π') (qX i):= by
    have ht:= P.bankHeat 3 (β) (T i) (Φ i); exact (congrArg (SP.U (P.horizon c r v i) : (P.ManyF 3 (β)).space → _) ht.symm).trans (P.roll_motion 3 (β) (P.pit c r v i) ((S).E (T i) (Φ i)))
 let K:=P.visitors 3 (β); have hp: Limited (V) qX:= le_seam (fun i=> Φ i) (shard_bill Z A Y p) (fun i=> ((Ψ).raw_isometry J (X i) ((S).E (T i) (Φ i))).le.trans (heatedLim (S) (T i) (Φ i)))
 have hv:Tendsto (fun i=> inner ℂ (K (Φ i)) (qX i) - inner ℂ (Φ i) (qX i)) atTop (𝓝 0):=(aura' V qX _ hp (whole_sky Z A Y p)).congr fun i=> inner_sub_left (𝕜:=ℂ) (K (Φ i)) (Φ i) (qX i)
 exact (unifier hv he).congr fun i=> ((congrArg (inner ℂ (ZK i)) (hh i)).trans (P.light_repay x (Φ i) (qX i))).symm
lemma rays (v:Bank) {z:ℝ} (q:0≤z)(D:ℕ→ℕ)(w:P.bargain r (fun i=>(D i:ℤ)) z)(F:ℕ→ Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)) : Tendsto (fun i=>inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (whenly M (c i) (D i)) (φ i)))) atTop (𝓝 (ovoid Z z v)):= by
 let t(i):=whenly M (c i) (D i); let x' (i:ℕ):= φ i; let B' := Ψ'; let g:=P.horizon c r v; let E i:= B'.E (t i) (x' i);
 have he:=highBeam Z A Y p v q D w; have hv: Tendsto (fun i=> B'.U (F i) (x' i)- B'.U (g i) (x' i)) atTop (𝓝 0):= neighbor Z A Y p v (P.pan r v) F (fun i=> P.intendR r (reveal i v) A.eager) h
 have hw:Tendsto (fun i=> inner ℂ (x' i) (B'.U (F i) (E i))- inner ℂ (x' i) (B'.U (g i) (E i))) atTop (𝓝 0):= (aura G x' _ (lucid_bill Z A Y p) (realize_shim (Ψ') x' t F g hv)).congr fun i=> inner_sub_right (𝕜:=ℂ) (x' i) (B'.U (F i) (E i)) (B'.U (g i) (E i))
 exact unifier hw he
omit Y p in
lemma grantR (t:ℝ)(h:0 ≤ t):∃ D:ℕ→ℕ, P.bargain r (fun i=>(D i:ℤ)) t ∧ P.dimensionS c r (fun i=> whenly M (c i) (D i)) t:=by
 have hv(i:ℕ): 0 ≤ P.roundingR (r i) t:= Int.floor_nonneg.mpr (by positivity)
 let U₁(i):=P.roundingR (r i) t; let D(i):= (U₁ i).toNat; have he:P.bargain r (fun i=>(D i:ℤ)) t:=(P.intendR r t A.eager).congr fun i=> by dsimp only; rw [show (D i:ℤ)=_ from Int.toNat_of_nonneg (hv i)]
 exact ⟨D,he, (P.priceV c r _ t he A.unitSize).congr fun i=> congrArg (· / ρ i) (natural_time M (c i) (D i))⟩
private lemma evenlater (v:Bank) {z:ℝ}(q:0<z) (E:ℕ→ℝ≥0)(w:P.dimensionS c r E z)(F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)):
 Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (E i) (φ i)))) atTop (𝓝 (ovoid Z z v)) := by
 let T:= Ψ'; let v'(i:ℕ):= φ i; let D:=(grantR A z q.le).choose; have he:= (grantR A z q.le).choose_spec; let L(i:ℕ):= whenly M (c i) (D i); let Z'(i:ℕ):= T.E (E i) (v' i); let G'(i:ℕ):= T.E (L i) (v' i)
 have hx:Tendsto (fun i=> T.U (F i) (Z' i) - T.U (F i) (G' i)) atTop (𝓝 0):= (soarE T F _ (uniform_zoom T v' (fun i=> P.dew_pos _ (A.unitSize i)) w he.2 q (lucid_bill Z A Y p))).congr fun i=> map_sub (T.U (F i)) (Z' i) (G' i)
 let f(i):=inner ℂ (v' i) (T.U (F i) (Z' i)); let g(i):=inner ℂ (v' i) (T.U (F i) (G' i)); have hh:Tendsto (fun i=> f i - g i) atTop (𝓝 0):= (aura G v' _ (lucid_bill Z A Y p) hx).congr fun i=> inner_sub_right (𝕜:=ℂ) (v' i) (T.U (F i) (Z' i)) (T.U (F i) (G' i))
 exact unifier hh (rays Z A Y p v q.le D he.1 F h)
lemma initialPoint (v:Bank)(F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)): Tendsto (fun i=>inner ℂ (φ i) ((Ψ').U (F i) (φ i))) atTop (𝓝 (ovoid Z 0 v)):= by
 let x' (i:ℕ):= φ i; let T:= Ψ'; let g(i:ℕ):=T.E (whenly M (c i) 0) (x' i); have he(i:ℕ):g i=x' i:= (congrArg (fun t=> T.E t (x' i)) (when_zero ..)).trans (DFunLike.congr_fun T.eZero _)
 exact (rays Z A Y p v le_rfl (fun i=>0) (unpaid_move (P:=P)) F h).congr fun i=> congrArg (inner ℂ (x' i) ∘ T.U (F i)) (he i) -- coercion
lemma eyes_norm : Tendsto (fun i=> ‖(φ i)‖^2) atTop (𝓝 (Δ).re):=by
 let v(i:ℕ):= φ i; have h:Tendsto (fun i=> (ρ i)⁻¹ • (0:Bank)) atTop (𝓝 0):= tendsto_const_nhds.congr fun i=> (smul_zero ..).symm
 have he:=Complex.continuous_re.continuousAt.tendsto.comp (initialPoint Z A Y p 0 (fun _=>0) h); have hv(i): (Ψ').U 0 (v i)=v i:= DFunLike.congr_fun (Ψ').uZero _; exact he.congr fun i=> (congrArg (fun x:G=> (inner ℂ (v i) x).re) (hv i)).trans (inner_self_eq_norm_sq (𝕜:=ℂ) _)
omit A Y p in
private lemma eye_cont : ContinuousAt (fun t=>ovoid Z t 0) (0:ℝ):=by
 have he(n:ℝ)(h:0<n): ContinuousAt (fun t=>plume (t+n) 0) (0:ℝ):=by
    unfold Cordial.plume pearly; fun_prop (disch:= positivity)
 unfold ovoid; exact continuousAt_const.add (continuousAt_const.mul ((he 2 (by norm_num)).mul (he 4 (by norm_num))))
private lemma shrinkage (E:ℕ→ℝ≥0)(h:P.dimensionS c r E 0) : Tendsto (fun i=> (Ψ').E (E i) (φ i)- (φ i)) atTop (𝓝 0):=by
 let v(i:ℕ):= φ i; let T':= Ψ'
 apply tiny (Ψ') (F:=fun t:ℝ=>ovoid Z t 0) _ (eye_cont Z) (eyes_norm Z A Y p) _ E h
 · exact fun i=> P.dew_pos _ (A.unitSize i)
 intro s t; let q:=(grantR A s t.le).choose; have ht:=(grantR A s t.le).choose_spec; let F(i):=whenly M (c i) (q i); let g(i):= T'.E (F i) (v i); have hg(i): T'.U 0 (g i)=g i:= DFunLike.congr_fun T'.uZero _; refine ⟨F,ht.2,?_⟩
 have he:Tendsto (fun i=> (ρ i)⁻¹ • (0:Bank)) atTop (𝓝 0):= tendsto_const_nhds.congr fun i=> (smul_zero ..).symm
 exact Complex.continuous_re.continuousAt.tendsto.comp ((rays Z A Y p 0 t.le q ht.1 (fun _=>0) he).congr fun i=> congrArg (inner ℂ (v i)) (hg i))
private lemma atOnce (v:Bank) (E:ℕ→ℝ≥0)(w:P.dimensionS c r E 0)(F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)):
 Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (E i) (φ i)))) atTop (𝓝 (ovoid Z 0 v)) := by
 let T:= Ψ'; let v'(i:ℕ):= φ i; have he : Tendsto (fun i=> T.U (F i) (T.E (E i) (v' i))-T.U (F i) (v' i)) atTop (𝓝 0):= (soarE T F _ (shrinkage Z A Y p E w)).congr fun i=> map_sub (T.U (F i)) (T.E (E i) (v' i)) (v' i)
 have hh:=initialPoint Z A Y p v F h; exact unifier ((aura G v' _ (lucid_bill Z A Y p) he).congr fun i=> inner_sub_right (𝕜:=ℂ) (v' i) (T.U (F i) (T.E (E i) (v' i))) (T.U (F i) (v' i))) hh
lemma EuclidAll (v:Bank) (z:ℝ)(q:0≤z) (E:ℕ→ℝ≥0)(w:P.dimensionS c r E z)(F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)):
 Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (E i) (φ i)))) atTop (𝓝 (ovoid Z z v)) := by
 -- avoid expensive dependent subst. case
 by_cases e:z=0
 · exact Eq.mp (congrArg (fun t:ℝ=> Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (E i) (φ i)))) atTop (𝓝 (ovoid Z t v))) e.symm) (atOnce Z A Y p v E (Eq.mp (congrArg (P.dimensionS c r E) e) w) F h)
 · exact evenlater Z A Y p v (lt_of_le_of_ne q (Ne.symm e)) E w F h
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.EuclidAll
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.EuclidAll
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.rays
