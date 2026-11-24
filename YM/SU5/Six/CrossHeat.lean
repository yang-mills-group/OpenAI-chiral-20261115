import YM.SU5.Cheer.Verse
import YM.SU5.Six.CrossStock
/-!
# Mixed heat estimate in physical zoom units

As in Cordial/Horizon, now with distinct clans. Important that projection error,
rounding continuity estimates and the UV reading estimate all describe the *same*
vectors on the *same* x.
-/
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
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z W:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
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
local notation "𝑊" => P.ColorHil (ι) (χ)
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
private lemma project_left (X Y: V) : inner ℂ ((π') X) ((π') Y)= inner ℂ (P.visitors 3 (β) X) Y:= by
 let g:= P.visitors 3 (β); change inner ℂ (g X) (g Y) = _; let D:=P.Viewers 3 (β);
 -- use adj formula but expensive
 have hc: g.adjoint=g:=Alliance.symmetricstack ..; have he: g (g X)=g X:=Alliance.grounded _ _ ((Ψ).planted (look 3) X); exact (ContinuousLinearMap.adjoint_inner_left g Y (g X)).symm.trans (congrArg (inner ℂ · Y) ((DFunLike.congr_fun hc _).trans he))
variable {P x r c}(A:Launch P c r){d:ℕ→ℝ}(Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
local notation "Δ"=>ovoid Z 0 0
-- characterize Laplace transform of spatial
include A Y p
private lemma shard_bound : Limited V (fun i=> Φ i):= OS.Semigroup.Balloon.hasLimit (H:=V) (horn_norm Z A Y p) -- name
private lemma lucid_bound : Limited G (fun i=>φ i):= by
 obtain ⟨k,h⟩:=shard_bound Z A Y p
 exact ⟨k,h.mono fun i v=> le_trans (P.bank_cost 3 (β) (Φ i)) v⟩
variable (e : Z ≠ W)
include e
local notation "Puv" => ((purePrice Z:ℂ)*(purePrice W:ℂ))
local notation "ψ" i:max => P.lucid x W (c i) (r i)
local notation "JΦ" i:max => P.shard x W (c i) (r i)
private lemma roundedHeat (v:Bank) {z:ℝ}(q:0≤z)(D:ℕ→ℕ)(w:P.bargain r (fun i=>(D i:ℤ)) z): let T i:= whenly M (c i) (D i); Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (P.horizon c r v i) ((Ψ').E (T i) (ψ i)))) atTop (𝓝 (Puv)):=by
 let g(i:Street):=v.val i.val; let f(i:Street)(n:ℕ):=P.pan r v n i; let X(i):=P.pit c r v i; let ZK(n):= ψ n
 let SP:= Ψ'; let J:= look (3:Axis); intro T
 have h : ∀ i:Street,P.bargain r (f i) (g i):=fun i=> P.intendR r (g i) A.eager
 let qX (i:ℕ):=(Ψ).raw J (X i) ((S).E (T i) (JΦ i))
 
 have he:Tendsto (fun i=>inner ℂ (Φ i) (qX i)) atTop (𝓝 (Puv)):= cross_penetration Z W J A Y p e D z q (fun i n => f i n) g (fun i _=>h i) w
 have hh(i:ℕ): SP.U (P.horizon c r v i) (SP.E (T i) (ZK i))= (π') (qX i):= by
    have ht:= P.bankHeat 3 (β) (T i) (JΦ i); exact (congrArg (SP.U (P.horizon c r v i) : (P.ManyF 3 (β)).space → _) ht.symm).trans (P.roll_motion 3 (β) (P.pit c r v i) ((S).E (T i) (JΦ i)))
 let K:=P.visitors 3 (β); have hp: Limited (V) qX:= le_seam (fun i=> JΦ i) (shard_bound W A Y p) (fun i=> ((Ψ).raw_isometry J (X i) ((S).E (T i) (JΦ i))).le.trans (heatedLim (S) (T i) (JΦ i)))
 have hv:Tendsto (fun i=> inner ℂ (K (Φ i)) (qX i) - inner ℂ (Φ i) (qX i)) atTop (𝓝 0):=(aura' V qX _ hp (whole_sky Z A Y p)).congr fun i=> inner_sub_left (𝕜:=ℂ) (K (Φ i)) (Φ i) (qX i)
 exact (unifier hv he).congr fun i=> ((congrArg (inner ℂ (φ i)) (hh i)).trans (P.project_left x (Φ i) (qX i))).symm
private lemma mixedRays (v:Bank) {z:ℝ} (q:0≤z)(D:ℕ→ℕ)(w:P.bargain r (fun i=>(D i:ℤ)) z)(F:ℕ→ Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)) : Tendsto (fun i=>inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (whenly M (c i) (D i)) (ψ i)))) atTop (𝓝 (Puv)):= by
 let t(i):=whenly M (c i) (D i); let x' (i:ℕ):= ψ i; let B' := Ψ'; let g:=P.horizon c r v; let E i:= B'.E (t i) (x' i);
 have he:=roundedHeat Z W A Y p e v q D w; have hv: Tendsto (fun i=> B'.U (F i) (x' i)- B'.U (g i) (x' i)) atTop (𝓝 0):= neighbor W A Y p v (P.pan r v) F (fun i=> P.intendR r (reveal i v) A.eager) h
 have hw:Tendsto (fun i=> inner ℂ (φ i) (B'.U (F i) (E i))- inner ℂ (φ i) (B'.U (g i) (E i))) atTop (𝓝 0):= (aura G _ _ (lucid_bound Z A Y p) (realize_shim (Ψ') x' t F g hv)).congr fun i=> inner_sub_right (𝕜:=ℂ) (φ i) (B'.U (F i) (E i)) (B'.U (g i) (E i))
 exact unifier hw he
lemma mixed_lucid_pos (v:Bank) {z:ℝ}(q:0<z) (E:ℕ→ℝ≥0)(w:P.dimensionS c r E z)(F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)):
 Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (E i) (ψ i)))) atTop (𝓝 (Puv)) := by
 let T:= Ψ'; let v'(i:ℕ):= ψ i; let D:=(grantR A z q.le).choose; have he:= (grantR A z q.le).choose_spec; let L(i:ℕ):= whenly M (c i) (D i); let Z'(i:ℕ):= T.E (E i) (v' i); let G'(i:ℕ):= T.E (L i) (v' i)
 have hx:Tendsto (fun i=> T.U (F i) (Z' i) - T.U (F i) (G' i)) atTop (𝓝 0):= (soarE T F _ (uniform_zoom T v' (fun i=> P.dew_pos _ (A.unitSize i)) w he.2 q (lucid_bound W A Y p))).congr fun i=> map_sub (T.U (F i)) (Z' i) (G' i)
 let f(i):=inner ℂ (φ i) (T.U (F i) (Z' i)); let g(i):=inner ℂ (φ i) (T.U (F i) (G' i)); have hh:Tendsto (fun i=> f i - g i) atTop (𝓝 0):= (aura G _ _ (lucid_bound Z A Y p) hx).congr fun i=> inner_sub_right (𝕜:=ℂ) (φ i) (T.U (F i) (Z' i)) (T.U (F i) (G' i))
 exact unifier hh (mixedRays Z W A Y p e v q.le D he.1 F h)
lemma mixed_lucid_init (v:Bank)(F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)): Tendsto (fun i=>inner ℂ (φ i) ((Ψ').U (F i) (ψ i))) atTop (𝓝 (Puv)):= by
 let x' (i:ℕ):= ψ i; let T:= Ψ'; let g(i:ℕ):=T.E (whenly M (c i) 0) (x' i); have he(i:ℕ):g i=x' i:= (congrArg (fun t=> T.E t (x' i)) (when_zero ..)).trans (DFunLike.congr_fun T.eZero _)
 exact (mixedRays Z W A Y p e v le_rfl (fun i=>0) (unpaid_move (P:=P)) F h).congr fun i=> congrArg (inner ℂ (φ i) ∘ T.U (F i)) (he i) -- coercion

omit A Y p e
section
variable {j:Axis}{H:Hilbert}
private lemma center_formula (S':OS.Semigroup H j) (v v' w w' Ω:H)
    (a:OS.Cross j)(t:ℝ≥0)(m n:ℂ)(h: v=v'+m • Ω)(r:w=w'+n • Ω)
    (o: inner ℂ Ω v'=0)(o':inner ℂ Ω w'=0)(η:‖Ω‖=1)
    (s': S'.U a Ω = Ω)(y': S'.E t Ω = Ω) :
    inner ℂ v' (S'.U a (S'.E t w')) =
      inner ℂ v (S'.U a (S'.E t w))-star m*n := by
  have hl:inner ℂ Ω (S'.U a (S'.E t w'))=0:=by
    nth_rw 1 [← s']; rw [minted,← S'.swing,y',o']
  rw [h,r,map_add,map_add,map_smul,map_smul,y',s',inner_add_left,inner_add_right,
    inner_add_right, inner_smul_right,inner_smul_left,inner_smul_left,inner_smul_right,hl,
    ← inner_conj_symm (𝕜:=ℂ) v' Ω, o, inner_self_eq_norm_sq_to_K]
  simp [η]
end
lemma cross_center {i n:ℕ} (t:ℝ≥0) (a:Bank) (u:P.lodestarHere 3 (β)) :
    inner ℂ (P.birthCloud x Z i n) ((Ψ').U a ((Ψ').E t (P.birthCloud x W i n))) =
      inner ℂ (P.lucid x Z i n) ((Ψ').U a ((Ψ').E t (P.lucid x W i n))) -
        star (P.allowance x Z i n) * P.allowance x W i n := by
  let Ω:= P.heaven 3 (β)
  have he: (Ψ').E t Ω=Ω:= by
    apply (heat_iff_edge (3:Axis) (Ψ') _).mpr _ t
    exact ((P.heavenRank 3 (β) u _).1 (Submodule.subset_span (Set.mem_singleton _))).1
  exact center_formula (Ψ') _ _ _ _ Ω _ _ _ _ (P.halo_split ..) (P.halo_split ..)
    (P.halo_zero ..) (P.halo_zero ..) (P.stone_norm ..) (P.stone_warm 3 (β) u a) he
variable (u:P.lodestarHere 3 (P.otherSpectrum 3 3 x))
include A Y p u
local notation "m" Z:max i:max => P.birthCloud x Z (c i) (r i)
private lemma center_price (t:ℕ→ℝ≥0)(F:ℕ→Bank){b:ℂ}
    (L:Tendsto (fun i=> inner ℂ (φ i) ((Ψ').U (F i) ((Ψ').E (t i) (ψ i)))) atTop (𝓝 b)) :
    Tendsto (fun i=> inner ℂ (m Z i) ((Ψ').U (F i) ((Ψ').E (t i) (m W i)))) atTop
      (𝓝 (b-Puv)) := by
  let lZ:ℂ:= (purePrice Z:ℂ)
  have pf := (refreshing Z A Y p).star
  let f (i:ℕ):= star (P.allowance x Z (c i) (r i))
  have hg : star lZ=lZ := by simp [lZ]
  have hf : Tendsto f atTop (𝓝 lZ) := by
    have pf' : Tendsto f atTop (𝓝 (star lZ)) := pf
    rw [hg] at pf'
    exact pf' 
  exact (L.sub (hf.mul (refreshing W A Y p))).congr fun i=>
    (cross_center Z W (i:=c i) (n:=r i) (t i) (F i) u).symm

/-- Useful also with *moving* heat and space arguments. Diagonal. -/
lemma zoom_diagonal (a:Space3)(t:ℝ≥0)(E:ℕ→ℝ≥0)(w:P.dimensionS c r E (t:ℝ))
    (F:ℕ→Bank)(h:Tendsto (fun i=>(ρ i)⁻¹ • F i) atTop (𝓝 (cutPulse a))) :
    Tendsto (fun i=> inner ℂ (m Z i) ((Ψ').U (F i) ((Ψ').E (E i) (m Z i)))) atTop
      (𝓝 (Cheer.FLap (promenade Z) a (↑(t:ℝ)))):= by
  have he : ovoid Z (t:ℝ) (cutPulse a) - (purePrice Z:ℂ)*(purePrice Z:ℂ)=Cheer.FLap (promenade Z) a ↑(t:ℝ) := by simpa only [pow_two] using blinded Z a t
  let f (i:ℕ):= inner ℂ (m Z i) ((Ψ').U (F i) ((Ψ').E (E i) (m Z i)))
  have ht:Tendsto f atTop (𝓝 (ovoid Z (t:ℝ) (cutPulse a) - (purePrice Z:ℂ)*(purePrice Z:ℂ))):= center_price Z Z A Y p u E F (EuclidAll Z A Y p (cutPulse a) t t.property _ w _ h)
  rw [he] at ht
  exact ht

include e
/-- Off-diagonal FLap test (variable poses, at strictly positive zoomed time). -/
lemma zoom_other_pos (v:Bank){z:ℝ}(q:0<z)(E:ℕ→ℝ≥0)(w:P.dimensionS c r E z)
    (F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i=> inner ℂ (m Z i) ((Ψ').U (F i) ((Ψ').E (E i) (m W i)))) atTop (𝓝 0) := by
  simpa only [sub_self] using center_price Z W A Y p u _ _
    (mixed_lucid_pos Z W A Y p e v q _ w _ h)

lemma zoom_other_zero (v:Bank)(F:ℕ→Bank)(h:Tendsto (fun i=> (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i=> inner ℂ (m Z i) ((Ψ').U (F i) ((Ψ').E 0 (m W i)))) atTop (𝓝 0) := by
  have ht := center_price Z W A Y p u (fun _=>0) F (b:=Puv)
    ((mixed_lucid_init Z W A Y p e _ F h).congr fun i=>
      congrArg (inner ℂ (φ i) ∘ (Ψ').U (F i)) (show (Ψ').E 0 (ψ i)=ψ i from DFunLike.congr_fun (Ψ').eZero _).symm)
  simpa only [sub_self] using ht

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
