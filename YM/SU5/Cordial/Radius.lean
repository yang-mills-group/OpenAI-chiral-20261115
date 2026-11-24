import YM.SU5.Cordial.Muses
import YM.SU5.Cordial.Ovals
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
def lucid (n:ℕ): P.ManyF 3 (β):= P.wealth 3 (β) (P.shard x Z s n)
local notation "φ" i:max=> P.lucid x Z (c i) (r i)
def mhint (y':Bank) (n:Street→ℝ) : Prop:= y'= transverse 3 n -- tune
lemma mhint_one (v:Bank): mhint v (fun i=> v.val i.val):= eyes_toFace ..
lemma mons(x:Bank) : ∀ (d:Street), (palace (look 3) (fun i=>x.val (i.val))).val d.val=x.val d.val:=by
 intro k; let f:=fun i:Street=>x.val i.val
 have he(i j:Street): (f i • streak i).val j.val= if j=i then f i else 0 := by
    change f i * (basis i.val) j.val=_; by_cases h:j=i
    · subst i; simp
    simp [h,show j.val ≠ i.val from (fun v=> h (Subtype.ext v))]
 have ht(L:List Street)(u:L.Nodup):(palace L f).val k.val=if k∈L then f k else 0:=by
    induction L with
    | nil=>simp [palace]
    | cons i L ih=> obtain ⟨p,q⟩:=List.nodup_cons.mp u; rw [palace_one]; change ((f i•streak i).val k.val)+(palace L f).val k.val= _; by_cases h:i=k; subst i; rw [he,ih q]; simp [p]; rw [he,ih q]; simp [Ne.symm h]
 exact (ht (look 3) (look_one 3)).trans (if_pos (look_all 3 k))
lemma palace_exact(x:Bank) : palace (look 3) (fun i=>x.val i.val)=x:= (eyes_toFace 3 _).trans ((congrArg (transverse 3) (funext (mons x))).trans (eyes_toFace 3 _).symm)
-- aggregate value
abbrev mountain (P: Spine) (z:Street→marks (timeMesh P.par)): Bank:= transverse 3 (fun i=>((z i):ℝ))
lemma mont_plus (x z:Street→Γ): P.mountain (x+z)=P.mountain x+P.mountain z:=by
 apply Subtype.ext; ext i; by_cases h:i=3; · subst i; exact (P.mountain _).property.trans ((show (((P.mountain x)+(P.mountain z)).val:E4) 3=0 from (P.mountain x + P.mountain z).property).symm)
 change (P.mountain _).val i=(P.mountain _).val i+ (P.mountain _).val i; let k:Street:=⟨i,h⟩; rw [show (P.mountain (x+z)).val i=((↑((x+z) k)):ℝ) from transverse_eyes 3 _ k,show (P.mountain x).val i=((↑(x k)):ℝ) from transverse_eyes 3 _ k,show (P.mountain z).val i=((↑(z k)):ℝ) from transverse_eyes 3 _ k]; rfl
lemma dizzy (H:Hilbert){a:Axis}(S':OS.Semigroup H a)(v:H)(x z w: OS.Cross a)(k:x=w+z) : ‖S'.U x v - S'.U w v‖=‖S'.U z v - v‖:= by rw [k,S'.space,ContinuousLinearMap.comp_apply,←map_sub,S'.unitary]
lemma notch_clear (i:ℕ): N₀ i (0:ℤ)=0:= notch_zero ..
lemma ridge (p:Street→Γ)(t:ℕ): (Ψ').U (P.mountain p) (φ t)=π' ((Ψ).raw (look 3) p (Φ t)):= P.roll_motion ..
lemma life_cost (w g: V) : ‖π' w - π' g‖≤ ‖w-g‖:= (le_of_eq (congrArg norm (map_sub (π') w g).symm)).trans (P.bank_cost 3 (β) (w-g))
section Tor
variable {P x c r} (A:Launch P c r) {d:ℕ→ℝ} (Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
local notation "Δ"=>ovoid Z 0 0
include A Y p
-- zero real measure limit even before projecting. fix K for lemma then remove dep
lemma horn_value : Tendsto (fun i:ℕ=>inner ℂ (Φ i) (Φ i)) atTop (𝓝 (Δ)):=by
 let F : Spine.Street:=⟨0,by decide⟩; have he:= pledge Z F A Y p _ (unpaid_move (P:=P) (r:=r));
 -- h ∞ kernel at 0
 have h0(n:ℕ) : P.viewer x Z F (c n) (N₀ (c n) 0) (r n)=inner ℂ (Φ n) (Φ n):=by
    let T' := (Ψ).crew F; let f:= Φ n; exact congrArg (inner ℂ f) ((congrArg (fun z=> T'.play z f) (P.notch_clear (c n))).trans (DFunLike.congr_fun (T').play_zero _))
 refine (congrArg (ovoid Z 0) (zero_smul ℝ (streak F))) ▸ he.congr h0 -- timeout
lemma horn_norm : Tendsto (fun i:ℕ=> ‖Φ i‖^2) atTop (𝓝 (Δ).re):=((Complex.continuous_re.continuousAt.tendsto.comp (horn_value Z A Y p))).congr fun i=> inner_self_eq_norm_sq (𝕜:=ℂ) (Φ i)
lemma estimates : OrbitTools.Recovers (U) (fun t=>ovoid Z 0 (t • streak k)) (fun i=>Φ i) (fun i=> ρ i) := by
 have he: (ovoid Z 0 ( (0:ℝ) • streak k)).re=(Δ).re:= congrArg Complex.re (congrArg _ (zero_smul ..));
 refine ⟨ (by exact (((horn_cont Z (t:=0) le_rfl).comp (continuous_id.smul continuous_const))).continuousAt), fun v _=>⟨_,P.priceV c r _ _ (P.intendR r v A.eager) A.unitSize⟩, ?_,fun u v h e=>⟨matchesM Z k A Y p u h e,persisted Z k A Y p u h e⟩⟩
 -- change limit only
 exact Eq.mp (congrArg (fun t=> Tendsto (fun i=> ‖Φ i‖^2) atTop (𝓝 t)) he.symm) (horn_norm Z A Y p) -- tune
lemma whole_sky : Tendsto (fun i:ℕ=> P.visitors 3 (β) (Φ i)- Φ i) atTop (𝓝 0):= (Ψ).stack_zooms (look 3) (fun i=> Φ i) fun k _=> (estimates Z k A Y p).clear
lemma raw_march (D:ℕ→Street→Γ)(h:∀ i:Street,P.attendsSky c r (fun j=>D j i) 0): Tendsto (fun i=> (Ψ).raw (look 3) (D i) (Φ i) - Φ i) atTop (𝓝 0) := (Ψ).raw_zoom _ _ (fun i _=> (estimates Z i A Y p).continuous_on (fun j=> D j i) (h i))
lemma raw_lift (D:ℕ→Street→Γ)(h:∀ i:Street,P.attendsSky c r (fun j=> D j i) 0) : Tendsto (fun j=> (Ψ').U (P.mountain (D j)) (φ j) - φ j) atTop (𝓝 0) := by
 let v :ℕ→ V:= fun i=>Φ i; let f:= P.wealth 3 (β); let t:=raw_march Z A Y p D h; have he:= f.continuous.continuousAt.tendsto.comp t
 have ha:f (0:V) = 0:=map_zero f
 have hr : Tendsto _ _ (𝓝 (0:G)):= Eq.mp (congrArg (fun a=> Tendsto (fun i:ℕ=>f ((Ψ).raw (look 3) (D i) (Φ i) - Φ i)) atTop (𝓝 a)) ha) he
 refine hr.congr fun i=>?_ ; let a:= P.ridge x Z c r (D i) i; let u:= (Ψ).raw (look 3) (D i) (v i);
 exact (map_sub f u (v i)).trans (congrArg (·- f (v i)) a.symm)
end Tor
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.raw_lift
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.whole_sky
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.life_cost
