import YM.SU5.Aria.Exult
import YM.SU5.Cheer.Harp
set_option maxHeartbeats 250000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open Aria Set
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(c r:ℕ→ℕ)
local notation "K"=> P.calibration
local notation "Λ"=> P.par
local notation "R"=> ruler P.par.block
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 (P.advocate 3 x 3)
local notation "Ω"=> P.heaven 3 (P.advocate 3 x 3)
local notation "ω"=> P.colorZero 3 (P.advocate 3 x 3)
local notation "S"=> P.seasons 3 (P.advocate 3 x 3)
local notation "G"=> P.ManyF 3 ξ
local notation "L₀"=>P.leftX Z s n
local notation "L₁"=>P.rightX Z s n
local notation "η"=> P.pairStory Z s n
local notation "p"=> P.stockS Z (P.flash n)
local notation "Σ₀"=> Prod.fst (α:=P.Apron) (β:=Vantage)
local notation "Σ₁"=> Prod.snd (α:=P.Apron) (β:=Vantage)
local notation "Χ" L:max=> P.commonWell 3 x Σ₀ Σ₁ L
variable (J:P.Ellis 3 x)
local notation "κ"=> P.cartage 3 ξ
local notation "u"=> P.palp s
local notation "E"=> (S).E
local notation "F"=>P.crownT Z s n
local notation "Z'"=> P.allowance x Z s n
local notation "Δ"=> P.lucid x Z s n
local notation "a"=>P.markX s
def pathGlow := P.pulse0 x Z s n - (Χ [L₀]) • Ω
lemma centered_glow (J:P.Ellis 3 x): P.pathGlow x Z s n = E a (P.birthCloud x Z s n):= by
 let v:= Δ; let K':= Z'; let η':=P.birthCloud x Z s n; have hv:E a η'= E a v- K' • Ω:=by
   apply Eq.trans (map_sub (E a) Δ (K' • Ω)); rw [map_smul,P.heaven_hot]
 let w:=Χ [L₀]; have hw:P.pulse0 x Z s n=E a v:= P.honorPulse ..
 exact (congrArg₂ (fun (v:G)(w:ℂ)=>v-w•Ω) hw (P.single_pays x Z s n J).1).trans hv.symm
-- spectral pricing harness
lemma sailLoan (J:P.Ellis 3 x): inner ℂ Ω (P.pathGlow x Z s n)=0:=by rw [P.centered_glow x Z s n J,← OS.Semigroup.swing,P.heaven_hot]; exact P.halo_zero ..
private lemma spectrum_pay (G':Hilbert)(σ: Spectral.PVM G' E4)(x:G'){Z:Set E4}(h:MeasurableSet Z): ‖σ.region Z x‖≤ ‖x‖:=by
 apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
 have he:= measureReal_mono (μ:=σ.diagonal x) (Set.subset_univ Z)
 have hf: (σ.diagonal x).real Set.univ= ‖x‖^2:= by rw [σ.same MeasurableSet.univ x,σ.all, ContinuousLinearMap.id_apply]
 rw [← σ.same h x,←hf] -- potential rewrites x norm inside previous wrong? tune
 exact he -- infer
variable {P x c r}(A:Launch P c r){g:ℕ→ℝ}(T:readyUV P c r x g)(d:Tendsto g atTop (𝓝 0))
include A T d J
local notation "ρ" i:max=> P.dew (c i) (r i)
open Cheer (press)
local notation "ϕ" i:max=> P.pulse0 x Z (c i) (r i)
local notation "ε" i:max=> P.pathGlow x Z (c i) (r i)
local notation "κ'" i:max=> P.birthCloud x Z (c i) (r i)
local notation "virtue" i:max=> P.lucid x Z (c i) (r i)
omit A T d J in
private lemma duo_payment (G':Hilbert)(X' Y':ℕ→G')(X:ℝ)(hx: ∀ i, ‖Y' i‖≤ ‖X' i‖) (hy:Tendsto (fun i=>‖X' i‖^2) atTop (𝓝 X))(hv:Tendsto (fun i=>(inner ℂ (X' i) (Y' i)).re) atTop (𝓝 X)) : Tendsto (fun i=>Y' i-X' i) atTop (𝓝 0):=by
 have he:Tendsto (fun i=> ‖X' i-Y' i‖^2) atTop (𝓝 0):=by
    have he:= (hy.sub hv).const_mul 2; rw [sub_self,mul_zero] at he; refine squeeze_zero (fun i=>sq_nonneg _) ?_ he; intro i; rw [norm_sub_sq (𝕜:=ℂ)]; rw [show (RCLike.re:ℂ→ℝ)=Complex.re from rfl]; nlinarith [hx i,norm_nonneg (Y' i)]
 apply tendsto_zero_iff_norm_tendsto_zero.mpr; have hp:= Real.continuous_sqrt.continuousAt.tendsto.comp he; rw [Real.sqrt_zero] at hp; exact hp.congr fun i=> (Real.sqrt_sq (norm_nonneg _)).trans (norm_sub_rev ..)
omit J in
lemma safe_level : Tendsto (fun i=> (ϕ i)-(virtue i)) atTop (𝓝 0):=by
 let μ(i):=P.allowance x Z (c i) (r i); let ξ'(i:ℕ):= ε i; let v(i:ℕ):= virtue i; let w(i:ℕ):= ϕ i
 let D(i:ℕ):= P.markX (c i); let U:=ovoid Z 0 0; have hD:P.dimensionS c r D 0:= shrinkBeat A 1
 have hs:Tendsto (fun i=> (ρ i)⁻¹ • (0:Bank)) atTop (𝓝 0):= by simp
 have htν:= EuclidAll Z A T d (0:Bank) 0 (by norm_num) D hD (fun _=>0) hs; have hx:Tendsto (fun i=> (inner ℂ (v i) (w i)).re) atTop (𝓝 U.re):=by
    let h(i:ℕ): (S).U 0 (E (D i) (v i))=w i:= (DFunLike.congr_fun (S).uZero _).trans (P.honorPulse x Z (c i) (r i)).symm
    refine (Complex.continuous_re.continuousAt.tendsto.comp htν).congr (fun i=> congrArg (fun y:G=>(inner ℂ (v i) y).re) (h i))
 have hy:Tendsto (fun i=> ‖v i‖^2) atTop (𝓝 U.re):= eyes_norm Z A T d -- name exported
 refine duo_payment G v w _ (fun i=> ?_) hy hx;
 exact (le_of_eq (congrArg norm (P.honorPulse x Z (c i) (r i)))).trans (((S).E (D i)).le_opNorm (v i) |>.trans (mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks _)))
omit J A T d in
private lemma concise (H':Hilbert)(X Y Z Q R':H')(h:X=Y-Z)(k:Q=R'-Z): X-Q=Y-R':= by rw [h,k]; abel
private lemma slim_rule (i:ℕ) : ε i - (κ' i)=ϕ i - (virtue i):=by
 let w:= P.allowance x Z (c i) (r i); have ht: ε i=ϕ i - w • Ω:= congrArg (fun z:ℂ => (ϕ i)-z • Ω) (P.single_pays x Z (c i) (r i) J).1
 exact concise G _ _ _ _ _ ht rfl
lemma approaches_glow : Tendsto (fun i=> (ε i)-(κ' i)) atTop (𝓝 0):=(safe_level Z A T d).congr fun i=> (slim_rule Z J A T d i).symm
lemma spectrum_hit {L:Set E4}(v:IsOpen L)(h:(Mink.inside∩L).Nonempty)(t:P.Bands x Z c r): ∃ D:ℝ, 0 < D ∧ ∀ᶠ i in atTop, D < ‖(S).ℚmeasure.region (Cheer.press (ρ i) L) (ε i)‖^2:=by
 obtain ⟨s,h₀,S'⟩:=Spine.lit t L v h; let U := Real.sqrt s /2; have hu:0<U:=by positivity
 refine ⟨U^2,by positivity,?_⟩
 have he:= approaches_glow Z J A T d -- arg order check
 filter_upwards [S',(he.norm).eventually (gt_mem_nhds (show ‖(0:G)‖<U by simpa using hu))] with i t y
 let X':=(ε i); let Y':=(κ' i); let U':=(S).ℚmeasure.region (Cheer.press (ρ i) L); change U^2 < ‖U' X'‖^2; change s< ‖U' Y'‖^2 at t; change ‖X'-Y'‖<U at y; apply (sq_lt_sq₀ hu.le (norm_nonneg _)).mpr; have hp: Real.sqrt s < ‖U' Y'‖:= by nlinarith [Real.sqrt_nonneg s, Real.sq_sqrt h₀.le, norm_nonneg (U' Y')]
 have hy: ‖U' Y'‖ - ‖U' X'‖ < U:=by
   apply (norm_sub_norm_le (U' Y') (U' X')).trans_lt; rw [←map_sub]; exact (spectrum_pay G (S).ℚmeasure _ (Cheer.pressured _ v.measurableSet)).trans_lt ((norm_sub_rev ..).trans_lt y)
 unfold U at *; linarith -- tune
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.spectrum_hit
