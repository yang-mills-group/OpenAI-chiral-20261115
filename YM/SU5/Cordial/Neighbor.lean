import YM.SU5.Cordial.Radius
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
-- approximate *coordinates*, not assuming arbitrary lattice shifts continuous before smoothing
open Set
private lemma transverse_cont : Continuous (transverse (3:Axis)):= Continuous.subtype_mk (by
 apply ((PiLp.continuous_toLp 2 _).comp (f:=fun x:Trans 3→ℝ=> fun i:Axis=> if h:i = (3:Axis) then (0:ℝ) else x ⟨i,h⟩) (continuous_pi fun i=> ?_)); split
 · exact continuous_const
 exact continuous_apply _) _
lemma mount_dense : DenseRange P.mountain:=by
 let L:= fun (x:Street→ marks M) (i:Street)=> ((x i):ℝ); let f:= transverse 3;
 have h:DenseRange L:= DenseRange.piMap fun _=>(daylight M).denseRange_val; have hf : DenseRange f:= (show Function.Surjective f from (fun x=>⟨_, (eyes_toFace 3 x).symm⟩)).denseRange; exact hf.comp h transverse_cont
lemma mount_rep (u:Street→Γ) : (P.mountain u).val k.val=(u k:ℝ):= transverse_eyes 3 _ k
noncomputable def reveal : Bank→ℝ:=fun x=>x.val k.val
private lemma reveal_cont : Continuous (reveal k):= by unfold reveal; fun_prop
lemma rev_zero : reveal k 0=0:= rfl
lemma revs (c:ℝ)(x:Bank): reveal k (c • x)=c*reveal k x:=rfl
lemma presentZ (H:Hilbert)(L: OS.Semigroup H (3:Axis)){T : Type*}(h:T→Bank)(g:DenseRange h)(a:ℝ)(u:ℝ)(p:0<u)(z:Bank)(w:H):∃ x:T, dist (a • h x) (a • z)<u ∧ dist (L.U (h x) w) (L.U z w)<u:=by
 have ht:= (L.continuousU w).tendsto z; let f(v : Bank):=a • v; have h2: Continuous f:= by unfold f; fun_prop
 have hk := (Metric.tendsto_nhds.mp ht u p).and (Metric.tendsto_nhds.mp (h2.tendsto z) u p); exact g.mem_nhds (show ∀ᶠ x' : Bank in 𝓝 z, dist (f x') (f z)<u ∧ dist (L.U x' w) (L.U z w)<u from hk.mono fun i u=>⟨u.2,u.1⟩)
private lemma densifies (H:Hilbert)(L:OS.Semigroup H (3:Axis)){X : Type*}(h:X→Bank)(g:DenseRange h)(a:ℕ→ℝ)(c:ℕ→H)(F:ℕ→ Bank)(v:Tendsto (fun i=>a i • F i) atTop (𝓝 0))(t:∀ (u:ℕ→X), Tendsto (fun n=>a n • h (u n)) atTop (𝓝 0)→ Tendsto (fun n=> L.U (h (u n)) (c n)-c n) atTop (𝓝 0)): Tendsto (fun n=> L.U (F n) (c n)-c n) atTop (𝓝 0):= by
 choose z e u using fun n:ℕ=> presentZ H L h g (a n) (keyV n) (keyV_positive n) (F n) (c n)
 have hx: Tendsto (fun n=> a n • h (z n)) atTop (𝓝 0):=(tendsto_iff_of_dist (squeeze_zero (fun n=>dist_nonneg) (fun n=>(e n).le) keyV_go)).2 v
 have hz:Tendsto (fun n=> L.U (F n) (c n)-L.U (h (z n)) (c n)) atTop (𝓝 0):= by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun n=> norm_nonneg _) (fun i=> ?_) keyV_go; exact (dist_eq_norm _ _).symm.le.trans ((dist_comm ..).le.trans (u i).le)
 have hw:=hz.add (t z hx); rw [zero_add] at hw; exact hw.congr fun i=> sub_add_sub_cancel ..
variable {P x r c}(A:Launch P c r){d:ℕ→ℝ}(Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
local notation "Δ"=>ovoid Z 0 0
-- generic dense extension
open Filter
include A Y p
lemma spatial_near (F:ℕ→Bank)(v:Tendsto (fun n=> ((ρ n)⁻¹) • F n) atTop (𝓝 0)): Tendsto (fun n=> (Ψ').U (F n) (φ n)- φ n) atTop (𝓝 0):=by
 let Vh (n:ℕ):G:= φ n
 refine densifies G (Ψ') P.mountain P.mount_dense _ Vh F v fun z hx=>?_ 
 have he(k:Street):P.attendsSky c r (fun n=> z n k) 0:=by
    have hie:= (reveal_cont k).continuousAt.tendsto.comp hx; rw [rev_zero] at hie; exact hie.congr fun i=> by rw [Function.comp_apply,revs,show reveal k (P.mountain (z i))=(z i k:ℝ) from P.mount_rep k (z i),mul_comm,div_eq_mul_inv]
 exact raw_lift Z A Y p z he
omit A Y p in
private lemma limit_expose {u:ℕ→Bank}{v:Bank}(x:∀ k,Tendsto (fun n=>reveal k (u n)) atTop (𝓝 (reveal k v))):Tendsto u atTop (𝓝 v):= by
 rw [eyes_toFace 3 v]; exact (transverse_cont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr x)).congr fun n=>(eyes_toFace 3 (u n)).symm -- unification danger
omit Y p in
lemma find_shadow (v:Bank) (D:ℕ→Street→ℤ)(w:∀ i:Street,P.bargain r (fun n=> D n i) (reveal i v)): let K i j:= N₀ (c i) (D i j); Tendsto (fun n=> (ρ n)⁻¹ • P.mountain (K n)) atTop (𝓝 v):=by
 intro K; apply limit_expose; intro i; refine (P.priceV c r _ _ (w i) A.unitSize).congr fun n=>?_ ; rw [revs,show reveal i _= (K n i:ℝ) from P.mount_rep i _,div_eq_mul_inv,mul_comm]
lemma neighbor (v:Bank) (K:ℕ→Street→ℤ) (F:ℕ→Bank)(w:∀ i:Street, P.bargain r (fun n=> K n i) (reveal i v))(h:Tendsto (fun n=> (ρ n)⁻¹ • F n) atTop (𝓝 v)) : let u i j:= (N₀ (c i) (K i j)); Tendsto (fun n=> (Ψ').U (F n) (φ n) - (Ψ').U (P.mountain (u n)) (φ n)) atTop (𝓝 0):=by
 intro u; let q (i:ℕ):=P.mountain (u i); let g(i):=F i-q i; have ht:= h.sub (find_shadow A v K w); rw [sub_self] at ht; have hg:= spatial_near Z A Y p g (ht.congr fun i=>(smul_sub ..).symm);
 rw [tendsto_zero_iff_norm_tendsto_zero]; exact (tendsto_zero_iff_norm_tendsto_zero.mp hg).congr fun i=> (dizzy G (Ψ') (φ i) (F i) (g i) (q i) (by unfold g; abel)).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.neighbor
