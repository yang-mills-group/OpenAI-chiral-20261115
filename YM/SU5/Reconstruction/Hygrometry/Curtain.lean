import YM.SU5.Reconstruction.Hygrometry.Theatre
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker -- may clobber K.Gauge representation norms
attribute [local instance] opCStarAlgebra
variable (m t s:ℕ)
local notation "𝗠" i:max j:max=> Journey.side Y i j
local notation "🎨" i:max=> (Y.voyage m).CapeT i
open LocalLimit.Intermediate Harbour
variable (T:ℕ) (F:Intermediate.Room T→ Corr (Λ.Ctor (Y.ir m) T))(z:Intermediate.Room T)
variable (P:Ramp) (r:ℝ≥0)
local notation "Θ" f:max=> Tilted.Ramp.bill P f
open Hygrometry Hygrometry.PriceCliff Metric Hygrometry.MeterFunding
namespace Therapies
-- physical purchase not just seats, show even complete stencil loci of points moving to ACTUAL positions inside Aperture qualify (with any appropriate sign Frame etc). Prove generically using Riemann lobe.
variable {β:Type*}[Fintype β]
variable (τ:ℕ→ℕ)(z:ℕ→ Cover)(q:Tendsto τ atTop atTop)
local notation "ξ" n:max=> i (G.rows n)
local notation "S" n:max=> Journey.side Y (i (G.rows n)) (τ n)
local notation "R" n:max=> precisionAt Λ (τ n)
local notation "L" n:max x:max=> gaugePosition Λ (τ n) x
local notation "N" n:max=> nodeC (z n)
open Stationary (Gaia)
include V q G
lemma calibrated (x:Gaia) (p:Tendsto (fun n=>Onyx.riseX (R n) (z n)) atTop (𝓝 x)): Tendsto (fun n=> gaugePosition Λ (τ n) (nodeC (z n))) atTop (𝓝 x.ofLp):= by
 simp_rw [←location_eq, risingPays]; exact tendsto_pi_nhds.mpr (atlas_tend.1 ((trace_iff (budget_grant Y H V G τ q) z x).2 p)) -- G isn't used except Y notation;include explicit
-- can use all t with independent G.Clock 
omit q
lemma widthMeters: Tendsto (fun n=>period Y (ξ n) (τ n)) atTop atTop:= by
 have hg : Tendsto (fun n=> ((Journey.side Y (ξ n) 0).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp ((SlabMark.goes Y H 0).comp ((V.pick.grow_i.comp G.history.growsA).tendsto_atTop))
 refine hg.congr (fun n=>?_); have he:=period_width Y 0 (ξ n) (τ n); rw [zero_add] at he; unfold period; rw [he]; change _=gaugeMesh Λ 0*((((Journey.side Y (ξ n) 0).val*2:ℕ)):ℝ); unfold gaugeMesh; push_cast; rw [pow_zero]; ring
include q
lemma thinnerT : Tendsto (fun n=> gaugeMesh Λ (τ n)) atTop (𝓝 0):=by
 apply Tendsto.congr _ (show Tendsto (fun n=>(1/2:ℝ)/R n) atTop (𝓝 0) from (budget_grant Y H V G τ q).thinner (1/2)); intro n; unfold precisionAt gaugeMesh; ring
lemma allowance (x:Gaia)(W:Set RSpace)(s:x.ofLp∈W)(e:IsOpen W)(p:Tendsto (fun n=>Onyx.riseX (R n) (z n)) atTop (𝓝 x)) : ∀ᶠ n in atTop,Fits Y (i (G.rows n)) (τ n) P r W {nodeC (z n)}:= by
 let b':= |landN P x.ofLp|+r+1; have he:= Metric.mem_nhds_iff.mp (show W∩ (fun x:RSpace=>|landN P x|+(r:ℝ))⁻¹' Iio b' ∈𝓝 x.ofLp from inter_mem (e.mem_nhds s) ((landNp P |>.abs|>.add continuous_const).continuousAt.preimage_mem_nhds (gt_mem_nhds (lt_add_one _)))) -- tune syntax
 obtain ⟨δ,u,v⟩:=he; let A i:= (reserve Λ l:ℝ)*gaugeMesh Λ (τ i); have hp:Tendsto A atTop (𝓝 0):=(mul_zero (reserve Λ l:ℝ)) ▸ (thinnerT Y H V G τ q).const_mul (reserve Λ l:ℝ)
 filter_upwards [Metric.tendsto_nhds.mp (calibrated Y H V G τ z q x p) (δ/2) (half_pos u), hp.eventually (gt_mem_nhds (half_pos u)), (widthMeters Y H V G τ).eventually_gt_atTop (b'*2)] with n e h j
 have hy:(bufferedHull Λ l (τ n) {N n}) ⊆ Metric.ball x.ofLp δ:=by
    intro y hy; rcases mem_iUnion₂.mp hy with ⟨b,q,u'⟩; rw [Finset.mem_singleton.mp q] at u'; obtain ⟨z,hz,rfl⟩:=u'
    rw [Metric.mem_ball]; refine (dist_triangle (toMatterUnits z) (L n (N n)) _).trans_lt ?_; have he:dist (toMatterUnits z) (L n (N n))≤ A n:=by
       rw [dist_eq_norm,pi_norm_le_iff_of_nonneg]; exact (fun j=>(shifted_shield ..).mp hz j)
       exact mul_nonneg (by positivity) (gaugeMesh_pos ..).le -- arguments
    linarith
 refine ⟨(supported_iff Λ l (τ n) _).2 ((hy.trans v).trans inter_subset_left),fun x hx=>?_⟩; have hu:|landN P x|+(r:ℝ)< b':=(v (hy hx)).2; exact hu.trans (lt_div_iff₀ (by norm_num)|>.2 j)
open MeterFunding
private lemma unwrapping(z':ℕ→ Cover)(x y:Gaia)(u:Tendsto (fun n=>Onyx.riseX (R n) (z n)) atTop (𝓝 x))(v:Tendsto (fun n=>Onyx.riseX (R n) (z' n)) atTop (𝓝 y)): ∀ᶠ n in atTop,Lattice.lift (wrap (More (Journey.side Y (i (G.rows n)) (τ n))) (nodeC (z' n))-wrap (More (S n)) (N n)) = nodeC (z' n) - N n :=by
 let F(n):= N n; let T' (n:ℕ):= nodeC (z' n); let d(n:ℕ):=L n (F n)-L n (T' n)
 let A(n):=gaugeMesh Λ (τ n); let ℓ(n):=More (S n); let δ(i:Axis):=1+|(x.ofLp-y.ofLp) i| *2
 have ht:Tendsto d atTop (𝓝 (x.ofLp-y.ofLp)):= (calibrated Y H V G τ z q x u).sub (calibrated Y H V G τ z' q y v)
 have hp(a:Axis):∀ᶠ n in atTop, - ((ℓ n).val:ℤ)<2*((T' n-F n) a) ∧ 2*((T' n-F n) a)≤(ℓ n).val:=by
    have hu:Tendsto (fun n=>|d n a| * 2) atTop (𝓝 (δ a-1)):= by unfold δ; rw [add_comm 1,add_sub_cancel_right]; exact ((tendsto_pi_nhds.mp ht a).abs).mul_const _
    filter_upwards [hu.eventually (gt_mem_nhds (show δ a-1<δ a by linarith)),(widthMeters Y H V G τ).eventually_gt_atTop (δ a)] with n h v
    have hp:0<A n:=gaugeMesh_pos ..; have hx:d n a=((F n a:ℝ)-T' n a) * A n := by rw [_root_.sub_mul]; rfl

    have he: |((F n a:ℝ)-T' n a)| * 2 < (ℓ n).val:=by
       apply lt_of_mul_lt_mul_right _ hp.le; have ht: δ a < A n * ((ℓ n).val:ℝ):= v; change |d n a| *2< _ at h; rw [hx,abs_mul,abs_of_pos hp] at h; linarith
    have hv:= (le_abs_self (((F n a:ℝ)-T' n a))); have hu:= neg_le_abs (((F n a:ℝ)-T' n a))
    refine ⟨by exact_mod_cast (show -((ℓ n).val:ℝ)<2*((T' n a:ℝ)-F n a) from by linarith),by exact_mod_cast (show 2*((T' n a:ℝ)-F n a) ≤ (ℓ n).val from by linarith)⟩
 exact (eventually_all.mpr hp).mono fun i v=> Lattice.lift_eq_iff.mpr ⟨(map_sub ..).symm,v⟩
noncomputable def twinNode (P:Ramp)(x:Cover) := nodeC ((Hygrometry.whisper P).cell x)


omit V q G
lemma prospects (U:RSpace)(t:U∈ SkyAcres P r): U∈P.s.act '' Acres P r:=⟨P.s.act U,acre_S_N P r (Set.mem_image_of_mem _ t),P.act_act U⟩
lemma singleton_wrap (k:Cover): Satin.region ({k}) (Journey.side Y m s) = {wrap (More (Journey.side Y m s)) k}:= image_singleton _ _
lemma twin_wrap (Q:Side)(x:Cover) : ((Satin.region {nodeC x} Q).image (P.plan.anon Q))= Satin.region {twinNode P x} Q:=by
 rw [Satin.region, Finset.image_singleton, Finset.image_singleton, Satin.region,Finset.image_singleton,Shape.anno,P.moved_wing]
 rfl
include V q G
lemma paid_space (x: Gaia)(p:(r:ℝ)<x P.a+x P.b)(u:Tendsto (fun n=> Onyx.riseX (R n) (z n)) atTop (𝓝 x)): ∀ᶠ n in atTop,∀ f:Mark (Journey.side Y (i (G.rows n)) (τ n)), AtSupport false {wrap (More (S n)) (N n)} f → CanInspect Y (i (G.rows n)) (τ n) P r {nodeC (z n)} {twinNode P (z n)} f := by
 let F := (Hygrometry.whisper P).cell ∘ z; let a := land_tilt P x; have hv: (P.s.act '' Acres P r)= SkyAcres P r:= Set.Subset.antisymm (acre_N_S ..) (fun _=>prospects P r _)
 have he:= allowance Y H V G P r τ z q x (Acres P r) p (isOpen_lt continuous_const (landNp P)) u
 have H₀:= budget_grant Y H V G τ q; have hp:Tendsto (fun n=>Onyx.riseX (R n) (F n)) atTop (𝓝 a):=by
    apply (trace_iff H₀ F _).1; change Tendsto (fun n=>Hygrometry.traceV _ ((Hygrometry.whisper P).cell _)) atTop (𝓝 a); simp_rw [here_tilts]; exact lands_tilt _ _ ((trace_iff H₀ z x).2 u)
 have ht:= allowance Y H V G P r τ F q a _ (show a.ofLp∈SkyAcres P r from (hv ▸ (show a.ofLp∈P.s.act '' Acres P r from ⟨x.ofLp,p,rfl⟩))) (isOpen_lt (landNp P) continuous_const) hp; rw [←hv] at ht
 filter_upwards [he,ht,unwrapping Y H V G τ z q F x a u hp, unwrapping Y H V G τ F q z a x hp u] with n q₀ p e w
 intro f k; let U:Finset Cover:= {N n}; have hb:U={N n}:= rfl; let T:Finset Cover := {nodeC (F n)} -- type tune
 have hF:AtSupport false (Satin.region U (Journey.side Y (ξ n) (τ n))) f:= by rwa [hb,singleton_wrap]
 have hrF:=P.term_marked hF
 change CanInspect Y (ξ n) (τ n) P r U T f
 refine ⟨hF,twin_wrap P _ _ ▸ hrF, q₀,p,?_, PhaseChoice.separatedPhys p.1 q₀.1 (Disjoint.preimage _ (unpaired P r))⟩
 intro x u y v; simp only [T,hb, Finset.mem_union,Finset.mem_singleton] at u v; rcases u with rfl|rfl <;> rcases v with rfl|rfl <;> first | exact w | exact e | simp
end Therapies
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
