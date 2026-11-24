import YM.SU5.Aria.Gathering
import YM.SU5.Aria.Orchestral
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "ξ"=>P.laysM
local notation "Γ"=>P.VMark
local notation "X"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "ω"=>P.colorZero j x
local notation "Ω"=>P.heaven j x
local notation "ν"=>P.seasons j x
local notation "ψ"=>P.physicalEnergy j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "τ" r:max=> Real.toNNReal r
local notation "κ"=> P.truck j x
variable {I:Type*}(A:I→P.Apron)(L:List I)(q:I→ Vantage)(p s:ℕ→ I→ P.VMark)
local notation "u₁" p:max=> P.porchY j A p
local notation "v₁" p:max=> P.resignY j A p
local notation "a" p:max F:max=> Apron.time_panel P j p F
local notation "b" p:max F:max=> Apron.time_edge P j p F
lemma frame_booking (t:∀ i∈ L,Tendsto (fun n=> P.laysM (p n i)) atTop (𝓝 (q i)))(ε:ℝ)(e:0<ε): ∀ᶠ n in atTop, FramesAt L (P.laysM ∘ p n) q ε:=by
 filter_upwards [ (Filter.eventually_all_finset L.toFinset).2 (fun i h=>Metric.tendsto_nhds.mp (t i (List.mem_toFinset.mp h)) ε e)] with n u; exact fun i h=> u i (List.mem_toFinset.mpr h)
lemma trucking_fixed (y z:P.VMark)(h:∀ i,i≠j → y i=z i): P.truck j x y=P.truck j x z:= congrArg ((P.voyageF j x).raw (look j)) (show y ∘ (Subtype.val : Trans j→Axis)=z ∘ Subtype.val from funext fun i:Trans j=>h i.val i.property)
lemma charter_stable (y z:Γ)(h:∀ i,i≠j→y i=z i)(F:(X).Op): P.charter j x y F=P.charter j x z F:=by unfold charter; rw [P.trucking_fixed j x y z h,P.trucking_fixed j x (-y) (-z) fun i v=>by rw [Pi.neg_apply,Pi.neg_apply,h i v]]
variable (t:P.Turnstile j A L q)(c:∀ i∈L,Tendsto (fun n=> P.laysM (p n i)) atTop (𝓝 (q i)))
   (c':∀ i∈L,Tendsto (fun n=> P.laysM (s n i)) atTop (𝓝 (q i)))
-- Note this pairwise stability does NOT require aligning the characters of projected vs unproj at each plane yet; first just axis property for whole
include c t
lemma approaches_turn : ∀ᶠ n in atTop,P.Turnstile j A L (ξ ∘ p n):= by obtain ⟨ε,t,h⟩:=P.shelter_frame j A L q t; exact (P.frame_booking L q p c _ t).mono fun n y=> h _ y
include c'
local notation "Σπ" r:max=> P.preview j x A L r
lemma close_axis (g:∀ n i,i∈L→∀ k,k≠j→ p n i k=s n i k):
    Tendsto (fun n=>dist (P.preview j x A L (p n)) (P.preview j x A L (s n))) atTop (𝓝 0):=by
 classical
 obtain ⟨D⟩:= choose_curtains (u₁ q) (v₁ q) L (P.turn_no_clones j A L q t) (weaves_sorted _ _ _ t)
 let f:=D.first; let v:=D.last; let R(i:I)(y:Γ):= P.raze j x (A i) (f i) (v i) y
 have tv:∀ i∈L, Tendsto (fun n=>dist (R i (p n i)) (R i (s n i))) atTop (𝓝 0):=by
    intro i e
    let F:= A i; let X'(q:Vantage):=(E (τ (a q F-f i))); let Y(q:Vantage):= E (τ (v i-b q F)); let z:=F.engine P j x; let w₀(n:ℕ):= P.charter j x (p n i) (F.engine P j x)
    have h₀: f i < a (q i) F:=D.inside i e; have hv: b (q i) F< v i := D.outside i e
    have hx:ContinuousAt X' (q i):=(steam_contPos (ψ) _ (sub_pos.mpr h₀)).comp (f:=fun t:Vantage=>a t F-f i) (((continuous_apply j).sub continuous_const).sub continuous_const).continuousAt
    have hy:ContinuousAt Y (q i):=(steam_contPos (ψ) _ (sub_pos.mpr hv)).comp (f:=fun t:Vantage=>v i-b t F) (continuous_const.sub ((continuous_apply j).add continuous_const)).continuousAt
    have pk:= c i e; have sk:=c' i e
    let t(n:ℕ):=max (dist (X' (ξ (p n i))) (X' (ξ (s n i)))) (dist (Y (ξ (p n i))) (Y (ξ (s n i))))
    have ht:Tendsto t atTop (𝓝 0):=by simpa [t] using (((hx.tendsto.comp pk).dist (hx.tendsto.comp sk)).max ((hy.tendsto.comp pk).dist (hy.tendsto.comp sk)))
    have he:Tendsto (fun n=> t n * ‖z‖ + ‖z‖*t n) atTop (𝓝 0):=by simpa using (ht.mul_const ‖z‖).add (ht.const_mul ‖z‖)
    apply squeeze_zero (fun n=>dist_nonneg) _ he; intro n; change dist ((X' _).comp ((w₀ n).comp (Y _))) _≤ _
    have y₂:=wrap_est (w₀ n) (X' (ξ (s n i))) (X' (ξ (p n i))) (Y (ξ (s n i))) (Y (ξ (p n i))) ((ψ).shrinks _) ((ψ).shrinks _) (le_max_left (dist (X' (ξ (p n i))) (X' (ξ (s n i)))) (dist (Y (ξ (p n i))) (Y (ξ (s n i))))) (le_max_right ..) (P.charter_pay ..)
    change dist _ ((X' _).comp ((P.charter j x (s n i) z).comp (Y _))) ≤ _; rw [←P.charter_stable j x _ _ (g n i e)]; exact y₂
   -- tune
 have he:∀ i∈ L, f i<(u₁ q) i∧(v₁ q) i < v i:= fun i e=> ⟨D.inside i e,D.outside i e⟩
 obtain ⟨ε,jε,hp'⟩:=P.curtains_stay j A L q he
 have T:= troupe_cost (fun i=>‖(A i).engine P j x‖) (fun n i=>R i (p n i)) (fun n i=> R i (s n i)) L (fun i _ n=> ⟨P.raze_pay ..,P.raze_pay ..⟩) tv
 apply (comfort (P.ColorHil j x) _ _ ω T).congr'
 filter_upwards [P.frame_booking L q p c _ jε,P.frame_booking L q s c' _ jε] with n u' h
 exact (congrArg₂ dist (P.pill_preview j x A L (p n) _ _ (hp' _ u') D.joins) (P.pill_preview j x A L (s n) _ _ (hp' _ h) D.joins)).symm
omit t c c'
structure Plenum : Prop where
 busy : ∀ i:Axis,∃ T: List I,L.Perm T∧P.Turnstile i A T q
include t c c'
omit t in
lemma compares_one (y z:Axis)(v:P.Turnstile z A L q)(e:P.Plenum A L q)(g:∀ n i,i∈L→∀ k,k≠y→ p n i k=s n i k):
    Tendsto (fun n=>dist (P.preview z (P.advocate j x z) A L (p n)) (P.preview z (P.advocate j x z) A L (s n))) atTop (𝓝 0):=by
 obtain ⟨T,hp,Y⟩:=e.busy y; have t:= P.close_axis y (P.advocate j x y) A T q p s Y (fun i t=> c i (hp.mem_iff.mpr t)) (fun i t=> c' i (hp.mem_iff.mpr t)) (fun n i t=> g n i (hp.mem_iff.mpr t)); apply t.congr'
 filter_upwards [P.approaches_turn z A L q p v c,P.approaches_turn z A L q s v c',P.approaches_turn y A T q p Y (fun i t=> c i (hp.mem_iff.mpr t)), P.approaches_turn y A T q s Y (fun i t=> c' i (hp.mem_iff.mpr t))] with n y₀ t h z'
 exact (congrArg₂ dist (P.match_forecast j x A L z y _ hp (p n) y₀ h) (P.match_forecast j x A L z y _ hp (s n) t z')).symm
omit t c c'
-- hybrid coordinates
def switchTide (v:List Axis)(F G: P.VMark): Γ:= v.foldr (fun i y=> Function.update y i (F i)) G
lemma switches_mem (v:List Axis)(α β:Γ) (p:Axis) : P.switchTide v α β p= if p∈v then α p else β p:=by
 induction v with
 | nil=>simp [switchTide]
 | cons i v ih=> change Function.update (P.switchTide v α β) i (α i) p=_; by_cases h:p=i <;> simp [h,ih]
include c c'
lemma switches_land (v:List Axis):∀ i∈L,Tendsto (fun n=> ξ (P.switchTide v (p n i) (s n i))) atTop (𝓝 (q i)):=by
 intro i e; apply tendsto_pi_nhds.mpr; intro k; by_cases h:k∈v
 · have hx:=tendsto_pi_nhds.mp (c i e) k; apply hx.congr; intro n; unfold laysM; rw [P.switches_mem,if_pos h]
 have hx:=tendsto_pi_nhds.mp (c' i e) k; apply hx.congr; intro n; unfold laysM; rw [P.switches_mem,if_neg h] -- shadows include statements typo for switches_mem binder c?
lemma standingBy (y:Axis)(w:P.Turnstile y A L q)(e:P.Plenum A L q)(v:List Axis):
    Tendsto (fun i=>dist (P.preview y (P.advocate j x y) A L (fun t=> P.switchTide v (p i t) (s i t))) (P.preview y (P.advocate j x y) A L (s i))) atTop (𝓝 0):=by
 induction v with
 | nil=> simp [switchTide]
 | cons i v h=>
    let W(z:List Axis)(n:ℕ)(i:I):=P.switchTide z (p n i) (s n i); let k:= P.preview y (P.advocate j x y) A L; have ht:= P.compares_one j x A L q (W (i::v)) (W v) (P.switches_land L q p s c c' _) (P.switches_land L q p s c c' _) i y w e fun n j h z u=> Function.update_of_ne (show z≠i from u) _ _ -- arg order
    have he: Tendsto (fun n=>dist (k (W (i::v) n)) (k (W v n))+dist (k (W v n)) (k (s n))) atTop (𝓝 0):= by
       change Tendsto (fun n=>dist (k (W v n)) _) _ _ at h
       change Tendsto (fun n=>dist (k _) _) _ _ at ht
       convert ht.add h using 1; rw [add_zero]
    exact squeeze_zero (fun _=>dist_nonneg) (fun n=> dist_triangle _ (k (W v n)) _) he
lemma compares_all (y:Axis)(w:P.Turnstile y A L q)(e:P.Plenum A L q):
    Tendsto (fun i=>dist (P.preview y (P.advocate j x y) A L (p i)) (P.preview y (P.advocate j x y) A L (s i))) atTop (𝓝 0):=by
 apply (P.standingBy j x A L q p s c c' y w e Vacancy.ordinate).congr; intro i; rw [show (fun t=>P.switchTide Vacancy.ordinate (p i t) (s i t))=p i from funext fun t=>funext fun j=> (P.switches_mem ..).trans (if_pos (Vacancy.ordinates j))]
-- raw canonical values, NO jitter needed now, no time/momentum damping. `e` dependent true P.
omit c'
lemma entirely (J:P.Ellis j x)(y:Axis)(w:P.Turnstile y A L q)(u:P.Plenum A L q): Tendsto (fun n=>P.preview y (P.advocate j x y) A L (p n)) atTop (𝓝 (P.memorial y (P.advocate j x y) A L q)):=by
 classical
 let K:= J.regimen P j x L p; let X':= P.preview y (P.advocate j x y) A L; have he: Tendsto (fun n=>dist (X' (p n)) ((K n).mean X')) atTop (𝓝 0):=by
    refine Casting.jitter_zero X' (fun n=> X' (p n)) K (fun v h=>?_)
    apply P.compares_all j x A L q p v c _ y w u; intro i e; refine Metric.tendsto_nhds.mpr (fun ε a'=>?_); exact (J.recoversPose P j x L q p c ε a').mono (fun n t=> (Mist.holds_at _).mp t _ (h n) i e)
 apply (J.draw_league P j x A L q p c y w).congr_dist; exact he.congr fun i=>dist_comm ..
omit c
lemma entirely_now (J:P.Ellis j x)(y:Axis)(p:I→Γ)(w:P.Turnstile y A L (P.laysM∘p))(u:P.Plenum A L (P.laysM∘p)): P.preview y (P.advocate j x y) A L p=P.memorial y (P.advocate j x y) A L (P.laysM∘p):= tendsto_nhds_unique tendsto_const_nhds (P.entirely j x A L _ (fun _=>p) (fun i _=>tendsto_const_nhds) J y w u)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.entirely
