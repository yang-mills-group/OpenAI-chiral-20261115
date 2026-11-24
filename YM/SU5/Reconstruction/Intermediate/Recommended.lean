import YM.SU5.Reconstruction.Intermediate.Ambition
/-! # Angular procurement. open input. -/
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
local notation "QB" => Harbour.screen Y m t T F z
local notation "pB" j:max => partitionZ (QB j) Λ.U ((Y.voyage m).CapeT j)
local notation "fe" => consultancy Y (i:=m) (k:=t) (s:=T) (F:=F) z
local notation "wb" i:max=> Harbour.earns Y m t T F z i
variable {U V' : Finset Cover}
local notation "Bu" n:max=> volumeAround Λ l n U
local notation "Bv" n:max=> volumeAround Λ l n V'
local notation "i'" n:max=> i (G.rows n)
local notation "𝒪" s:max=> Py.buoy (Y.ivory s)
variable (x:Dome (tent Y H))
variable {ε:ℝ}
private lemma stamp_learn (p:x∈ insideAt Λ l (tent Y H) true (Acres P r) s) (tK:Rectitude Y H V G P r)(g:0<ε): ∀ᶠ n in atTop,-ε≤ (ticketPrice Y H (i (G.rows n)) (k (G.columns n)) s P x).re := by
 let z:= windTilt P K x * x; let w:=ticket Y H G s x
 have h:w∈D true (Acres P r):=ticket_mem Y H G p
 have v:gust P K w*w ∈ µ:= domain_loose Y H G univ (pay_your Y H V G P r h h)
 have he: ticket Y H G s z= gust P K w*w:=by unfold w; rw [gust_ticket Y H V G P]; exact ticket_separated Y H G (protects P s true (Acres P r) _ p) p (unpaired P r)
 have ht:0≤ (E s z.val).re:= by
    let a':= tK ⟨w,h⟩ v
    refine ((reflection_root Y H V G P w v).1 a').trans ?_
    refine le_of_eq ?_
    rw [show (⟨_,v⟩:µ) = ⟨ticket Y H G s z,ticket_loose ..⟩ from Subtype.ext he.symm,course_ticket_val]
 have ha: Tendsto (fun n:ℕ=>(ticketPrice Y H (i (G.rows n)) (k (G.columns n)) s P x).re) atTop (𝓝 (E s z.val).re):= Complex.continuous_re.continuousAt.tendsto.comp (PhaseChoice.final_limit Y H G s z.val ((marque ..).1 z.property))
 exact (ha.eventually (lt_mem_nhds (lt_of_lt_of_le (neg_lt_zero.mpr g) ht))).mono fun _ v=> v.le
private lemma shift_receipt {x y:ℂ}(h:‖x-y‖≤ε) : x.re - ε ≤ y.re ∧ y.re-ε ≤ x.re := by
 have e:= abs_le.mp ((Complex.abs_re_le_norm (x-y)).trans h); rw [Complex.sub_re] at e; exact ⟨by linarith [e.2],by linarith [e.1]⟩
local notation "ρ" n:max => climb Y m t s T F z (basement Y H m s x) n
private lemma on_sponsor {T:ℕ} {F} (w:Wraps Y H s P r U V' x m) (e:0<ε)(a:Surrounds Y m t T F P r) (h:s< Py.buoy (Y.ivory t)) (v:∀ z:Intermediate.Room T, Harbour.phaseMoney Y m t T F z → Accurate Y H m t s T F z P x ε): Ambition Y H m t s P x ε:= by
 obtain ⟨T',rfl⟩:=Nat.exists_eq_add_of_le (h.le.trans a.2.2.1)
 obtain ⟨u,e',hv,p⟩:= a; obtain ⟨z,g⟩:= possible Y e' u
 have ht: Accurate Y H m t s (s+T') F z P x ε:= v z g
 obtain ⟨hw,hV,-⟩:= audit_spend Y H m t s (s+T') F z P r x w e' u g T' le_rfl
 have hk:= ht.qualify; rw [launchGram_eq] at hk
 refine ⟨T',F,z,⟨hv,e',u,g,hk, le_trans (le_of_lt (neg_lt_zero.mpr e)) (p _ _ _ _ hk hw hV)⟩⟩
include V
lemma uniform_implies (e:SponsoredHigh Y H G P r): Adaptive Y H G P r :=by
 intro s x p ε u; obtain ⟨U,V',w⟩ := formed Y H V G s P r x p
 refine (e.and_eventually ((accessible Y H V G s P x _ u).and w)).mono fun n t=>?_
 obtain ⟨⟨k₀,F,a⟩,⟨q,h⟩,b⟩:= t
 exact on_sponsor Y H (i (G.rows n)) (k (G.columns n)) s P r x b u a q (h _ a.2.1 a.2.2.1 _ a.1)
omit V
private lemma permutes (w:Wraps Y H s P r U V' x m) {d:ℕ}{F z} (a:Arriving Y H m t s P x d F z (ε/2)) (u:Accurate Y H m t s (s+d) F z P x (ε/2)): -ε≤ (ticketPrice Y H m t s P x).re:= by
 have ht:= (audit_spend Y H m t s (s+d) F z P r x w a.chart a.quota a.got d le_rfl).2.2; have p:= a.sufficesAt; rw [sessionPrice,←ht] at p; have h:= (shift_receipt u.norm_current).2; linarith
include V in
lemma sourced (p:Adaptive Y H G P r) : Rectitude Y H V G P r:= by
 apply born Y H V G P r; intro s f g ε hz
 obtain ⟨U,V',t⟩:= formed Y H V G s P r f g
 refine ((p s f g (ε/2) (half_pos hz)).and_eventually ((accessible Y H V G s P f _ (half_pos hz)).and t)).mono ?_
 rintro n ⟨⟨d,F,z,q⟩,⟨a,b⟩,w⟩; exact permutes Y H (i (G.rows n)) (k (G.columns n)) s P r f w q (b _ q.chart q.high _ q.quota z q.got)

private lemma canArrive (w:Wraps Y H s P r U V' x m) (e:- (ε/2)≤ (ticketPrice Y H m t s P x).re)(v:s ≤ 𝒪 t) (u:∀ F, Harbour.campus Y m t (Py.buoy (Y.ivory t)) F → ∀ z, Harbour.phaseMoney Y m t (𝒪 t) F z → Accurate Y H m t s (𝒪 t) F z P x (ε/2)): Ambition Y H m t s P x ε:= by
 -- Actually may take a blank Corr at intermediate. Not even need parameter-specific F.
 let Gq:Corr (Λ.Ctor (Y.ir m) (𝒪 t)):=0
 have hq:campus Y m t (𝒪 t) (fun _=>Gq):= Intermediate.static (projectA Y m t) _ Λ.δ _ (Charged.zero.mono ((money Y m t).clocks (𝒪 t)).leaf.le)
 have hi:𝒪 t ≤ Y.uv t:= (Py.Rate.LocalLimit.deeper _ _).le -- elaboration
 suffices K': ∀ (d k:ℕ), d=s+k → d=Py.buoy (Y.ivory t) →
         ∀ (F:Intermediate.Room d→ Corr (Λ.Ctor (Y.ir m) d)), campus Y m t d F → Ambition Y H m t s P x ε by
    obtain ⟨d,r⟩:=Nat.exists_eq_add_of_le v; exact K' _ d r rfl _ hq
 intro d k' p l' F kp -- k' notation shadow
 subst d; obtain ⟨z,tz⟩:= possible Y (l'.trans_le hi) kp
 have uh:∀ (d:ℕ), d=Py.buoy (Y.ivory t) → ∀ F, Harbour.campus Y m t d F → ∀ z, Harbour.phaseMoney Y m t d F z → Accurate Y H m t s d F z P x (ε/2):= by rintro _ rfl; exact u
 have hu:= uh _ l' F kp _ tz; have hv:= hu.qualify; rw [launchGram_eq] at hv
 refine ⟨k',F,z,le_of_eq l'.symm,l' ▸ hi,kp,tz,hv,?_⟩
 have h:= (audit_spend Y H m t s _ F z P r x w (l'.trans_le hi) kp tz k' le_rfl).2.2
 rw [sessionPrice,←h]; have hx := (shift_receipt hu.norm_current).1; linarith -- indentation
include V
lemma adaptive_characterization: Adaptive Y H G P r ↔ Rectitude Y H V G P r:=by
 refine ⟨sourced Y H V G P r,?_⟩; intro p s x g ε v; obtain ⟨U,V',b⟩:= formed Y H V G s P r x g
 apply Filter.Eventually.frequently
 filter_upwards [stamp_learn Y H V G s P r x g p (half_pos v), accessible Y H V G s P x _ (half_pos v), b] with n p t w; refine canArrive Y H (i (G.rows n)) (k (G.columns n)) s P r x w p t.1.le (t.2 _ ?_ le_rfl) -- provide height ≤ bound
 exact (Py.Rate.LocalLimit.deeper _ _).le
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened
