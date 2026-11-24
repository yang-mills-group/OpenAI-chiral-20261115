import YM.SU5.Reconstruction.Brazier.Purchase
/-! SINGLE deployment of pointing χ surveys. CHosen cofinally in horizon and menu and fees, keeping all queries (pointwise algebra not enough) normalized. Provide exact support receipt by just checking wallet & menu and, for every deployment, spends the costs while staying on the inherited cone. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Px" => LightBudget.prepaid Y H V G j C
namespace Path
open Tarmac Fortune Fervor LightBudget
-- allow any schedule.Calculate directly on support and norm closest to input
variable {Tt:ℕ → ℕ → Tariff} {tv:ℕ → Tariff} (X':Fashion Y H i k I E L B Tt tv)
def Exhaust (T:ℕ→ Finset Tarmac): Prop:= ∀ a,∀ᶠ t in atTop,a∈ T t
def CalibratedCost (g e:ℕ→ℝ): Prop:= Tendsto g atTop atTop ∧ (∀ i,0<g i) ∧ Tendsto e atTop (𝓝 0) ∧ ∀ i,0<e i
local notation "ρ" n:max=> i (G.rows n)
local notation "β" n:max=> k (G.columns n)
variable (T:ℕ→Finset Tarmac) (g e:ℕ→ℝ)
-- choose at stage AFTER all prior estimates. actual payments along the inherited $G$ history, take one.And offers remain valid for any yet-later readings with THAT gate.
structure Salvo (r:ℕ→Hearth Y H G j)(t:ℕ→ℕ): Prop where
 late : StrictMono t
 scans (n):n≤(r n).roof
 authorize : ∀ n k, t n ≤ k → Routing Y H V G Z j C χ (T n) (g n) (e n) (ρ k) (β k) (r n)
lemma furnishing (p:CalibratedCost g e)(Q:ℕ→ℕ) :∃ (r:ℕ→Hearth Y H G j) (t:ℕ→ℕ), Salvo Y H V G X'.toExhibition j C χ T g e r t ∧ ∀ i,Q i ≤ (r i).roof ∧ Q i ≤ t i:=by
 choose r hr h using fun i=> available Y H V G j C χ (T i) (g i) (e i) X' (p.2.1 i) (p.2.2.2 i) (max (Q i) i) -- arg order check
 choose n hn using fun i=> eventually_atTop.mp (h i)
 let B₁(i:ℕ):=max (Q i) (n i)
 let t:ℕ→ℕ:=Nat.rec (motive:=fun _=>ℕ) (B₁ 0) (fun i k=> max (k+1) (B₁ (i+1))); have Ht(i:ℕ): t (i+1)=max (t i+1) (B₁ (i+1)):= rfl
 have hu(i): B₁ i ≤ t i:= by cases i with| zero=> exact le_rfl| succ i=> rw [Ht]; exact le_max_right ..
 refine ⟨r,t,⟨strictMono_nat_of_lt_succ fun i=>?_,fun i=>(le_max_right ..).trans (hr i),fun i s p=> hn i _ ((le_max_right (Q i) (n i)).trans ((hu i).trans p))⟩,fun i=> ⟨(le_max_left ..).trans (hr i), (le_max_left (Q i) (n i)).trans (hu i)⟩⟩
 rw [Ht]; exact Nat.lt_succ_self _|>.trans_le (le_max_left ..)
lemma everSchedule : ∃ (T:ℕ→Finset Tarmac)(g e:ℕ→ℝ), Exhaust T ∧ CalibratedCost g e:=by
 classical
 obtain ⟨p,h⟩:= exists_surjective_nat Tarmac -- name
 refine ⟨(fun n=> (Finset.Iic n).image p),(fun i=>(i:ℝ)+1), (fun i=>propeller i), fun a=>?_,⟨?_,fun i=>by positivity, propeller_fades,fun i=>by unfold propeller; positivity⟩⟩
 · obtain ⟨i,rfl⟩:=h a; exact (eventually_ge_atTop i).mono fun j h=> Finset.mem_image.mpr ⟨i,Finset.mem_Iic.mpr h,rfl⟩
 exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
-- Recover χ reader as one map, not an assertion about recurrence with no gate.
noncomputable def will (x: FiniteGaugeDataPoly (tent Y H)): ℂ:= osValue Y H V G j C χ ⟨realize Y H Z x, always_realizes Y H V G Z x⟩
lemma will_mark (x:Dome (tent Y H))(s:ℕ) (p:pinhole (Dome K) s x∈FiniteGaugeDataPoly (tent Y H)): will Y H V G Z j C χ ⟨pinhole _ s x,p⟩=oneAt Y H V G j C χ s x:= by
 unfold will; rw [show (⟨_,always_realizes Y H V G Z _⟩: D false univ)=_ from (Subtype.ext (one_realized Y H V G Z s x p) : (⟨_,always_realizes Y H V G Z _⟩:D false univ)=⟨ticket Y H G s x,ticket_loose ..⟩)]; exact os_ticket_val .. -- tune metavars
lemma will_bill {s:ℕ}(x:FiniteGaugeDataPoly (tent Y H))(p:x.val∈ shorter (Dome (tent Y H)) s):
    will Y H V G Z j C χ x=receives Y H V G Z j C χ s x.val:=by
 unfold will; rw [show (⟨_,always_realizes Y H V G Z x⟩: D false univ)=_ from (Subtype.ext (realize_ticket Y H V G Z s x p): (⟨_,always_realizes Y H V G Z x⟩:D false univ)=⟨ticket Y H G s (vistaFinish Y H s Z x.val),ticket_loose ..⟩)]; exact os_ticket_val ..
lemma will_across (x:FiniteGaugeDataPoly (tent Y H))(d:Axis)(D':Arena Y H G.history.circuit d 0 false) :
    will Y H V G Z d D' (displacement Y H V G.history G.clipped j false C χ d D') x= will Y H V G Z j C χ x:=by unfold will; rw [os_across] -- proof_irrel
variable {r:ℕ→Hearth Y H G j}{t:ℕ→ℕ} (s: Salvo Y H V G Z j C χ T g e r t)(p:Exhaust T)(h:CalibratedCost g e)
include s p h
lemma dual (a:Tarmac){ε:ℝ}(v:0<ε): ∀ᶠ l₁ in atTop, a∈ T l₁ ∧ ∀ (n:ℕ), t l₁ ≤ n → ∀ x:FiniteGaugeDataPoly (tent Y H),∀ b:ℝ, Pocket (tent Y H) a.book a.roof b x.val →
  ‖scored Y H G j (i (G.rows n)) (k (G.columns n)) (r l₁) x.val-will Y H V G Z j C χ x‖ ≤ b*ε:=by -- replace k symbol shadow
 filter_upwards [h.2.2.1.eventually (gt_mem_nhds v),p a] with l' hx t'
 refine ⟨t',fun n η x b f=>?_⟩
 rw [will_bill Y H V G Z j C χ x f.funded]; exact (((s.authorize l' n η).body a t' x.val b f)).trans (mul_le_mul_of_nonneg_left hx.le f.priced)
lemma marker_purchased (a:Tarmac) : ∀ᶠ l' in atTop, ∀ n, t l' ≤ n → Sightline Y H G j (r l') (g l') a ∧ Hearth.LongReach Y H G j (r l') a (i (G.rows n)):= (p a).mono fun i h n v=> (s.authorize i n v|>.clearance a h)
lemma atStake (x : FiniteGaugeDataPoly (tent Y H)) : Tendsto (fun l'=> scored Y H G j (i (G.rows (t l'))) (k (G.columns (t l'))) (r l') x.val) atTop (𝓝 (will Y H V G Z j C χ x)):=by
 obtain ⟨a,h',b,t'⟩:= Tarmac.received Y H ((questions_top_loose (Λ:=Λ) (l:=l)).symm ▸ (x.property: x.val∈ FiniteGaugeDataPoly (tent Y H)) : x.val∈ questions Λ l K false Set.univ) -- tune `questions`
 apply Metric.tendsto_nhds.mpr; intro δ he
 let d:= δ/(b+1); have ht:= t'.priced
 have hd:0<d:=by unfold d; positivity
 refine (dual Y H V G Z j C χ T g e s p h a hd).mono fun i ⟨_,y⟩=>?_
 rw [dist_eq_norm]; apply (y (t i) le_rfl x b t').trans_lt; unfold d; field_simp; linarith
end Path
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
