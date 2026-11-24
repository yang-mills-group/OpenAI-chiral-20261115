import YM.SU5.Reconstruction.Brazier.Band
/-! The thermodynamic χ criterion, scoped.Holding.S.Book. This is a true expenditure.W.Step implementation. -/
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
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
open Hearth Fervor
namespace Fortune
variable (T:Finset Tarmac)(g e:ℝ)
local notation "ℵ" n:max=> receives Y H V G Z j C χ n
local notation "rχ"=> Hearth Y H G j
/-- Include transfers before taking sharp f values with linear script.P.Not requiring this map to be a positive functional at that finite partner. -/
noncomputable def scored (m u:ℕ)(r:Hearth Y H G j) : Cloud (Dome (tent Y H))→ₗ[ℂ] ℂ:=
 (taking Y H m u (r.spanMark Y H G j))⁻¹ • ((taking Y H m u).comp (LinearMap.mulRight ℂ (r.spanMark Y H G j)))
@[simp] lemma interpreting (m u:ℕ)(r:Hearth Y H G j)(x:Cloud (Dome (tent Y H))):
 scored Y H G j m u r x=taking Y H m u (x*r.spanMark Y H G j) / taking Y H m u (r.spanMark Y H G j):=by unfold scored; simp [div_eq_mul_inv]; ring
abbrev scopeAir (r:Hearth Y H G j)(m:ℕ) : Prop:= ∀ n, PhaseChoice.FullDistances (volumeAround Λ l n (r.facePlate Y H G j)) (Journey.side Y m (r.roof+n))
structure Routing (m u:ℕ)(r:Hearth Y H G j): Prop where
 finance : Tapestry.Pay Y r.roof m u
 actual : scopeAir Y H G j r m
 far : g < (r.height:ℝ)
 clearance : ∀ a∈T,Sightline Y H G j r g a ∧ LongReach Y H G j r a m
 solvent : taking Y H m u (r.spanMark Y H G j)≠0
 interior : ‖taking Y H m u (r.spanMark Y H G j)-1‖≤ e
 body : ∀ a∈T,∀ x: Cloud (Dome (tent Y H)),∀ c:ℝ,Pocket (tent Y H) a.book a.roof c x→
          ‖scored Y H G j m u r x-receives Y H V G Z j C χ a.roof x‖ ≤ c*e

private theorem skew (x y z:ℂ) {M d:ℝ}(h:0≤M)(he:‖z‖≤ M)(k:4*d ≤ 1)(hx: ‖x-z‖≤2*d)(hz:‖y-1‖ ≤ 2*d) : ‖x/y-z‖≤ (4+4*M)*d := by
 have hk:= norm_sub_norm_le (1:ℂ) y
 have hy : 1/2 ≤ ‖y‖ := by rw [norm_one,norm_sub_rev] at hk; linarith
 have H:y≠0:=norm_pos_iff.mp (by linarith)
 rw [show x/y-z=(x-z*y)/y from (by field_simp [H]),norm_div]
 have hD : 0≤d:=by linarith [norm_nonneg (y-1)]
 apply (div_le_iff₀ (by linarith)).2
 have hu : x-z*y=x-z+z*(1-y):=by ring
 rw [hu]; apply (norm_add_le ..).trans; rw [norm_mul,norm_sub_rev 1]
 refine le_trans (add_le_add hx (mul_le_mul he hz (norm_nonneg _) h)) ?_
 apply le_trans (le_of_eq (show 2*d+M*(2*d)=(4+4*M)*d*(1/2) by ring)) (mul_le_mul_of_nonneg_left hy (by positivity))

lemma cost_linear (K':Calibration) (a:Tarmac)(F G':Cloud (Dome K') →ₗ[ℂ] ℂ)(e:ℝ) (p:0<e)(W:∀ x:Cloud (Dome K'), Pocket K' a.book a.roof 1 x→ ‖F x-G' x‖ ≤ e){c:ℝ} (x:Cloud (Dome K'))(h:Pocket K' a.book a.roof c x): ‖F x-G' x‖≤ c*e:=by
 have hx(d:ℝ)(p:d>0)(t:d ≥ c) : ‖F x-G' x‖≤ d*e:=by
   let z:ℂ:=(d⁻¹:ℝ); have hv:‖z‖=d⁻¹:=by unfold z; rw [Complex.norm_real,Real.norm_eq_abs, abs_of_pos (inv_pos.mpr p)]
   have hk:= Pocket.shade z (Pocket.fully t h); rw [hv, inv_mul_cancel₀ p.ne'] at hk
   have ht:= W _ hk; rw [map_smul,map_smul,←smul_sub,norm_smul,hv] at ht; exact (inv_mul_le_iff₀ p).1 ht
 rcases h.priced.eq_or_lt with g|g; swap; · exact hx _ g le_rfl
 by_contra! v; rw [←g,zero_mul] at v; have hd : 0 < ‖F x-G' x‖/(2*e):=by positivity
 have Hc:= hx _ hd (g ▸ hd.le); field_simp at Hc; linarith
variable (r:Hearth Y H G j) (a:Tarmac)
local notation "vf"=>spanMark Y H G j r
local notation "jz" i:max k:max=>taking Y H i k
local notation "op"=>vistaTake Y H Z
local notation "ir₀" n:max=> i (G.rows n)
local notation "uv₀" n:max=> k (G.columns n)
-- numeric criterion. use on $D$ (not bare exhibition, need chosen Fashion for some). Scope exact.
variable {S:ℕ → ℕ → Tariff} {s:ℕ → Tariff}(E':Fashion Y H i k I E L B S s)
lemma throughput {d:ℝ}(u:0<d){U:BillOfWork}(m:ℕ) : ∀ᶠ t:ℕ in atTop, ∀ (c:ℝ) (x:Cloud (Dome (tent Y H))), Pocket K U m c x→ ‖taking Y H (i (G.rows t)) (k (G.columns t)) x - vistaTake Y H E'.toExhibition x‖≤c*d:=by
 refine ( (G.history.growsA.tendsto_atTop).eventually ( E'.wintering Y H U m d u)).mono fun t z c x p=> ((E'.calculation Y H U m _ _ d z p (G.history.gate t)).2.1).trans_eq (mul_comm d c) -- tune Fashion.calculation
lemma fare_charge {d:ℝ}(u:0<d)(a:Tarmac)(hs:a.roof < r.roof): ∀ᶠ t:ℕ in atTop, ∀ (x:Cloud (Dome (tent Y H))), Pocket K a.book a.roof 1 x→ ‖taking Y H (i (G.rows t)) (k (G.columns t)) (x*r.spanMark Y H G j) - vistaTake Y H E'.toExhibition (x*r.spanMark Y H G j)‖ ≤ d:=by
 obtain ⟨b,hv,h⟩:= Note.promotion a K hs (r.gate Y H G j) (r.faceBudget Y H G j) -- membership θ.D.
 refine (throughput Y H G E' (show 0< d/(b+1) by positivity) (U:=update a.book r.roof (r.facePlate Y H G j)) r.roof).mono fun t p x v=>?_
 rw [←r.gratuity]; refine le_trans (p _ _ (h 1 x v)) ?_; rw [one_mul]; field_simp; linarith
lemma base_charge {d:ℝ}(u:0<d) : ∀ᶠ t:ℕ in atTop, ‖taking Y H (i (G.rows t)) (k (G.columns t)) (r.spanMark Y H G j)-vistaTake Y H E'.toExhibition (r.spanMark Y H G j)‖≤ d:= (Metric.tendsto_nhds.mp (value_along Y H G E' ⟨_,questions_polynomials (r.funding Y H G j)⟩) _ u).mono fun i h=> by rw [← dist_eq_norm]; exact h.le -- args
lemma spend {d M:ℝ}(w:ℕ) (pe:Challenge Y H V G E'.toExhibition j C χ w T r g d) (u:0<d)(q0:0≤M)(h:BoundBooks Y H V G E'.toExhibition j C χ T M)(Hₑ:4*d ≤ 1)(p:(4+4*M)*d≤ e):
 ∀ᶠ t in atTop, Routing Y H V G E'.toExhibition j C χ T g e (ir₀ t) (uv₀ t) r:=by
 filter_upwards [G.history.finance r.roof,((V.pick.grow_i.comp G.history.growsA).tendsto_atTop).eventually (unwrapped Y H r.roof (r.facePlate Y H G j)),(eventually_all_finset T).mpr (fun t h=>spare Y H V G j r t),base_charge Y H G j r E' u,(eventually_all_finset T).mpr (fun t ht=>fare_charge Y H G j r E' u t (pe.full t ht|>.futureEntry))] with t Q Z Bi Hb Hu
 let z:= taking Y H (i (G.rows t)) (k (G.columns t)); let o:= vistaTake Y H E'.toExhibition; let W:= z vf; have A' : ‖W-1‖ ≤2*d:= (norm_sub_le_norm_sub_add_norm_sub W (o vf) 1).trans ((add_le_add Hb pe.valFee).trans_eq (two_mul d).symm)
 have he:2*d ≤ (4+4*M)*d:=by nlinarith
 refine ⟨⟨Q.depth,Q.enters⟩,Z,pe.height,fun i t=> ⟨(Station.clearance Y H G j (pe.full i t)), Bi i t⟩,fun hz=>?_, A'.trans (he.trans p),fun i a x c q=>?_⟩
 · rw [show W=0 from hz] at A'; simp only [zero_sub,norm_neg,norm_one] at A'; linarith
 -- scaling; rename hBinder to distinguish
 apply cost_linear K i _ _ e (lt_of_lt_of_le (mul_pos (by norm_num) u) (he.trans p)) ?_ x q
 intro y v; have h': ‖z (y*vf) - receives Y H V G E'.toExhibition j C χ i.roof y‖ ≤2*d:= (norm_sub_le_norm_sub_add_norm_sub _ (o (y*vf)) _).trans ((add_le_add (Hu i a y v) (pe.era i a y v)).trans_eq (two_mul d).symm)
 rw [interpreting]; exact (skew _ W _ q0 (h i a y v) Hₑ h' A').trans p
lemma available (u:0<g)(f:0<e)(b:ℕ) : ∃ r:Hearth Y H G j,b ≤ r.roof∧∀ᶠ t:ℕ in atTop, Routing Y H V G E'.toExhibition j C χ T g e (ir₀ t) (uv₀ t) r:=by
 obtain ⟨w,h,v⟩:= assist (Λ:=Λ) (l:=l) j T
 obtain ⟨M,c,h,u'⟩:= afforded Y H V G E'.toExhibition j C χ w T v
 let d:= min (1/4:ℝ) (e/(4+4*M)); have he:0<d:=lt_min (by norm_num) (by positivity); obtain ⟨r,p,y⟩:= u' d g b he u
 refine ⟨r,p, spend Y H V G j C χ T g e r E' w y he c h ?_ ?_⟩
 · unfold d; linarith [min_le_left (1/4:ℝ) (e/(4+4*M))]
 rw [mul_comm]; exact (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
end Fortune
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
