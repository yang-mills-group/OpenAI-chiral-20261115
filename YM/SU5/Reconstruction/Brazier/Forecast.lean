import YM.SU5.Reconstruction.Brazier.Venator
import YM.SU5.Reconstruction.Trap.Castle
/-! New single-history invoice. Does not postulate symmetry restoration nor mistake it for a cost already funded; if don't see asymptotic obstruction using THESE actual phase journeys, at these coordinates, then already have physical Light boost backing on that interaction state. Includes at least enough gauges to be legitimate reconstruction on the common Y.

Test comparison uses `Pole` at top explicitly & its stamp‑basis purchases. -/
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
namespace Forecast
open Marshal Tarmac FirstWindows.Brazier.Path LightBudget
variable {T:ℕ→Finset Tarmac}{g e:ℕ→ℝ}
def arenaFees (t:ℕ→ℕ)(r:ℕ→Hearth Y H G j) (k:Axis) (z d:ℝ): Prop :=
  ∀ (b:Axis)(_ : b ≠ k)(n:marks (timeMesh Λ)), 0<(n:ℝ) → (n:ℝ)<d → let u:= Picket.byStamp k b n
    ∀ x:Sky (tent Y H), x∈ Domain Y H G true (flank k z) → ∀ A' B': FiniteGaugeDataPoly (tent Y H),
      A'.val∈ questions Λ l K true (flank k z ∪ mirrorE k 0 '' flank k z) → B'.val∈ questions Λ l K true (flank k z ∪ mirrorE k 0 '' flank k z) →
      realize Y H Z A'= LightBudget.gram k K (LightBudget.shop k K u x) →
      realize Y H Z B'= LightBudget.gram k K (LightBudget.floor k K u x) →
      ∀ ε> (0:ℝ), ∃ᶠ m in atTop, (observed Y H G j t r A'.val m).re ≤ (observed Y H G j t r B'.val m).re + ε
-- repair shadow k.C.ovariance. k here axis explicit? G carries anyway.
variable (a : Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (U':displayAlgebra Y H V G.history G.clipped j false (c j) →⋆ₐ[ℂ] ℂ)
variable (t:ℕ→ℕ)(r:ℕ→Hearth Y H G j) (s:Marshal.Reconstitution Y H V G Z j (c j) U' T g e t r)
local notation "F"=> will Y H V G Z j (c j) U'
local notation "κa"=> displacement Y H V G.history G.clipped j false (c j) U' a (c a)
local notation "f"=> observed Y H G j t r
private lemma limitAsk {X Y':ℕ→ℝ}{x y:ℝ}(p:Tendsto X atTop (𝓝 x))(h:Tendsto Y' atTop (𝓝 y)):
 x ≤ y ↔ ∀ ε>(0:ℝ), ∃ᶠ m in atTop, X m ≤ Y' m + ε:=by
 constructor
 · intro t ε e; have hc:x < y+ε:=by linarith
   exact ((p.eventually_lt (h.add_const ε) hc)|>.mono (fun i h=>h.le)).frequently -- tune p.eventually_lt signature
 intro t; by_contra! v; have he:0<(x-y)/2:=by linarith
 obtain ⟨m,h,q⟩:=((t _ he).and_eventually ((h.add_const ((x-y)/2)).eventually_lt p (by linarith))).exists; exact not_le.mpr q h
include V in
private lemma coveredIx (z:ℝ)(x:Sky (tent Y H))(v:0<z)(b:x∈Domain Y H G true (flank a z)) :
 ∃ B':FiniteGaugeDataPoly (tent Y H), B'.val ∈ questions Λ l K true (flank a z ∪mirrorE a 0 '' flank a z) ∧ realize Y H Z B'= LightBudget.gram a K x:=by
 obtain ⟨U,W,u,w,h',k,r,f',y,c₀,v⟩ := processed Y H G a z x b v -- f notation danger
 have h: LightBudget.gram a K x∈ Domain Y H G true (flank a z ∪mirrorE a 0 '' flank a z):= domain_mono Y H G (union_comm (flank a z) _ ▸ Set.union_subset_union u w) r -- orientation eq substitution
 exact (show LightBudget.gram a K x∈ realize Y H Z '' {v:FiniteGaugeDataPoly (tent Y H) | v.val∈ questions Λ l K true (flank a z∪mirrorE a 0 '' flank a z)} from by rw [realize_covers Y H V G Z]; exact h)
include s
private lemma reward (A' B':FiniteGaugeDataPoly (tent Y H))(x y:Sky (tent Y H))(p:realize Y H Z A'=x)(q:realize Y H Z B'=y)(h:x∈ Domain Y H G false univ) (w:y∈ Domain Y H G false univ):
 (osValue Y H V G a (c a) κa ⟨x,h⟩).re ≤ (osValue Y H V G a (c a) κa ⟨y,w⟩).re ↔ ∀ ε>(0:ℝ), ∃ᶠ m in atTop, (observed Y H G j t r A'.val m).re ≤ (observed Y H G j t r B'.val m).re + ε:=by
 subst x y; rw [os_across]; exact limitAsk (Complex.continuous_re.continuousAt.tendsto.comp (s.news A')) (Complex.continuous_re.continuousAt.tendsto.comp (s.news B'))
lemma tariff {z d:ℝ}(p:0<z) : arenaFees Y H G Z j t r a z d ↔ Ivory Y H V G a (c a) (displacement Y H V G.history G.clipped j false (c j) U' a (c a)) z d:=by
 constructor
 · intro k b u n h hv x v c₀ g k'; -- intro let? Ivory binder
   have hd: coordinates Λ x a∈ Set.Ioi 0:=by
     apply (show 0< (coordinates Λ x a:ℝ) from ?_)
     -- by p.starch
     exact ((show coordinates Λ x∈ConePrice.CostDomain a d from Picket.starch (mainsea Y H V G.history G.clipped a false (c a) κa) ⟨b,u⟩ n h hv)).1
   obtain ⟨e,fV⟩:= budget_legs Y H V G a z v x c₀ hd.le
   obtain ⟨X,g₀,t'⟩:= coveredIx Y H V G Z a z _ p e; obtain ⟨Q,h₀,k0⟩:=coveredIx Y H V G Z a z _ p fV
   exact (reward Y H V G Z j a c U' t r s X Q _ _ t' k0 g k').2 (k b u n h hv _ c₀ X Q g₀ h₀ t' k0)
 intro k b u n h hv x v c₀ A' B' g k' sA sB -- lets
 exact (reward Y H V G Z j a c U' t r s A' B' _ _ sA sB (sA ▸ always_realizes Y H V G Z A') (sB ▸ always_realizes Y H V G Z B')).1 (k b u n h hv _ c₀ _ _)
lemma critical (z d:ℝ)(p:0<z)(b:0<d): BoostBacking Y H V G c j U' ↔ ∀ a:Axis, arenaFees Y H G Z j t r a z d := by
 rw [← real_boost_purchase Y H V G c j U' p.le b]; constructor; · intro h a; exact (tariff Y H V G Z j a c U' t r s p).2 (h.purchases a)
 intro h; exact ⟨fun a=> (tariff Y H V G Z j a c U' t r s p).1 (h a)⟩
end Forecast
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
