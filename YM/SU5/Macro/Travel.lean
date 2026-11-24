import YM.SU5.Macro.Edge
/-! # Applying the nonlocal test at spatial displacements trading in given readings -/
set_option autoImplicit false
noncomputable section
namespace YM.SatinMacro
open Function Set Filter Metric NormedSpace OS.Semigroup Bornology Complex
open scoped Topology BigOperators InnerProductSpace NNReal
variable {H : Hilbert} {j : Axis} (S : OS.Semigroup H j) (X Y : H)

-- pointwise response and bounds. Omitting Δ positivity here makes the abstraction reusable for
-- pasting positive heat & analytic in any interval.
structure Ticket (e : OS.Cross j) (Δ : ℝ≥0) : Prop where
  ace : kernel S X Y 0 Δ ≠ 0
  stuff : HasPadding S Y
  centered : S.orth Y=0
  window : ∃ k:ℝ, k<0 ∧ AnalyticOnNhd ℝ (fun u:ℝ=> kernel S X Y (u•e) Δ) (Ioi k)

namespace Ticket
variable {S X Y} {Δ : ℝ≥0}
section
variable {e : OS.Cross j} (p : Ticket S X Y e Δ)
include p
lemma trades {J : Set ℝ} (h : Dense J) {a b:ℝ} (t:0≤a)(v:a<b) :
    ∃ u∈ Ioo a b ∩ J, kernel S X Y (u•e) Δ ≠ 0 := by
  obtain ⟨k,k',w⟩:=p.window
  exact analytic_price k' h w (by rw [zero_smul]; exact p.ace) (k'.le.trans t) v
lemma far {J : Set ℝ} (h : Dense J) : ∃ᶠ u:ℝ in atTop, u∈ J ∧ kernel S X Y (u•e) Δ ≠ 0 := by
  intro w; obtain ⟨t,v⟩:=eventually_atTop.mp w; let q:= max t 0
  obtain ⟨u,⟨⟨e,h'⟩,p⟩,v'⟩:=p.trades h (le_max_right t 0) (lt_add_one q)
  exact v u ((le_max_left t 0).trans e.le) ⟨p,v'⟩
end
-- port to Mink context
section
variable {S : OS.Semigroup H timeAxis} {e : OS.Cross timeAxis} (p : Ticket S X Y e Δ) (h : 0 < ‖(e:E4)‖)
variable {J : Set ℝ} (q : Dense J) (U V : Set E4) (x : IsBounded U) (y : IsBounded V)
variable {a b:ℝ} (m:a<b)
include h x y q m p
local notation "P" u:max t:max => joinST (j:=timeAxis) ((u:ℝ) • e) (t:ℝ)
lemma journeys : ∃ᶠ u:ℝ in atTop, u∈ J ∧ kernel S X Y (u•e) Δ ≠ 0 ∧
    (∀ t : ℝ, t∈ Icc a b → Apart U (there (P u t) V)) ∧
    -- Keep even the ordering of quantifiers. It isn't claiming the same t will
    -- detect the commutator against EVERY lift of the vectors to Labels.
    ∀ {W:Hilbert} (T:OS.Semigroup W timeAxis) (A A' B B':W), accord S X Y (u • e) T A B →
      ∃ t∈ Ioo a b, ¬ swap T.unit (P u t) A A' B B' := by
  refine ((p.far q).and_eventually (eventuallyApart x y e h (max (-a) b))).mono (fun u z=>?_)
  refine ⟨z.1.1,z.1.2, fun t v=> z.2 t (abs_le.mpr ⟨?_,?_⟩),fun {W} T A A' B B' v=> edge_any _ _ _ _ p.stuff p.centered z.1.2 m _ _ _ v _ _⟩
  · linarith [v.1,le_max_left (-a) b]
  exact (v.2).trans (le_max_right ..)

variable {W:Hilbert} (T:OS.Semigroup W timeAxis) (w:W) (hw:∀ p, T.unit.translation p w=w)
include hw
lemma distant (A B : W.Op) (t : ∀ᶠ u:ℝ in atTop, u∈J → accord S X Y (u • e) T (A w) (B w)) :
    ∃ᶠ u:ℝ in atTop, u∈ J ∧ (∀ t:ℝ,t∈ Icc a b→ Apart U (there (P u t) V)) ∧
    (∃ t∈ Ioo a b, ¬ Commute (star A) (act T.unit (P u t) B)) := by
  apply ((p.journeys h q U V x y m).and_eventually t).mono
  rintro u ⟨⟨i,v,c,d⟩,t⟩
  obtain ⟨t,h,t'⟩:= d T (A w) ((star A) w) (B w) ((star B) w) (t i)
  exact ⟨i,c,t,h,fun d=> t' (swap_of_commute T.unit _ w hw _ _ d)⟩

omit hw
lemma distinct (A B : H.Op) (w:H) (hw:∀ p, S.unit.translation p w=w) (u:A w=X)(v:B w=Y) :
    ∃ᶠ u:ℝ in atTop, u∈ J ∧ (∀ t:ℝ,t∈ Icc a b→ Apart U (there (P u t) V)) ∧
    (∃ t∈ Ioo a b, ¬ Commute (star A) (act S.unit (P u t) B)) := by
  refine p.distant h q U V x y m S w hw A B (Eventually.of_forall (fun r t=>?_))
  rw [u,v]; exact ⟨1,zero_lt_one, (Filter.Eventually.of_forall (fun i=>rfl)).frequently⟩
end
end Ticket
end YM.SatinMacro

#print axioms YM.SatinMacro.Ticket.journeys
#print axioms YM.SatinMacro.Ticket.distinct
