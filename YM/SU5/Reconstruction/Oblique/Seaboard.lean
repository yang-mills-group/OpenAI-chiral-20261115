import YM.SU5.Reconstruction.Oblique.Precard
/-! # The Stieltjes semigroup, costs from other actual oriented fields (Full indoor). -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
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
variable (P:Ramp) {J: Calibration}
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "Π" => Domain Y H G false (northD P)
local notation "S" => Domain Y H G false (southD P)
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
variable (W:Chat Y H V G P C a χ)
abbrev billT (P:Ramp) (t: marks (timeMesh Λ)) := stretchD P t t
lemma billT_pos (t:Gt)(h:0≤ (t:ℝ)): 0≤(hoursN P (billT P t)).val:=by unfold billT; rw [hourMark]; exact add_nonneg h h
noncomputable def treks (P:Ramp)(t:Gt)(h:0≤ (t:ℝ)): Domain Y H G false (northD P) →ₗ[ℂ] Domain Y H G false (northD P) := sails Y H V G P (billT P t) (billT_pos P t h)
local notation "ξ" => treks Y H V G P
local notation "Ωy"=> gust P K
local notation "Wr"=> stretchD P
lemma trek_add(i j:Gt)(x y z)(f:Π): treks Y H V G P i x (treks Y H V G P j y f) = ξ (i+j) z f:=by apply Subtype.ext; change move K (Wr i i) (move K (Wr j j) f.val)=move K (Wr _ _) f.val; rw [move_sum,stretch_add]
lemma trek_zero(f:Π): ξ (0:Gt) (by simp) f=f:=by apply Subtype.ext; change au (Wr 0 0) _=_; rw [mark_zero,move_by_zero]; rfl

lemma shifts(x y:Π)(s u v p:placement Λ)(hs hu hv hp)
    (e:P.s.act u+v=P.s.act p+s):
    inner ℂ (W.plant (sails Y H V G P u hu x)) (W.plant (sails Y H V G P s hs y)) = inner ℂ (W.plant (sails Y H V G P p hp x)) (W.plant (sails Y H V G P v hv y)):= by
 let T:=sails Y H V G P p hp x; let D':=sails Y H V G P v hv y
 simp only [guide Y H V G P C a χ W]
 rw [←whiff_move Y H V G C a χ (on_Cover Y H V G P T.property D'.property) (s-v)] -- target exact match? unfolds not?
 change Ω ((Ωy (au u x.val))* (au s y.val))= Ω (au (s-v) ((Ωy (au p x.val)) *(au v y.val)))
 rw [move_prod, zone_gust Y H P, zone_gust Y H P,move_sum,move_sum,sub_add_cancel,show s-v+P.s.act p=P.s.act u by rw [eq_sub_of_add_eq e]; abel]
private lemma sailing_zero(f:Π): sails Y H V G P 0 (by rw [map_zero];exact le_rfl) f=f:=Subtype.ext (move_by_zero Λ K f.val)
lemma doubly_take (x y:Π)(s u v:placement Λ)(hs hu hv) (h:u = P.s.act s+v):
    inner ℂ (W.plant (sails Y H V G P s hs x)) (W.plant (sails Y H V G P u hu y)) = inner ℂ (W.plant x) (W.plant (sails Y H V G P v hv y)) := by
 nth_rw 2 [← sailing_zero Y H V G P x]; exact shifts Y H V G P C a χ W x y u s v 0 hu hs hv (by rw [map_zero];exact le_rfl) (by rw [Signed.act_zero,zero_add,h])
lemma sail_cost (x y:Π)(s v:Gt)(p:0≤ (hoursN P (stretchD P s v)).val)(u)
    (A:Π) (q:A.val=au (Wr (s+v) (s+v)) y.val) (H':0≤((s+v:Gt):ℝ)) : inner ℂ (W.plant (sails Y H V G P (Wr s v) p x)) (W.plant (sails Y H V G P (Wr s v) u y))=inner ℂ (W.plant x) (W.plant A) := by
 rw [show A=ξ _ H' y from Subtype.ext q]
 refine doubly_take Y H V G P C a χ W x y _ _ _ p u (billT_pos P _ H') ?_
 unfold billT; rw [stretch_turn,stretch_add]; congr 1 <;> abel_nf -- tune

lemma doubles_take (x:Π)(v:Gt)(p:0≤(v:ℝ))(q:0≤((v+v:Gt):ℝ)): inner ℂ (W.plant (ξ v p x)) (W.plant (ξ v p x)) = inner ℂ (W.plant x) (W.plant (ξ (v+v) q x)):= sail_cost Y H V G P C a χ W x x v v (billT_pos P v p) (billT_pos P v p) (ξ (v+v) q x) rfl q -- args tune
lemma monotone_v(t:Gt)(q:0≤(t:ℝ))(x:Π): 0 ≤ inner ℂ (W.plant x) (W.plant (ξ t q x)):=by
 have hx:0≤(hoursN P (Wr t 0)).val:=by rw [hourMark,add_zero]; exact q
 rw [← sail_cost Y H V G P C a χ W x x t 0 hx hx (ξ t q x) (by change au _ _=_; rw [add_zero]; rfl) (by rw [add_zero]; exact q)]
 rw [inner_self_eq_norm_sq_to_K]; positivity
lemma motionScore (x y:Π)(t:Gt)(q:0≤ (t:ℝ)): inner ℂ (W.plant x) (W.plant (ξ t q y))= Ω (gust P K x.val * move K (Wr t t) y.val):= guide Y H V G P C a χ W x (ξ t q y)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
