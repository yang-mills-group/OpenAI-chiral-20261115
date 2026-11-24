import YM.SU5.Reconstruction.AnglePath.Vista
/-! # angular prices on this law CP. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
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
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
variable (P:Ramp)(e:RPos Y H V G P C a χ)(B:BoostBacking Y H V G C a χ)(W:Chat Y H V G P C a χ)
open CrossedFrame.Cardio _root_.YM.ConePrice.Storm.StepVoucher
local notation "S"=> SpinOn Y H V G C a χ P e
local notation "G₁" => Domain Y H G false (aperture P)
local notation "H₀" => Domain Y H G false (northD P)
local notation "U"=> audition Y H V G C a χ P P.a (stocks_a P)
local notation "Z"=> audition Y H V G C a χ P P.b (stocks_b P)
local notation "M"=> motor Y H V G C a χ B S (Oriented.rotateAB P)
local notation "R"=> retina Y H V G C a χ P e B
local notation "K₁"=> profile Y H V G C a χ P W
local notation "F"=> cruise P (1/2)
local notation "ξ"=> coordinates Λ
local notation "V'"=> sails Y H V G P
lemma post_spin(x: placement Λ): 0≤ (cruise P (1/2) (coordinates Λ x)) P.a ↔ 0≤(hoursN P x).val:=by
 rw [mid_rate]; have H:0<Real.sqrt 2/2:=by positivity
 exact mul_nonneg_iff_of_pos_left H
private lemma ir (p:placement Λ): p = P.s.act p+billT P (hoursN P p) :=by
 funext i; rw [Pi.add_apply]; unfold billT stretchD; by_cases e:i=P.a; · subst i; rw [terrain_time P.cross,P.move_a]; change _= -(p P.b)+(p P.a+p P.b); abel
 by_cases v:i=P.b; · subst i; rw [terrain_space,P.move_b]; change _= -(p P.a)+(p P.a+p P.b); abel
 rw [terrain_other _ _ _ _ _ e v,P.move_h _ e v,add_zero]
private lemma tans(p:placement Λ)(h:0≤ (hoursN P p).val)(x:H₀): inner ℂ (W.plant (V' p h x)) (W.plant (V' p h x))=inner ℂ (W.plant x) ((radial Y H V G P C a χ W (hoursN P p) h) (W.plant x)):=by
 rw [(service Y H V G P C a χ W _ h).2]; exact doubly_take Y H V G P C a χ W x x p p (billT P _) h h (billT_pos P _ h) (ir ..)
lemma sat_budget (p:placement Λ)(h:0≤ (hoursN P p).val)(x:H₀) : ‖W.plant (sails Y H V G P p h x)‖≤‖W.plant x‖:=by
 let t:= hoursN P p; let A:= W.plant (V' p h x); let B':=W.plant x; let U':=radial Y H V G P C a χ W t h
 apply le_of_sq_le_sq _ (norm_nonneg _); change ‖A‖^2≤‖B'‖^2
 have he:‖inner ℂ B' (U' B')‖= ‖A‖^2:= by unfold U' B' A t; rw [← tans Y H V G C a χ, inner_self_eq_norm_sq_to_K,norm_pow]; change ‖(↑(‖W.plant _‖:ℝ):ℂ)‖^2=_; simp -- tune P implicit
 rw [←he]; exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left ((U'.le_opNorm B').trans (mul_le_of_le_one_left (norm_nonneg _) (service Y H V G P C a χ W _ h).1)) (norm_nonneg _)).trans_eq (pow_two _).symm)
noncomputable def procure (p:placement Λ)(h:0≤(hoursN P p).val): W.H.Op:= (extends_path (fanoForm Y H V G P C a χ) W (sails Y H V G P p h) (sat_budget Y H V G C a χ P W p h)).choose
lemma procurement(p:placement Λ)(h:0≤(hoursN P p).val): ‖procure Y H V G C a χ P W p h‖≤1∧∀x:H₀,(procure Y H V G C a χ P W p h) (W.plant x)= W.plant (sails Y H V G P p h x):= (extends_path (fanoForm Y H V G P C a χ) W (sails Y H V G P p h) (sat_budget Y H V G C a χ P W p h)).choose_spec
local notation "E'"=> procure Y H V G C a χ P W
lemma procure_sum(p u:placement Λ)(v w z): E' p v * E' u w= E' (p+u) z:= by apply W.by_bud; intro x; change E' p v ((E' u w) (W.plant x))=_; rw [(procurement Y H V G C a χ P W u w).2,(procurement Y H V G C a χ P W p v).2,(procurement Y H V G C a χ P W _ z).2,issue_add Y H V G P p u v w z]
open Schedule OS.Semigroup
private lemma gain_all {H:Hilbert}(S':OS.Semigroup H P.a)(x:RSpace): DenseRange (route S' x):=by
 let s:= diameter (a:=P.a) x; have h: (S'.U s)*(S'.U (-s))=1:= by rw [show (S'.U s)*(S'.U (-s))= S'.U (s+(-s)) from (S'.space ..).symm,add_neg_cancel,S'.uZero]; rfl
 exact (S'.whole _).mono (by rintro _ ⟨z,rfl⟩; exact ⟨S'.U (-s) z,congrArg _ (DFunLike.congr_fun h z)⟩) -- tune ν ℝ
lemma reflectSpots (p:placement Λ)(u:(coordinates Λ p P.a)≥0)(v: (coordinates Λ p P.b)≥0):0≤ (hoursN P p).val:=add_nonneg u v
-- Reconciliation of all, even if corresponding tilting frame α no longer in Q signage.
lemma trajectory(S':OS.Semigroup W.H P.a)
  (g:∀ (p:placement Λ)(u:(coordinates Λ p P.a)≥0)(v: (coordinates Λ p P.b)≥0), E' p (reflectSpots P p u v)=Schedule.route S' (cruise P (1/2) (coordinates Λ p))) (p: placement Λ)(z:0≤ (hoursN P p).val): E' p z=Schedule.route S' (F (coordinates Λ p)):=by
 let t:= ξ p; obtain ⟨s,h⟩:= anywhere Λ (max (max (-t P.a) (-t P.b)) 0)
 have u:0≤ s.val:= (le_max_right ..).trans h.le; let q:=billT P s
 have p₁:(coordinates Λ q P.a)= (s:ℝ):= congrArg Subtype.val (terrain_time P.cross s s)
 have p₂:ξ q P.b=(s:ℝ):= congrArg Subtype.val (terrain_space P.a P.b s s) -- tune
 have v:0≤ξ q P.a:=p₁.symm ▸ u; have w:0≤ξ q P.b:=p₂.symm ▸ u
 have vx:0≤ ξ (p+q) P.a:= by rw [map_add,Pi.add_apply,p₁]; change 0≤ t _+_; linarith [le_max_left (-t P.a) (-t P.b), le_max_left (max (-t P.a) (-t P.b)) 0]
 have wx:0≤ ξ (p+q) P.b:= by rw [map_add,Pi.add_apply,p₂]; change 0≤ t _+_; linarith [le_max_right (-t P.a) (-t P.b), le_max_left (max (-t P.a) (-t P.b)) 0]
 let u':= reflectSpots P q v w; have he:E' p z* E' q u'=route S' (F (ξ p))* E' q u':= by
    rw [procure_sum Y H V G C a χ P W p q z u' (reflectSpots P (p+q) vx wx),g (p+q) vx wx, g q v w, map_add, cruise_add, joint_routes P S' _ _ ((post_spin P p).2 z) ((post_spin P q).2 u')]
 refine dense_cancel _ ?_ he; rw [g q v w]; exact gain_all (H:=W.H) P S' _
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose.Emissions
