import YM.SU5.Reconstruction.Cross.Smoothed
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected Tapestry Tapestry.Altitude Tapestry.Exhibition
open Set OS.Semigroup MeshClock Germ
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
local notation "Μ" => timeMesh Λ
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  {D : ℕ→Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i:=i) (k:=k) (E:=E) Y H D a b) (Qt : Clipped Y H (i∘a) (k∘b))
  (s : ℕ) (j : Axis) (C : Arena Y H Q.circuit j 0 false) -- aim all even incl characters extension
variable (c : (displayAlgebra Y H V Q Qt j false C) →⋆ₐ[ℂ] ℂ)
local notation "𝔄" => driveAlgebra Y H V Q Qt j false C
local notation "ρ" => indoor Y H V Q Qt j false C c
local notation "Ρ" => procession Y H V Q Qt j false C c
local notation "Ω" => doorstep Y H V Q Qt j false C c
local notation "Eχ" s:max => Selected.response Y H V s Q Qt j false C c
local notation "Ex" => ride Y H V Q Qt j false C c
local notation "Φ" t:max => Tower.Field Y H t j 0 false
local notation "T" n:max => Selected.bud Y H V n Q Qt j false C c
open _root_.YM.SelectionAnalysis
variable {f : Marks (tent Y H) false} (g : Gate Y H s j f)
local notation "U" x:max => ambient (M:=timeMesh Λ) (turnstile Y H V Q Qt j false C c) x
local notation "S" => turnstile Y H V Q Qt j false C c
local notation "Β" => entrance Y H V s Q Qt j false C g.entry g.pos
local notation "B" => Ρ Β
local notation "O₀" => indoorOp Y H V Q Qt s j C c g
local notation "Γ" => saunters Y H V Q Qt j false C c
local notation "G" => peninsula Y H V Q Qt j false C c
local notation "L" => fort Y H V Q Qt j false C c
local notation "ζ" x:max => (G).U (diameter x)
local notation "P" => (Γ).orthogonalProjectionOnto
local notation "B₀" => narrowOrt Y H V Q Qt j false C c Β
local notation "ℓ" v:max => ((g.left v).toNNReal)
local notation "κ" v:max => ((g.right v).toNNReal)
noncomputable def paidOp (v : Axis→ℝ) : (fort Y H V Q Qt j false C c).Op :=
    (G).E (ℓ v)*(ζ v)* (narrowOrt Y H V Q Qt j false C c (entrance Y H V s Q Qt j false C g.entry g.pos)) * (ζ (-v)) * (G).E (κ v)
local notation "O" => paidOp Y H V Q Qt s j C c g

lemma keeping_times {X:Type*} {A D : Hilbert}(F : X→ A→L[ℂ]D) {l:Filter X} (v : X→A) (u:A)(w:D)
    (C₀ : ℝ) (c : ∀ i,‖F i‖≤C₀) (h:Tendsto v l (𝓝 u)) (p:Tendsto (fun i=> F i u) l (𝓝 w)) : Tendsto (fun i=> F i (v i)) l (𝓝 w):=by
 apply tendsto_of_tendsto_of_dist p
 apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) (g:=fun i=> C₀*dist (v i) u) ?_ (by simpa using (tendsto_iff_dist_tendsto_zero.mp h).const_mul C₀) -- tune implicit names
 apply Eventually.of_forall; intro x; rw [dist_comm,mul_comm C₀]
 simp only [dist_eq_norm,← map_sub]; exact ((F x).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (c x) (norm_nonneg _)).trans_eq (mul_comm ..))

lemma hot_cont {X:Type*}[TopologicalSpace X]{A:Hilbert} {j:Axis} (S₀ : OS.Semigroup A j){f:X→ A}{w:X→ℝ≥0}(h:Continuous f)(p:Continuous w): Continuous (fun x=> S₀.E (w x) (f x)) := continuous_iff_continuousAt.mpr (fun x=> keeping_times (fun i=> S₀.E (w i)) _ _ _ 1 (fun i=> S₀.shrinks _) h.continuousAt ((((S₀.continuousE (f x)).comp p).tendsto x)))
lemma dia_cont (j:Axis) : Continuous (fun v:Axis→ℝ=> SelectionAnalysis.diameter (a:=j) v):= (SEP j).continuous.comp (by fun_prop)

lemma minus_grid {M : Mesh} (x : seeMesh M) : -toR (M:=M) x=toR (M:=M) (-x):=rfl
lemma left_cont : Continuous (fun v=> ℓ v):= continuous_real_toNNReal.comp (((continuous_apply j).add continuous_const).sub continuous_const)
lemma right_cont : Continuous (fun v=> κ v):= continuous_real_toNNReal.comp (continuous_const.sub (((continuous_apply j).add continuous_const).sub continuous_const))

lemma paid_cont {X:Type*} [TopologicalSpace X](u : X→ L)(v:X→Axis→ℝ)(h:Continuous u)(p:Continuous v): Continuous (fun i=> O (v i) (u i)):=by
  unfold paidOp; simp only [ContinuousLinearMap.mul_apply]; refine hot_cont (G) ?_ ((left_cont Y H s j g).comp p)
  refine (G).cont_cross _ _ ?_ ((dia_cont j).comp p)
  exact (B₀).continuous.comp ((G).cont_cross _ _ (hot_cont (G) h ((right_cont Y H s j g).comp p)) ((dia_cont j).comp p.neg))
lemma ambient_norm {j:Axis} {M: Mesh} {A:Hilbert} (S₀:Germ.Alliance (Trans j) (marks M) A) (x:seeMesh M) (u : A) : ‖ambient (M:=M) S₀ x u‖= ‖u‖:=by
 unfold ambient; generalize look j=t
 induction t with
 | nil=> rfl
 | cons i t ih=>rw [S₀.raw_step,ContinuousLinearMap.comp_apply,Players.wins,ih]
lemma ambient_cost {M:Mesh} {j:Axis}{A:Hilbert} (S₀:Germ.Alliance (Trans j) (marks M) A) (x:seeMesh M):‖ambient (M:=M) S₀ x‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro v; rw [ambient_norm,one_mul])
lemma indoor_cost (x : seeMesh (timeMesh Λ)) : ‖O₀ x‖ ≤ ‖Ρ Β‖ := by
 have h {a b:(ρ).Op} (z:‖b‖ ≤ 1): ‖a*b‖≤‖a‖:= (norm_mul_le ..).trans (mul_le_of_le_one_right (by positivity) z)
 unfold indoorOp; dsimp only
 refine le_trans ((le_trans (h ((Ex).shrinks _)) (h (ambient_cost _ _)))) ((norm_mul_le ..).trans (mul_le_of_le_one_left (by positivity) ((h (ambient_cost _ _)).trans ((Ex).shrinks _)))) -- tune notation

local notation "Ο" => seeMesh (timeMesh Λ)
local notation "Tv" x:max=> toR (M:=timeMesh Λ) x
lemma indoor_glass (u:Ο)(x:L): ((ζ (Tv u)) x : Γ).val=(U u) x.val:= glass_move (mainsea Y H V Q Qt j false C c) (daylight (timeMesh Λ)) Ex (follows_road Y H V Q Qt j false C c) x u
lemma commit_heat (u:Ο)(t:ℝ≥0)(x:ρ) : (Ex).E t ((U u) x)= (U u) ((Ex).E t x) :=
     congrArg ((fun T₀ : (ρ).Op=> T₀ x)) (((turnstile Y H V Q Qt j false C c).hard (look j) ((Ex).E t) (fun i _ v=> follows_road Y H V Q Qt j false C c i v t) (fun i=> u i.val)).symm)
lemma proceeds_heat (x:L) (u : ℝ≥0) : ((G).E u x:Γ).val=(Ex).E u x.val:=rfl
lemma bracket_heat (x:ρ)(t:ℝ≥0) : P ((Ex).E t x)=(G).E t (P x) := by
 apply Subtype.ext; rw [proceeds_heat]; have he:= (S).ground (look j) ((Ex).E t) (fun i _ v=> follows_road Y H V Q Qt j false C c i v t)
 rw [stack_projection S] at he
 exact congrArg (fun s : (ρ).Op=> s x) he.symm

/-- In this precise sense the bounded window factor in a CP4 fort is an unprojected
Gate observation, averaged in ABSOLUTE lateral spacetime placements in the true
hierarchy, then projecting. This supplies the strong limit on fort vectors, not all. -/
lemma strong_projection (x:Ο)(w:L) :
    Tendsto (fun n:ℕ×ℕ=> smear (timeMesh Λ) (indoorOp Y H V Q Qt s j C c g) x n (w.val:ρ)) nested
        (𝓝 (((paidOp Y H V Q Qt s j C c g (toR (M:=Μ) x) w : Γ).val):ρ)):=by
 let Y₀(z:Axis→ℝ):L:= (ζ (-z)) ((G).E (κ z) w)
 have hY: Continuous Y₀:= (G).cont_cross _ _ (hot_cont (G) continuous_const (right_cont Y H s j g)) ((dia_cont j).comp continuous_neg)
 let q(v:Axis→ℝ):ρ:= (Ex).E (ℓ v) ((Ρ Β) (Y₀ v).val)
 have hq:Continuous q:= hot_cont Ex ((B).continuous.comp (continuous_subtype_val.comp hY)) (left_cont Y H s j g)
 have he (u:Ο): O₀ u (w.val:ρ) = (U u) (q (Tv u)):=by
    unfold indoorOp q; simp only [ContinuousLinearMap.mul_apply]; rw [commit_heat]
    unfold Y₀; rw [minus_grid,indoor_glass,proceeds_heat]
 have ht : ((O (Tv x) w:Γ).val:ρ)=(U x) (((S).aviator (look j)).starProjection (q (Tv x))) := by
    unfold paidOp
    simp only [ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.comp_apply (g:=(G).E (ℓ (Tv x))), (G).independent, ContinuousLinearMap.comp_apply, indoor_glass]
    change (U x) (((G).E _ (P ((Ρ Β) (Y₀ _).val)) : Γ).val) = _
    rw [←bracket_heat]; rfl
 rw [ht];
 have hu(n): smear Μ O₀ x n (w.val:ρ)=(smear Μ (fun u=> (U u) (q (Tv u))) x n):= by unfold smear; rw [centerActs]; simp_rw [he]
 simp_rw [hu]; apply beside _ _ _ _ (glide S x (q (Tv x)))
 simp only [dist_eq_norm,←map_sub, ambient_norm]
 have hc: Tendsto (fun i:(Ο)=> q (Tv x)-q (Tv i)) (𝓝 x) (𝓝 (q (Tv x)-q (Tv x))) := tendsto_const_nhds.sub ((hq.comp (toR_cont Μ)).tendsto x)
 simpa only [sub_self,norm_zero] using hc.norm -- maybe simplify
lemma smear_budget (v:Ο)(t:ℕ×ℕ): ‖smear Μ (indoorOp Y H V Q Qt s j C c g) v t‖≤ ‖Ρ Β‖:= by
 exact Average.norm_worth fun i=> indoor_cost Y H V Q Qt s j C c g _
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Atlas.strong_projection
