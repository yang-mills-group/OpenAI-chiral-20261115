import SatinPP.Showroom
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "Γ"=> P.truck 3 ξ
local notation "γ"=> P.cartage 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "λ'"=> P.enter 3 ξ
local notation "E"=> (S).E

variable (D:Vantage→ℝ)(F:SampleDose)(t:ℕ)
-- only μ-specific clamp off support -- positive all-T on x enables this
variable (V:ℝ→P.ColorHil 3 (P.advocate 3 x 3))(Z:ℝ→P.ManyF 3 (P.advocate 3 x 3))
local notation "p" => P.meshPose t
local notation "u" => P.vtile t
local notation "α"=> P.activation t F
local notation "ε"=> P.usedGrid t F

def askW:H := ∑ i∈ε,α i • Γ (u i) (V (D (p i)))

def readW:G:= DoseTravel.beam (G) F (fun v=> γ v (Z (D v))) -- scope
local notation "T"=> P.askW x D F t V
private lemma msum_here (X:Hilbert)(f:Vantage→X)(U:Cover → X.Op):
    poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) U (P.macroStep t) =∑ i∈ ε, α i • U i (f (p i)):=by
  let g:=fun i:Cover=> U i ((F.val (p i):ℂ) • f (p i))
  have he(i:Cover)(x:i∉ε): g i=0:= by
    have hu : F.val (p i)=0 := by by_contra q; exact x ((P.usedPose t F i).2 (subset_closure q))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
  refine (room_price (P.macroStep t) (P.macroStep_pos t) g (ε) he).2.trans ?_
  rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h
  unfold g; rw [map_smul,
    show Fintype.card Axis=4 by rfl, ← Complex.coe_smul ((P.macroStep t)^4), smul_smul]
  push_cast [activation]; rfl

-- macro projection cost
lemma ask_cont (J:P.Ellis 3 x)(B:Positive (S) V) (u₁:Continuous D)(u₂:∀ y,0 < D y)(z:∀ t:ℝ,0<t→ π' (V t)= Z t):
    Tendsto (fun t=> P.askW x D F t V) atTop (𝓝 (λ' (P.readW x D F Z))):= by
 let A(qz:Vantage):=D qz; have hA(qz:Vantage):0<A qz:= u₂ qz
 let U:= V∘ A; let X(qz:Vantage):=(F.val qz:ℂ) • U qz; let q(qz:Vantage):= γ qz (π' (X qz))
 have he: HasCompactSupport X:= F.budget.mono (fun i w t=> w ((congrArg (fun b:ℝ=> (b:ℂ) • U i) (show F.val i=0 from t)).trans (zero_smul ℂ _)))
 have hu:Continuous U:= continuous_iff_continuousAt.mpr (fun i=> (Positive.cont (S) V B (hA i)).comp (f:=A) (u₁.continuousAt))
 have ht: Continuous X:= (Complex.continuous_ofReal.comp F.smooth.continuous).smul hu
 rw [show P.readW x D F Z= ∫ qz:Vantage,q qz from integral_congr_ae (Eventually.of_forall fun i:Vantage=> by
    change (F.val i:ℂ) • γ i (Z (A i))= γ i (π' ((F.val i:ℂ) • V (A i)))
    rw [map_smul,map_smul,z _ (hA i)])]
 exact (P.macroRiemann x 3 J X he ht).congr fun i=> msum_here P _ _ (H) U _


variable {P x V D Z}{μ:ℝ}(g:∀ y,μ ≤ D y)(f:Continuous D)(m:0<μ)
variable (B:Positive (P.physicalEnergy 3 (P.advocate 3 x 3)) V)(J:P.Ellis 3 x)
section
variable {W:ℝ→P.ColorHil 3 (P.advocate 3 x 3)}
include B g m
lemma ask_cost (L:Positive (S) W):
 dist T (P.askW x D F t W) ≤ (∑ i∈ ε,‖α i‖)* ‖W μ - V μ‖ := by
 rw [dist_comm,dist_eq_norm, askW, askW, ← Finset.sum_sub_distrib, Finset.sum_mul]
 refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> ?_)
 have r:=g (p i)
 let U:= Γ (u i)
 have hu (x): ‖U x‖=‖x‖:= P.truck_norm ..
 rw [←smul_sub,norm_smul, B _ _ m r, L _ _ m r, ←map_sub U, hu]
 let k:=E (D (p i)-μ).toNNReal
 rw [←map_sub k]
 exact mul_le_mul_of_nonneg_left
     ((k.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks _)))
     (norm_nonneg _)

end
/-- Norm delivery through consultations (all simultaneous runs
 *and* iterated slot). Fixed widths then grid →∞ even when
prices off-limit outside final recipe. -/
structure Routed (K:ℕ→ℕ→P.ColorHil 3 (P.advocate 3 x 3)) (T':P.ManyF 3 (P.advocate 3 x 3)):Prop where
 iterates : ∃Y:ℕ→G,(∀ᶠ i in atTop, Tendsto (K i) atTop (𝓝 (λ' (Y i)))) ∧
      Tendsto Y atTop (𝓝 T')
 together (ℓ:ℕ→ℕ)(e:Tendsto ℓ atTop atTop): Tendsto (fun i=>K i (ℓ i))
      atTop (𝓝 (λ' T'))

include f B J g m
lemma ask_out (z:∀ y:ℝ,0<y→ π' (V y)= Z y)
  (W:ℕ→ℝ→(H).space)(L:∀ i,Positive (S) (W i))
  (a:Tendsto (fun i=>W i μ) atTop (𝓝 (V μ))):
 Routed (P:=P) (x:=x) (fun i t=>P.askW x D F t (W i))
    (P.readW x D F Z):=by
 let Y(i:ℕ):=P.readW x D F ((π')∘W i)
 have b(i:ℕ):Tendsto (fun t=>P.askW x D F t (W i)) atTop (𝓝 (λ' (Y i))):=
    ask_cont P x D F _ _ J (L i) f (fun _=>m.trans_le (g _)) (fun _ _=>rfl)


 have d:=ask_cont P x D F V Z J B f (fun _=>m.trans_le (g _)) z
 have lim:=tendsto_iff_norm_sub_tendsto_zero.mp a
 refine ⟨⟨Y,Eventually.of_forall b,?_⟩,fun ℓ e=>?_⟩
 · apply (tendsto_const_nhds (x:=P.readW x D F Z)).congr_dist
   have y:=lim.const_mul (∫ v, ‖F.val v‖)
   rw [mul_zero] at y
   refine squeeze_zero (fun _=>dist_nonneg) (fun i=>?_) y
   change dist _ (Y i) ≤ _
   rw [←(λ').dist_map]
   exact le_of_tendsto_of_tendsto (d.dist (b i))
     ((P.thin_activation_abs F).mul_const _) (Eventually.of_forall fun v=>ask_cost F v g m B (L i))
 apply (d.comp e).congr_dist
 have y:= ((P.thin_activation_abs F).comp e).mul lim
 rw [mul_zero] at y
 exact squeeze_zero (fun _=>dist_nonneg) (fun i=>ask_cost F _ g m B (L i)) y

omit f B J g m
#print axioms ask_out

lemma Routed.transfer
 {a b:ℕ→ℕ→P.ColorHil 3 (P.advocate 3 x 3)}
 {c:P.ManyF 3 (P.advocate 3 x 3)} (r:Routed a c)(d:∀ᶠ i in atTop, ∀j,a i j=b i j):
 Routed b c:=by
 obtain ⟨Y,h,k⟩:=r.iterates
 exact ⟨⟨Y,(h.and d).mono fun _ i=>i.1.congr i.2,k⟩,
   fun ℓ e=> (r.together _ e).congr' (d.mono fun _ i=>i _)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
