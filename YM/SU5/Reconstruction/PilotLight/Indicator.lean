import YM.SU5.Reconstruction.PilotLight.Composition
import YM.SU5.Reconstruction.Vermont.Playlist
/-! The Wick amplitude of these probes. Full before any projecting to real
spatial-continuity price. Will use where proven licensed. Only at BOUGHT
positions on the common grid (time gap then analyt continued; orientation convention as CP1). -/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5500
set_option maxHeartbeats 340000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
local notation "Gt" => marks (timeMesh Λ)
variable (j : Axis)(C:Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
open Chambers LightBudget
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "Ω"=> doorstep Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "F"=> osValue Y H V G j C χ
local notation "T₀"=> OSvector Y H V G j C χ
local notation "Pr"=> atEstate Y H V G.history G.clipped j false C χ
local notation "U₁"=>charted Y H V G j C χ
local notation "Lp'"=> Follows Y H V G j C χ
open Fock OS Semigroup ConePrice Sail
variable (p:placement Λ)
variable (A B: (indoor Y H V G.history G.clipped j false C χ).Op)
def pilotBeam (A B: (indoor Y H V G.history G.clipped j false C χ).Op)(z:ℂ) := inner ℂ Ω (A (Sail.phase (L) z (U₁ p (B Ω))))
local notation "Pb"=>pilotBeam Y H V G j C χ p
lemma beamingHol : AnalyticOnNhd ℂ (Pb A B) OS.Semigroup.inside:=by
 intro z hz; exact ((innerSL ℂ Ω).analyticAt _).comp ((A.analyticAt _).comp (((ContinuousLinearMap.apply ℂ (J₀).space (U₁ p (B Ω))).analyticAt _).comp (phase_ana (L) z hz)))
lemma beaming_cont : Continuous (Pb A B):= continuous_const.inner (A.continuous.comp (phase_cont (L) _ _ continuous_const continuous_id))
lemma on_clock (t:ℝ): Pb A B (sideways t)=inner ℂ Ω (A ((L).edge t (U₁ p (B Ω)))):= by unfold pilotBeam; rw [width_imaginary]
section linear
variable {A B}
private lemma solidAdd (x y z: (J₀).Op) (t:ℂ) : Pb (x+y) z t= Pb x z t+Pb y z t:=by unfold pilotBeam; rw [ContinuousLinearMap.add_apply,inner_add_right] -- tune
lemma allSolids (x y z: (J₀).Op) (t:ℂ): Pb (x+y) z t= Pb x z t+Pb y z t ∧ Pb x (y+z) t= Pb x y t+Pb x z t:= ⟨solidAdd ..,(by unfold pilotBeam; rw [ContinuousLinearMap.add_apply,map_add,map_add,map_add,inner_add_right])⟩
lemma quota_scale (x y:(J₀).Op)(t a:ℂ) : Pb (a • x) y t=a*Pb x y t ∧ Pb x (a • y) t=a*Pb x y t:=by constructor <;> unfold pilotBeam <;> simp only [ContinuousLinearMap.smul_apply,map_smul,inner_smul_right]
lemma zero_left (A: (J₀).Op)(t:ℂ): Pb 0 A t=0:= inner_zero_right ..
lemma zero_right (A:(J₀).Op)(t:ℂ): Pb A 0 t=0:=by unfold pilotBeam; rw [ContinuousLinearMap.zero_apply,map_zero,map_zero,map_zero,inner_zero_right]
lemma phaseVac (z:ℂ): Sail.phase (L) z Ω=Ω:=by unfold Sail.phase; rw [ContinuousLinearMap.comp_apply,bought_heat]; exact (resides_real ..).1 _
lemma fullHeat (a b:ℝ≥0)(t:ℂ): Pb ((L).E a) ((L).E b) t=1:=by unfold pilotBeam; rw [bought_heat,concert_omega,phaseVac,bought_heat,inner_self_eq_norm_sq_to_K,Selected.ready]; norm_num
lemma staysDim (a b:ℝ≥0)(t:ℂ): Pb (-((L).E a)) (-((L).E b)) t =1:=by
 rw [← neg_one_smul ℂ ((L).E a),← neg_one_smul ℂ ((L).E b), (quota_scale Y H V G j C χ p _ _ t (-1)).1,(quota_scale Y H V G j C χ p _ _ t (-1)).2,fullHeat]; ring
lemma span_bill (A B:(indoor Y H V G.history G.clipped j false C χ).Op)(z:ℂ): ‖Pb A B z‖ ≤ ‖A‖*‖B‖:=by
 let R:=(L); let t:=Sail.phase (L) z (U₁ p (B Ω))
 have hg: ‖t‖≤ ‖B‖:=by
   unfold t; refine (((Sail.phase R _).le_opNorm _).trans ?_); apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (Lens.phase_price (L) z))
   apply le_trans ((U₁ p).le_opNorm _); apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (concert_bill ..)); exact (B.le_opNorm Ω).trans_eq (by rw [Selected.ready,mul_one])
 unfold pilotBeam; apply (norm_inner_le_norm (𝕜:=ℂ) _ _).trans; rw [Selected.ready,one_mul]; exact (A.le_opNorm t).trans (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
lemma distance_pay {a b:ℝ≥0}{g h:ℝ} (z:ℂ) (x:‖A+(L).E a‖≤g)(y:‖B+(L).E b‖≤h): ‖Pb A B z-1‖ ≤ h+g+g*h:=by
 let W:=(L).E a; let H0:=(L).E b; let X:= A+W; let Z:=B+H0
 have Hx:‖-W‖≤1:=by rw [norm_neg]; exact (L).shrinks _
 have Hp:‖-H0‖≤1:=by rw [norm_neg]; exact (L).shrinks _
 have y1:‖Pb (-W) Z z‖≤h:= (span_bill ..).trans ((mul_le_of_le_one_left (norm_nonneg _) Hx).trans y)
 have y2:‖Pb X (-H0) z‖ ≤g:= (span_bill ..).trans ((mul_le_of_le_one_right (norm_nonneg _) Hp).trans x)
 have e: Pb A B z-1=Pb (-W) Z z+Pb X (-H0) z+Pb X Z z:=by
    nth_rw 1 [show A=-W+X from (by unfold X; abel),show B=-H0+Z from (by unfold Z; abel)] -- syntax? 
    rw [(solidAdd ..), (allSolids Y H V G j C χ p _ _ _ z).2, (allSolids Y H V G j C χ p X _ _ z).2, staysDim Y H V G j C χ p a b]; abel
 rw [e]; exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add y1 y2)) ((span_bill ..).trans (mul_le_mul x y (norm_nonneg Z) ((norm_nonneg X).trans x))))
end linear

variable {x y: Sky (tent Y H)}{u v: marks (timeMesh Λ)} {A B}
lemma sparePrice (t : (u:ℝ)<(p j:ℝ)) (w:0≤(v:ℝ))(he:0≤(u:ℝ)) (a:Lp' x u A)(b:Lp' y v B){z: Domain Y H G false (flank j 0)} (q:z.val=x*move K p y) : T₀ z= A (Pr (p-eject j u) (B Ω)):=by
 let f:= boxAfter Y H V G j C χ p (p j+v) he w t (le_refl _) a b
 rw [answer_oper Y H V G j C χ f q]; change A (Pr _ (B (Pr _ Ω)))=_; rw [staysVacuum]
lemma euPrice (t:(u:ℝ)<(p j:ℝ))(w:0≤(v:ℝ))(he:0≤(u:ℝ))(a:Lp' x u A)(b:Lp' y v B): ∃ h:x*move K p y∈D false Set.univ,
    osValue Y H V G j C χ ⟨x*move K p y,h⟩ = Pb A B (((coordinates Λ p j - (u:ℝ)):ℝ):ℂ):=by
 let e:= boxAfter Y H V G j C χ p (p j+v) he w t (le_refl _) a b;
 let z:Domain Y H G false (flank j 0):=⟨_,domain_mono Y H G (Chambers.strip_in j ((p j+v: Gt):ℝ)) e.pose⟩; refine ⟨domain_mono Y H G (Set.subset_univ _) z.property,?_⟩
 apply Eq.trans (expectation Y H V G j C χ z).symm; rw [sparePrice Y H V G j C χ p t w he a b (show z.val=_ from rfl)];
 unfold pilotBeam; rw [width_real];
 rw [ensemble,chart_away Y H V G j C χ _ p (fun i=> by change p i.val-eject j u i.val=_; rw [eject_away j u i.val i.property,sub_zero]), Pi.sub_apply,eject_at]; rfl
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.euPrice
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.distance_pay
