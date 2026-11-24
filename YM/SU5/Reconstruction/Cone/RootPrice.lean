import YM.SU5.Reconstruction.Cone.Test
import YM.SU5.Reconstruction.Cone.Fosters
/-!
# Pay the same Euclidean price on the unselected theory TO establish the cone budget for **all** windows on any character.
Before-selection OS transfer; thus also provides a SHARP-path route for obtaining the analytic pressure price.
Importantly, not merely using mixture to push price to some component -- requires *operator order* with gauge singlets dense.
Conditional, not claiming affordability already. `fullBudget` priced here against coarse Eu Gram `courseValue`, so one
can pass from real estimates at finite-lattice gauges. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace LightBudget
open SlabMark MeshClock ConePrice Germ OS SelectionAnalysis
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "V₀" => Domain Y H G false
local notation "D" => Domain Y H G true
local notation "Gt" => timeMesh Λ
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀" => indoor Y H V G.history G.clipped j false C χ
local notation "C₀" => saunters Y H V G.history G.clipped j false C χ
local notation "G₀" => fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "E₀"=> advance Y H V G.history.circuit j 0 false C
local notation "Z"=> ladder Y H V G.history.circuit j 0 false C
set_option quotPrecheck false
local notation "S₀"=> (clockdrive Y H V G.history.circuit j 0 false C).monoAxis j
local notation "ν" s:max=> actor Y H s G.history.circuit j 0 false C

/-- Before-selection linear receipt on the SAME test system. -/
noncomputable def prepaid : Domain Y H G false (flank j 0) →ₗ[ℂ] A :=
  assemble Y H G (flank j 0) false (fun s => (arrows Y H V G.history.circuit j 0 false C s).comp (asField Y H j false s)) (fun s t p x=>
    join_actor Y H V G.history.circuit j 0 false C s t p (asField Y H j false s x)) -- maybe defeq
local notation "ν₀"=> prepaid Y H V G j C
local notation "Κv"=> courseValue Y H V G
@[simp] theorem prepaid_enclose (s : ℕ) (x : insideAt Λ l K false (flank j 0) s) :
    ν₀ (enclose Y H G (flank j 0) false s x) = (ν s) (asField Y H j false s x) := assemble_enclose ..

lemma initial_pair (x y : Domain Y H G false (flank j 0)) :
    inner ℂ (ν₀ x) (ν₀ y)= courseValue Y H V G ⟨flipMark j K x.val*y.val, paired_forever Y H G j _ _ x.property y.property⟩ := by
  obtain ⟨s,⟨x,rfl⟩,y,rfl⟩ := ((eventually_enclosed Y H G x).and (eventually_enclosed Y H G y)).exists
  let f := aureole K j 0 x.val * y.val
  have h : flipMark j K (ticket Y H G s x.val)*ticket Y H G s y.val=ticket Y H G s f := (paired_today ..).symm
  have he : ∀ (v : flipMark j K (enclose Y H G A₀ false s x).val * (enclose Y H G A₀ false s y).val ∈ V₀ univ), (⟨_,v⟩ : V₀ univ) = ⟨ticket Y H G s f,ticket_loose ..⟩ := fun _ => Subtype.ext h
  rw [he,course_ticket_val,prepaid_enclose,prepaid_enclose,Tower.stems Y H V G.history.circuit j 0 false C]; erw [area0]; rfl -- names

local notation "κ" t:max x:max=> actor Y H t G.history.circuit j 0 false C x
lemma travelling (v : List (Trans j)) (s : ℕ) (z : Cover) (x : Tower.Field Y H s j 0 false) :
    (Z).raw v (fun k=> stamps Λ s z k.val) ( (ν s) x)=(ν s) (transport Y H s j false v (fun k=> z k.val) x) := by
  induction v with
  | nil=>rfl
  | cons k v ih=> rw [Alliance.raw_step,ContinuousLinearMap.comp_apply,ih,stamps_at,on_ladder,sailV_at Y H V s G.history.circuit j 0 false k.val k.property C _ s le_rfl,smill_id]; rfl
lemma rootEstate (s : ℕ) (z : Cover) (x : Tower.Field Y H s j 0 false) (p : 0≤ z j) :
    let t:= (coordinates Λ (stamps Λ s z) j).toNNReal
    E₀ t ((Z).raw (look j) (fun k=> stamps Λ s z k.val) ((ν s) x))= (ν s) (tick Y H s j 0 false (2*(z j).toNat) (transport Y H s j false (look j) (fun k=>z k.val) x)) := by
  have h : (coordinates Λ (stamps Λ s z) j).toNNReal= whenly Gt s (z j).toNat := by
    rw [show coordinates Λ _ j=(bell Gt s (z j)) from rfl]; nth_rw 1 [← Int.toNat_of_nonneg p]; rw [natural_time]; exact Real.toNNReal_coe
  dsimp only; rw [travelling,h,advance_at,limited_time Y H V s G.history.circuit j 0 false C (2*(z j).toNat) le_rfl,amount_reset]

noncomputable def ruler (z : placement Λ) : (A).Op := (E₀ (coordinates Λ z j).toNNReal).comp ((Z).raw (look j) (fun i=>z i.val))
lemma initial_moves (x : Sky (tent Y H)) (p : x∈Domain Y H G false A₀) (z : placement Λ) (v : 0≤ coordinates Λ z j) (t : move K z x∈ V₀ A₀) :
    ruler Y H V G j C z (prepaid Y H V G j C ⟨x,p⟩) = prepaid Y H V G j C ⟨move K z x,t⟩ := by
  obtain ⟨s,⟨z,rfl⟩,f,hF,rfl⟩ := ((stamps_eventually z).and ((domain_eventually Y H G).1 p)).exists
  let f' := reposition K z f
  let h': f'∈ insideAt Λ l K false A₀ s := insideAt_mono (even_flank j (stamps Λ s z) (by rw [zero_add]; exact v)) (here_cov Y H false A₀ s z f hF)
  rw [show (⟨move K (stamps Λ s z) _ , t⟩ : V₀ A₀)=enclose Y H G A₀ false s ⟨f',h'⟩ from Subtype.ext (move_at Y H V G _ s f z rfl), show (⟨_,p⟩ : V₀ A₀) = enclose Y H G A₀ false s ⟨f,hF⟩ from rfl,prepaid_enclose,prepaid_enclose]
  let g := asField Y H j false s ⟨f,hF⟩
  have hz : 0 ≤ z j := (bell_le Gt s 0 (z j)).1 (by change 0 ≤ bell Gt s (z j) at v; unfold bell; simpa [bell] using v)
  unfold ruler; rw [ContinuousLinearMap.comp_apply,rootEstate Y H V G j C s z _ hz]; apply congrArg (ν s)
  let Z' := aptMoves Y H V s G.history j false C g z (z j).toNat (Int.toNat_of_nonneg hz)
  have hv := congrArg Subtype.val Z'
  rw [world_val] at hv
  exact Subtype.ext hv

/-- Full unselected OS Hilbert filled also at arbitrarily late time via PURE SINGLET inputs. -/
lemma advance_dense (r : ℝ) : Dense {x : A | ∃ f : Sky (tent Y H), f ∈ Domain Y H G true (flank j r) ∧ f ∈ D (flank j 0) ∧ ∃ p:f∈ V₀ A₀, prepaid Y H V G j C ⟨f,p⟩=x} := by
  obtain ⟨n,h⟩ := exists_nat_gt (r/(mill Gt 0 : ℝ))
  let t := whenly Gt 0 n; have hp : r ≤ t := by
    refine ((div_lt_iff₀ (show 0 < (mill Gt 0:ℝ) from mill_pos Gt 0)).1 h).le.trans_eq ?_
    simp only [t,whenly]; push_cast; rfl
  let d:= TimeMesh.along Λ j 0 n
  have hd : ruler Y H V G j C d=(S₀).E t := by
    have hf : (fun k:Trans j=> d k.val)=0 := funext fun k=> by unfold d TimeMesh.along; rw [stamps_at,Pi.single_eq_of_ne k.property,notch_zero]; rfl
    unfold ruler; rw [show coordinates Λ d j=(t:ℝ) from TimeMesh.at_self ..,Real.toNNReal_coe,hf,Alliance.raw_zero]; rfl
  apply (((S₀).whole t).dense_image ((S₀).E t).continuous (reserved_arena Y H V G.history G.clipped j C)).mono
  rintro _ ⟨x,h,rfl⟩; obtain ⟨s,h⟩:= Set.mem_iUnion.mp h; obtain ⟨x,rfl⟩:= h; let X:= fromField Y H j s x; let y:= enclose Y H G A₀ true s X
  let f:= y.val; let g:= move K d f
  have ht:= TimeMesh.at_self (Λ:=Λ) j 0 n
  have hb : g∈D (flank j t):= domain_mono Y H G (even_flank j _ (by rw [show (d j).val=(t:ℝ) from ht,zero_add])) (moving Y H V G d f y.property)
  have hv : g∈D A₀:= domain_mono Y H G (TimeMesh.flank_mono j t.property) hb; let v:= domain_loose Y H G A₀ hv
  let u : f∈ V₀ A₀:= domain_loose Y H G _ y.property
  have h : prepaid Y H V G j C ⟨f,u⟩= (ν s) (admit Y H s j x) := prepaid_enclose Y H V G j C s ⟨X.val, insideAt_loose s X.property⟩
  refine ⟨g,domain_mono Y H G (TimeMesh.flank_mono j hp) hb,hv,v,?_⟩
  dsimp only [g]; rw [← initial_moves Y H V G j C f u d (by rw [show coordinates Λ d j=(t:ℝ) from ht]; positivity),h,hd]

end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
