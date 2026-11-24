import YM.SU5.Selected.Squaring
/-! # Upper square bill and probability election on any one axis.
All SU slots (45 initial components in both charge families). Can pick a
phase where all 6 active together at unbounded scales. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Theory Set CF.Pannier.Chancel
variable (s : ℕ)
local notation "T"=> catalog Y H V G j strict C
local notation "TN"=>seal₀ Y H V G j strict C s
local notation "μ"=>residents Y H V G strict j C

set_option maxHeartbeats 1200000
lemma eval_average (a:T) : (∫ x, eye x a∂μ)= inner ℂ Ω (a.val Ω):= (resident_mark Y H V G j strict C j C a).trans (bar_move Y H V G j strict C j C a)
lemma mom (f:observable (tent Y H) strict) :
    (∫ x, (‖eye x (TN f)‖)^2∂μ)= ‖(P s) f Ω‖^2:=by
  let a:= TN f
  have hu: ∀ x:Resident T, eye x (star a*a)=(((‖eye x a‖:ℝ)^2:ℝ):ℂ):=fun x=> EyeSq a x
  have Q: (∫ x, eye x (star a*a)∂μ)=(((‖a.val Ω‖:ℝ)^2:ℝ):ℂ):=by
    rw [eval_average]
    change inner ℂ Ω ((a.val).adjoint (a.val Ω))=_; rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [hu] at Q; rw [integral_complex_ofReal] at Q; exact Complex.ofReal_injective Q
where EyeSq {Tq:Type} [CommCStarAlgebra Tq] (a:Tq) (x:Resident Tq) : eye x (star a*a)=(((‖eye x a‖:ℝ)^2:ℝ):ℂ):=by rw [map_mul,map_star,mul_comm,Complex.star_def,Complex.mul_conj']; push_cast; rfl

-- pack false election interfaces, independent of arbitrary late continuation
section fuller
variable (T' : Arena Y H G.history.circuit j 0 false)
local notation "RS"=> catalog Y H V G j false T'
local notation "ν"=>residents Y H V G false j T'
local notation "FR"=> Tower.Field Y H s j 0 false
local notation "Θ"=>mirror K j 0
local notation "SX"=> seal₀ Y H V G j false T' s
variable (d q w :ℕ)(z:SU.Slot) {f g: Family (tent Y H)}
variable (A0:Papal.Squared Y H E z j q d w s f g)
local notation "δ"=> payout d q w
local notation "o₀"=>scheduled δ (addgap K)
local notation "S₀"=> Sen (o₀) δ
noncomputable def observP : observable K true:=⟨f,aux_test (FilTest A0.first).widen,fun _=> A0.neutralF⟩
local notation "δf"=>observP Y H j s d q w z A0
lemma certifiedPower :
    (∫ x, ‖1+markE Y H V G false j T' x s (restore δf)‖^2∂ν) ≤ 1/1000 ∧
    ‖1+E s f‖^2 ≤ 1/1000 := by
  have hf:= FilTest A0.first|>.widen
  have hg:= (FilTest A0.scalarTest).widen
  have hh:InTest K true (S₀) false (1+g):= InTest.add InTest.one hg
  let a:FR:=⟨(1:Family K)+g,(purpose_ok ..).2 ⟨⟨S₀,hh,by rw [area0]; exact placement j Y H δ⟩,by simp⟩⟩
  let Ω₀:= seat0 Y H V G.history j false T'; let W:= Aurora Y H V G.history j false T'
  let k:= actor Y H s G.history.circuit j 0 false T' a
  have hp: ‖k‖^2≤1/1000:=by
    have he : inner ℂ k k= E s (Θ a.val*a.val) := (stems Y H V G.history.circuit j (0:ℤ) false T' s a a).trans (by rw [area0])
    rw [inner_self_eq_norm_sq_to_K] at he
    have ht: ‖E s (Θ a.val*a.val)‖≤1/1000:= A0.roof
    rw [←he,norm_pow] at ht; change ‖((‖k‖:ℝ):ℂ)‖^2 ≤_ at ht; simpa using ht
  obtain ⟨m,v,p,t⟩:= A0.same
  let b:= SX (restore δf); let y:observable K false:=observe (aux_test hg)
  have he:b=SX y:= reynolds_exact Y H V G j T' S₀ s m v hg hf t p
  let z':= observableOf Y H j false s a; let h':= SX z'
  have hT:1+b=h':= by
    rw [he]; let u:= observe (show TestFamily (tent Y H) true 1 from TestFamily.oneT) -- tune
    apply Subtype.ext; change (1: W →L[ℂ] W) + _ =_
    have hN:=cap_unit Y H V G j false T' s u rfl
    exact (congrArg (fun a: W →L[ℂ] W => a + (cap Y H V s G.history G.clipped j false T' y)) hN.symm).trans (cap_add Y H V G j false T' s z' u y rfl).symm -- tune
  have hx:‖h'.val Ω₀‖^2 ≤1/1000:=by
    apply le_trans _ hp
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2; rw [show h'.val Ω₀=W.orthogonalProjectionOnto k from cap_actor Y H V G j false T' s a]; apply Submodule.norm_orthogonalProjectionOnto_apply_le
  constructor
  · simp_rw [show ∀ x,1+markE Y H V G false j T' x s (restore δf)=eye x h' from (fun x=> by rw [←hT,map_add,map_one]; rfl)]
    rw [show (∫ x :Resident RS, ‖eye x h'‖^2∂ν)=_ from mom Y H V G j false T' s z']; exact hx
  have hv:= Vacancy.inspected (F:=restore δf) Y H V s G.history G.clipped j false T'; have hu: ‖Ω₀‖=1:= by unfold Ω₀; exact (bank Y H V G j false T' j T').unit
  have heq:inner ℂ Ω₀ (h'.val Ω₀)=1+E s f:=by
    rw [← hT]; change inner ℂ Ω₀ (Ω₀+b.val Ω₀)=_; rw [inner_add_right,inner_self_eq_norm_sq_to_K,hu]; rw [show inner ℂ Ω₀ (b.val Ω₀)=E s f from hv]; simp -- hv tune
  rw [←heq]; exact (pow_le_pow_left₀ (norm_nonneg _) ((norm_inner_le_norm ..).trans_eq (by rw [hu,one_mul])) _).trans hx
end fuller
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.certifiedPower
