import YM.SU5.Selected.SquareCap
/-! # Election for unbounded levels simultaneous interaction slots
A genuine single sector of this law containing active readings throughout
all scales (quantified here as suitable levels unbounded above).
Note: the first-ever cost placement chosen spatially is **one** pose (internal
supports are those anchored at the selected origin of native resolution),
in application fixed physical separation uses **one s**, not claiming as s
varies the new probes are different placements of that one fixed physical
witness. `Fixture` etc prove that latter witness ALSO propagates up the
resolution hierarchy, in the precise sense specified there (as one coupled
observable). -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 330000
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
local notation "AH"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Theory CF.Pannier.Chancel Set
variable (R : Arena Y H G.history.circuit j 0 false)
local notation "T"=>catalog Y H V G j false R
local notation "μ₀"=>residents Y H V G false j R
local notation "M"=>markE Y H V G false j R
variable {d q w s:ℕ}

private lemma threshold {Y₁:Type}[MeasurableSpace Y₁]{μ:Measure Y₁}[IsProbabilityMeasure μ]
    (f:SU.Slot→ Y₁→ℝ)(p:∀i x,0≤f i x)(v:∀ i,Measurable (f i))(h:∀ i, Integrable (f i) μ)
    (e:∀ i, (∫ x,f i x ∂μ)≤1/1000) : ∃ A:Set Y₁,MeasurableSet A ∧ μ.real A ≥ 1/2 ∧ ∀ x∈A,∀ i,f i x < 1/4:=by
  let F (x:Y₁):=∑ i, f i x
  let U:= {x| 1/4 ≤ F x}
  have hv:MeasurableSet U:= measurableSet_le measurable_const (Finset.measurable_fun_sum _ (fun i _=> v i)) -- name
  have ht:Integrable F μ:= integrable_finsetSum _ (fun i _=> h i)
  have hp: (1/4:ℝ)* μ.real U≤∑ _:SU.Slot, (1/1000:ℝ) := le_trans (mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun x=>show 0≤F x from sum_nonneg (fun i _=>p i x)) ht (1/4)) (by unfold F; rw [integral_finsetSum _ (fun i _=>h i)]; exact sum_le_sum fun i _=>e i)
  rw [sum_const,card_univ,SU.slots,nsmul_eq_mul] at hp
  refine ⟨Uᶜ,hv.compl,?_,fun x p' i=>?_⟩
  · rw [measureReal_compl hv,probReal_univ]; push_cast at hp; linarith
  exact lt_of_le_of_lt (show f i x≤ F x from single_le_sum (fun i _ => p i x) (mem_univ _)) (lt_of_not_ge p')

variable (Z J γ : ℝ)
structure Fair (x:Resident (catalog Y H V G j false R))(d q w s:ℕ) : Prop where
  attends (z:SU.Slot) : ∃ (f:observable K true)(g:Family (tent Y H)),
    Papal.Squared Y H E z j q d w s f.val g ∧ ‖M x s (restore f)‖ > 1/2 ∧ ‖E s f.val‖ > 3/4

lemma presentFair (p:Papal.Policy Y H q d w Z J γ) :
    ∀ᶠ s in atTop, ∃ A':Set (Resident T), MeasurableSet A' ∧ (μ₀).real A' ≥ 1/2 ∧ ∀ x∈A', Fair Y H V G j R x d q w s := by
  filter_upwards [eventually_all.mpr (fun z:SU.Slot=> Papal.squarePaid Y H j z V p)] with s Pp
  choose f g h using Pp
  let F(z:SU.Slot) := observP Y H j s d q w z (h z)
  let W (z:SU.Slot)(a:Resident T):= 1+M a s (restore (F z))
  let Q(z:SU.Slot)(a:Resident T):= ‖W z a‖^2
  have he(z:SU.Slot):=(certifiedPower Y H V G j s R d q w z (h z))
  have Hc(z:SU.Slot):Continuous (Q z) := (continuous_const.add (mean_admit Y H V G false j R s (restore (F z)))).norm.pow _
  obtain ⟨U,c,c',u⟩:= threshold (μ:=μ₀) Q (fun i x=>by unfold Q; positivity) (fun i=>(Hc i).measurable) (fun i=>(Hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun i=>(he i).1)
  refine ⟨U,c,c',fun x t=>⟨fun z=>?_⟩⟩
  let V' := M x s (restore (F z)); have hv: ‖1+V'‖^2<1/4:=u x t z
  have hf (x:ℂ): 1≤ ‖1+x‖+‖x‖:= le_of_eq (norm_one (α:=ℂ)).symm|>.trans (by nth_rw 1 [← add_sub_cancel_right 1 x]; exact norm_sub_le ..) -- tune
  have hp: ‖1+E s (F z).val‖^2≤ 1/1000:=(he z).2
  exact ⟨F z,g z,h z,(by change 1/2 < ‖V'‖; nlinarith only [hv,hf V',norm_nonneg (1+V')]),(by nlinarith only [hp,hf (E s (F z).val),norm_nonneg (1+E s (F z).val)])⟩

private lemma springs {Y₁ : Type}[MeasurableSpace Y₁](μ:Measure Y₁)[IsProbabilityMeasure μ]
    (G':ℕ→Y₁→ Prop)(g: ∀ᶠ s in atTop, ∃ A:Set Y₁, MeasurableSet A ∧ μ.real A≥1/2 ∧ ∀i∈A,G' s i) :
    ∃ A:Set Y₁, MeasurableSet A ∧ μ A≥ENNReal.ofReal (1/2) ∧ ∀x∈A, ∃ᶠ s in atTop, G' s x := by
  classical
  choose A s h using fun x:ℕ=> (g.and (eventually_ge_atTop x)).exists -- order? x -> ∃ s(...)∧_; A:ℕ→ℕ
  choose U u hn v using s
  let Q (n:ℕ):Set Y₁:=⋃ m≥ n,U m
  have hm :Antitone Q:=fun i j e a ha=>by
    obtain ⟨t,p⟩:= mem_iUnion.mp ha; obtain ⟨z,l⟩:=mem_iUnion.mp p; exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨e.trans z,l⟩⟩
  have hv(s):MeasurableSet (Q s):= MeasurableSet.iUnion fun i=> MeasurableSet.iUnion fun _=> u i
  have hu(s:ℕ): μ (Q s)≥ ENNReal.ofReal (1/2):= ((ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ (U s))).mpr (hn s)).trans (measure_mono (show U s⊆Q s from fun i v=> mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨le_rfl,v⟩⟩))
  refine ⟨⋂ i,Q i, MeasurableSet.iInter hv,(Antitone.measure_iInter hm (fun s=>(hv s).nullMeasurableSet) ⟨0,measure_ne_top μ _⟩).ge.trans' (le_iInf hu),?_⟩
  intro x hx; refine frequently_atTop.mpr fun s=>?_
  obtain ⟨z,p⟩:= mem_iUnion.mp (mem_iInter.mp hx s); obtain ⟨n,l⟩:= mem_iUnion.mp p
  exact ⟨A z, n.trans (h z), v _ _ l⟩

lemma concert (p:Papal.Policy Y H q d w Z J γ) : ∃ S:Set (Resident T), MeasurableSet S ∧ (μ₀) S≥ ENNReal.ofReal (1/2) ∧
    ∀ x∈S,∃ᶠ s in atTop,Fair Y H V G j R x d q w s:= springs (μ₀) _ (presentFair Y H V G j R Z J γ p)
variable (U : ∀ i:Axis, Arena Y H G.history.circuit i 0 false)
theorem jointly (p:Papal.Policy Y H q d w Z J γ) : ∃ x, ExtremeReceipt Y H V G j U x ∧
      (∃ᶠ s in atTop,Fair Y H V G j (U j) x d q w s) := by
  obtain ⟨S,v,f,h⟩:= concert Y H V G j (U j) Z J γ p
  let μ:= residents Y H V G false j (U j)
  obtain ⟨i,hi,hx⟩:= Measure.exists_mem_of_measure_ne_zero_of_ae (show μ S≠0 from (lt_of_lt_of_le (by positivity) f).ne') (ae_restrict_of_ae (extremal_usual Y H V G j U)); exact ⟨i,hx,h i hi⟩
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.jointly
