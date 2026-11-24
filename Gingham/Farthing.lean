import YM.SU5.Selected.Contrast
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine.Gingham

open Spine
variable (P:Spine)
local notation "A"=> P.Ensemble 3
local notation "W"=> P.Hil 3
local notation "R"=> P.vacuum 3
local notation "S"=> P.Spectrum0 3

open Set
variable (x : P.Spectrum0 3)
variable {I:Type*} [Finite I]

/-- Finite-list character localization in one mean ground vector (with a cost
    even on operator action, not just expectation). Localize by Urysohn
    near the desired evaluations, then feed to one near-norming vector.
    No qualification on character. -/
lemma embryonic (X:I→A) (d:ℝ)(p:0<d) :
    ∃ v : ↥R, ‖v‖=1 ∧ ∀ i, ‖(X i).val v - (P.chi 3 x (X i)) • v‖≤d := by
 let F(i:I):A:= X i - P.chi 3 x (X i) • 1
 obtain ⟨O,ON,oo,xo⟩:= mem_nhds_iff.mp (eventually_all.mpr (fun i=>
    (P.chi_joint 3 (F i)).norm.continuousAt.eventually
    (ge_mem_nhds (by
      change ‖P.chi 3 x (F i)‖<d/2
      unfold F
      rw [map_sub,map_smul,map_one, smul_eq_mul,mul_one,sub_self,norm_zero]
      exact half_pos p)))
    : ∀ᶠ y:S in 𝓝 x,∀ i, ‖P.chi 3 y (F i)‖ ≤ d/2)
 obtain ⟨f,h₀,h₁,h⟩:=exists_continuous_zero_one_of_isClosed oo.isClosed_compl
    (isClosed_singleton (x:=x)) (by simpa using xo)
 let g:C(S,ℂ):=⟨fun y=> (f y:ℂ), by fun_prop⟩
 have gx:g x=1:=by
    change ((f x:ℝ):ℂ)=1
    rw [show f x=1 from h₁ rfl,Complex.ofReal_one]

 have gz(y:S)(p:y∉O):g y=0:=by
    change ((f y:ℝ):ℂ)=0
    rw [show f y=0 from h₀ p,Complex.ofReal_zero]
 have gs(y:S):‖g y‖≤1:=by
    rw [show g y=((f y:ℝ):ℂ) from rfl,Complex.norm_real,
      Real.norm_of_nonneg (h y).1]
    exact (h y).2
 let J:=gelfandStarTransform A
 have hm : Isometry J:=gelfandTransform_isometry A
 have hn (i:A): ‖J i‖=‖i‖:= hm.norm_map_of_map_zero (map_zero _) i
 let L := J.symm g
 have he: J L=g:=J.apply_symm_apply g
 have hu : 1≤‖L‖:=by
    have h':=g.norm_coe_le_norm x
    rw [gx,norm_one] at h'; rwa [←hn,he]
 have hF(i:I): ‖F i*L‖≤d/2 := by
   rw [← hn]
   refine ((J (F i*L)).norm_le (half_pos p).le).2 (fun y=>?_)
   rw [map_mul,he,ContinuousMap.mul_apply, norm_mul]
   by_cases b:y∈O
   · exact (mul_le_of_le_one_right (norm_nonneg _) (gs y)).trans (ON b i)
   rw [gz y b, norm_zero,mul_zero]; exact (half_pos p).le
 have hw:∃ w:↥R,(1/2:ℝ)*‖w‖<‖L.val w‖:=by
   by_contra! a
   have hz: ‖L.val‖ ≤1/2 := L.val.opNorm_le_bound (by norm_num) a
   change ‖L‖ ≤1/2 at hz
   linarith
 obtain ⟨w,hw⟩:=hw

 let z:=L.val w
 have hp:0< ‖z‖:=lt_of_le_of_lt (by positivity) hw
 let c:ℂ:=((‖z‖⁻¹:ℝ):ℂ)
 have hc:‖c‖= ‖z‖⁻¹:=by simp [c]
 let v:=c • z
 refine ⟨v,?_,fun i=>?_⟩
 · rw [show v=c • z from rfl,norm_smul,hc,inv_mul_cancel₀ hp.ne']
 change ‖(F i).val v‖≤d
 rw [show v=c • z from rfl,map_smul,norm_smul,hc]
 rw [inv_mul_le_iff₀ hp]
 have h₂: ‖(F i).val z‖≤(d/2)*‖w‖:= 
   ((F i*L).val.le_opNorm w).trans (mul_le_mul_of_nonneg_right
      (show ‖(F i*L).val‖≤d/2 from hF i) (norm_nonneg _))
 exact h₂.trans (by
   change d/2*‖w‖ ≤ ‖L.val w‖*d
   nlinarith)


lemma cries (X:I→A) {U:Set (I→ℂ)}
   (op:IsOpen U) (e:(fun i=> P.chi 3 x (X i))∈U) :
   ∃ v: ↥R,(fun i=>inner ℂ v ((X i).val v))∈U:=by
 let d(n:ℕ):ℝ:= 1/(n+1)
 have dp(n): 0<d n:=by unfold d; positivity
 choose v h k using fun n=>embryonic P x X (d n) (dp n)


 have u:Tendsto (fun n i=>inner ℂ (v n) ((X i).val (v n))) atTop
    (𝓝 (fun i=>P.chi 3 x (X i))) := by
   refine tendsto_pi_nhds.mpr fun i=> Metric.tendsto_nhds.mpr fun t pt=>?_
   let b:= P.chi 3 x (X i)
   have H:Tendsto d atTop (𝓝 0):= tendsto_one_div_add_atTop_nhds_zero_nat
   filter_upwards [H.eventually <| gt_mem_nhds pt] with n hn
   change dist (inner ℂ (v n) ((X i).val (v n))) b<t
   have he : inner ℂ (v n) (b • v n)=b:=by
     rw [inner_smul_right,inner_self_eq_norm_sq_to_K,h n]; simp
   rw [dist_eq_norm_sub]
   conv_lhs => arg 1; rhs; rw [←he]
   rw [← inner_sub_right]
   exact ((norm_inner_le_norm ..).trans (by rw [h n,one_mul]; exact k n i)).trans_lt
     (show d n<t from hn)
 obtain ⟨n,hn⟩:=(u.eventually <| op.mem_nhds e).exists
 exact ⟨v n,hn⟩



lemma crying_cards {s w:ℕ} (p:0<w)(F:I→P.Card 3 s w) {U:Set (I→ℂ)}
    (op:IsOpen U)
    (e:(fun i=> P.singleState 3 s x (P.entryTest 3 s (F i)))∈U) :
    ∃ (t:ℕ) (_:s≤t) (v:P.Vox 3 t),
    (fun i=>inner ℂ (P.piece 3 t v)
      (P.Box 3 s w p (F i) (P.piece 3 t v)))∈U := by
 let X:=fun i=> P.reading 3 s (P.entryTest 3 s (F i))


 obtain ⟨v,h⟩:=cries P x X op e
 let Y(i):=P.Box 3 s w p (F i)
 let f (z:W)(i:I):= inner ℂ z (Y i z)
 have hv:f v.val∈U:=by
    have he (i:I) : inner ℂ v ((X i).val v)=f v.val i:=by
      unfold X
      rw [P.at_label,P.compresses 3 s w p,
        ContinuousLinearMap.comp_apply]
      rw [show P.piZero 3=(R).orthogonalProjectionOnto from rfl]
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
      rfl
    rwa [←show (fun i=>_)=f v.val from funext he]
 have o:IsOpen (f ⁻¹' U):= op.preimage (show Continuous f from
    continuous_pi fun i=>continuous_id.inner (Y i).continuous)
 obtain ⟨z,hz',hz⟩:= (sounds P.run P.large P.law P.history.circuit 3
   0 false (P.room 3)).inter_open_nonempty (f ⁻¹' U) o ⟨_,hv⟩
 -- check order
 obtain ⟨r,k⟩:= mem_iUnion.mp hz
 obtain ⟨u,rfl⟩:= k
 let t:=max r s
 have rt:r≤t:=le_max_left ..
 refine ⟨t,le_max_right ..,Raise P.run P.large P.history.circuit 3
   0 false r t rt u,?_⟩
 unfold piece; simp_rw [join_actor P.run P.large P.law]
 exact hz'


