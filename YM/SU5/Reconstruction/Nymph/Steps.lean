import YM.SU5.Reconstruction.Seams.AtState
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
namespace Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

-- smaller than CP2 mesh, still a pitch program (two matter pitches)
def dainty (Λ:Preparation) : Mesh:=⟨(timeMesh Λ).L,(timeMesh Λ).Llarge,2,by norm_num⟩
local notation "V₀" => dainty Λ
abbrev perch (Λ:Preparation) := marks (dainty Λ)
local notation "δ" => perch Λ
@[simp] lemma glint_perch (Λ:Preparation) (s n:ℕ) : whenly (dainty Λ) s n = pitchMill Λ s (2*n):= by
  simp only [whenly,dainty,pitchMill,mill,timeMesh,Nat.cast_mul,Nat.cast_ofNat]; ring
lemma ruler_perch (Λ:Preparation) (s:ℕ)(v:ℤ) : bell (dainty Λ) s v= glint Λ s (2*v):=by
  change (v:ℝ) * ((2/(Λ.R.L.val:ℝ≥0)^s:ℝ≥0):ℝ)=((2*v:ℤ):ℝ)/(Λ.R.L.val:ℝ)^s; push_cast; ring
lemma as_deep (Λ:Preparation) (s:ℕ)(z:ℤ) : bell (timeMesh Λ) s z= bell (dainty Λ) s ((4*Λ.block.val)*z):=by
  change (z:ℝ)* (((8*(Λ.block.val:ℝ≥0))/(Λ.R.L.val:ℝ≥0)^s:ℝ≥0):ℝ)= (( (4*Λ.block.val)*z:ℤ):ℝ) * ((2/(Λ.R.L.val:ℝ≥0)^s:ℝ≥0):ℝ); push_cast; ring
lemma conductor (Λ:Preparation) : marks (timeMesh Λ) ≤ marks (dainty Λ) := by
  intro x p
  let v : marks (timeMesh Λ) := ⟨x,p⟩
  obtain ⟨s,p,h⟩:= notch_exists (timeMesh Λ) v
  rw [← show bell (timeMesh Λ) s p=x from congrArg Subtype.val h, as_deep]; exact (notch _ _ _).property
def finerNow (Λ:Preparation): marks (timeMesh Λ) →+ marks (dainty Λ):= AddSubgroup.inclusion (conductor Λ)
lemma rose (Λ:Preparation)(s:ℕ)(z:ℤ): finerNow Λ (notch (timeMesh Λ) s z)=notch (dainty Λ) s ((4*Λ.block.val)*z) :=Subtype.ext (as_deep ..)

lemma eventually_toned (v:δ): ∀ᶠ s in atTop,∃ n:ℤ, notch (dainty Λ) s n=v:=by
  obtain ⟨t,z,rfl⟩:= notch_exists _ v; filter_upwards [eventually_ge_atTop t] with s h; exact ⟨_,notch_up (dainty Λ) t s h z⟩
noncomputable def beatAt (v: perch Λ) (s:ℕ) := if h:∃ n:ℤ, notch (dainty Λ) s n=v then h.choose else 0
@[simp] lemma beats_here (v:δ) {s:ℕ} {n:ℤ} (h:notch (dainty Λ) s n=v) : beatAt v s=n:=by unfold beatAt; rw [dif_pos ⟨n,h⟩]; apply notch_tight _ s; rw [h]; exact Exists.choose_spec (p:=fun n=>notch (dainty Λ) s n=v) (by exact ⟨n,h⟩)

lemma cruise_inside (J:Calibration) (s:ℕ) (j:Axis)(z:ℤ)(x:Dome J)(p:x ∈ insideAt Λ l J q y s) : cruise j J z x∈ insideAt Λ l J q (slides (eject j (glint Λ s z)) y) s := by
  have ht:slides (eject j (glint Λ s z)) y= steer j (glint Λ s z) '' y:=by
    unfold slides; congr 1; funext x i; rw [steer]; by_cases h:i=j <;> simp [h]
  rw [ht,insideAt]; have he:= Algebra.mem_inf.mp (show x ∈ keep Λ l s J true (handstamp y)⊓ _ from p); apply Algebra.mem_inf.mpr; refine ⟨hand_steer j J z Λ l s y he.1,?_⟩
  cases q
  · exact Algebra.mem_top
  exact aureoleEnclave J j z (aureoleEnclave J j 0 he.2)

lemma climb_one (s t:ℕ) (j:Axis)(z:ℤ)(f:Dome K) : spreadTo Y H G s t (cruise j K (2*z) f)= cruise j K (2*castor (dainty Λ) s t z) (spreadTo Y H G s t f) := by
  apply Subtype.ext
  rw [spreadTo_val, sailsTo,sailsTo, spreadTo_val, acreage_X Y H G j s (t-s) ((marque ..).1 f.property),castor,show (dainty Λ).L=Λ.R.L.val from rfl]; ring_nf

noncomputable def stride (J:Calibration) (j:Axis)(a: perch Λ): Sky J →ₗ[ℂ] Sky J:= skySemilinear (fun s=> (cruise j J (2*beatAt a s)).toLinearMap)
@[simp] lemma stride_coe (j:Axis)(x:δ) (f : ℕ→ Dome J): stride J j x (↑f)= ↑(fun i=> cruise j J (2*beatAt x i) (f i)):= rfl
lemma stride_mark (j:Axis)(x:δ)(s:ℕ)(z:ℤ)(p : notch (dainty Λ) s z=x)(f:Dome (tent Y H)) : stride (tent Y H) j x (ticket Y H G s f)= ticket Y H G s (cruise j K (2*z) f) := by
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_ge_atTop s] with t h
  change cruise j K (2*beatAt x t) (spreadTo Y H G s t f) = _; rw [beats_here x ((notch_up (dainty Λ) s t h z).trans p), ← climb_one]
lemma stride_region (j:Axis)(x:δ)(f:Sky (tent Y H))(p:f∈ D q y): stride (tent Y H) j x f ∈ D q (slides (eject j (x:ℝ)) y) := by
  obtain ⟨s,⟨n,h⟩,v,b,rfl⟩:= ((eventually_toned x).and ((domain_eventually Y H G).1 p)).exists
  rw [stride_mark Y H G j x s n h, show (x:ℝ)= glint Λ s (2*n) from (congrArg Subtype.val h).symm.trans (ruler_perch ..)]; exact ticket_mem Y H G (cruise_inside K s j (2*n) v b)

@[simp] lemma stride_zero (Λ:Preparation)(j:Axis)(f:Sky J):stride J j (0:perch Λ) f=f:=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr (Eventually.of_forall fun s=>?_); change cruise j J (2*beatAt (0:perch Λ) s) (f s)= f s; rw [beats_here _ (notch_zero _ _),mul_zero,sailsBack]
lemma stride_add (j:Axis)(x y:δ)(f:Sky J): stride J j x (stride J j y f)= stride J j (x+y) f:=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr ?_; filter_upwards [eventually_toned x,eventually_toned y] with s ⟨v,h⟩ ⟨w,t⟩
  change cruise j J (2*beatAt x s) (cruise j J (2*beatAt y s) (f s))=cruise j J (2*beatAt (x+y) s) (f s); rw [beats_here _ h,beats_here _ t, beats_here (x+y) ((notch_add (dainty Λ) s v w).trans (congrArg₂ (·+·) h t)), mul_add,sailsBy]
lemma stride_cross (x y:δ)(j i:Axis)(f:Sky J): stride J j x (stride J i y f)=stride J i y (stride J j x f):=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr (Eventually.of_forall fun s=> Subtype.ext ?_)
  exact Tower.twin_slide j i _ _ ((marque ..).1 (f s).property).paid.choose_spec
lemma stride_mul (x:δ) (j:Axis)(f g:Sky J) : stride J j x (f*g)= stride J j x f* stride J j x g:= by
  let H := fun i : ℕ=> ⇑(cruise j J (2*beatAt x i))
  change skyChange H (f*g)=skyChange H f *skyChange H g
  exact sky_change_mul H (Eventually.of_forall fun i : ℕ=> fun p w=> map_mul (cruise j J (2*beatAt x i)) p w) f g
lemma stride_flip (x:δ)(j:Axis)(f:Sky J): stride J j x (flipMark j J f)= flipMark j J (stride J j (-x) f):=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr ?_; filter_upwards [eventually_toned x] with s ⟨v,h⟩
  change cruise j J (2*beatAt x s) (aureole J j 0 (f s))= aureole J j 0 (cruise j J (2*beatAt (-x) s) (f s)); rw [beats_here _ h,beats_here (-x) (show notch (dainty Λ) s (-v)= -x from ?_)]
  · apply Subtype.ext; rw [mul_neg]; exact Tower.chime_diag J j _ 0 ((marque ..).1 (f s).property).paid.choose_spec
  apply Subtype.ext; rw [←h]; change bell _ _ _ = - bell _ _ _; simp [bell]
lemma stride_other (x:δ)(j i:Axis)(h:j≠i)(f:Sky J): stride J j x (flipMark i J f)= flipMark i J (stride J j x f):=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr (Eventually.of_forall fun s=> Subtype.ext ?_)
  exact Tower.straddle _ _ h _ _ ((marque ..).1 (f s).property).paid.choose_spec
-- real spatial contact needs bigger purchase. but at earlier stamps EXACT agreement as test objects
lemma earlier_here (j:Axis)(x:marks (timeMesh Λ)) : stride K j (finerNow Λ x) = FirstWindows.move K (eject j x) := by
  ext1 f; induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr ?_; filter_upwards [stamps_eventually (eject j x)] with s ⟨v,h⟩
  let z:= v j; have t : notch (timeMesh Λ) s z=x:= by unfold z; rw [← stamps_at]; exact (congrFun h j).trans (eject_at j x) -- z unfold tune
  have ht:v=eject j z:= stamp_injective Λ s (by rw [h,stamps_eject, t]);
  change cruise j K (2*beatAt (finerNow Λ x) s) (f s)=reposition K (chooseStamp (eject j x) s) (f s); rw [chooseStamp_eq h, beats_here (finerNow Λ x) ((rose Λ s z).symm.trans (congrArg (finerNow Λ) t)),ht]
  apply Subtype.ext; rw [sailsTo, chart_eject, relocate]; unfold gaugeT Heat.gaugeShift; rw [show (tent Y H).B=Λ.block from rfl]; ring_nf
end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
