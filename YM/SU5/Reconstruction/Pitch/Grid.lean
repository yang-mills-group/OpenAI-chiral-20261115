import YM.SU5.Reconstruction.UVPrice.CostHere
/-!
# Native position increments on the calibrated hierarchy 
No identification with earlier $2\Gamma$. Extend Nymph.Steps to all $\Gamma$ now verifying 
relations for ALL pitches on the most general philological treks on real law. 
-/
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
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

def loomD (Λ:Preparation) : Mesh:=⟨(timeMesh Λ).L,(timeMesh Λ).Llarge,1,by norm_num⟩
local notation "V₀" => loomD Λ
abbrev weft (Λ:Preparation) := marks (loomD Λ)
local notation "δ" => weft Λ
@[simp] lemma glint_weft (Λ:Preparation) (s n:ℕ) : whenly (loomD Λ) s n = pitchMill Λ s n:= by
  simp only [whenly,loomD,pitchMill,mill,timeMesh]; ring
lemma ruler_weft (Λ:Preparation) (s:ℕ)(v:ℤ) : bell (loomD Λ) s v= glint Λ s v:=by
  change (v:ℝ) * ((1/(Λ.R.L.val:ℝ≥0)^s:ℝ≥0):ℝ)=(v:ℝ)/(Λ.R.L.val:ℝ)^s; push_cast; ring
lemma eventually_pitched (v:δ): ∀ᶠ s in atTop,∃ n:ℤ, notch (loomD Λ) s n=v:=by
  obtain ⟨t,z,rfl⟩:= notch_exists _ v; filter_upwards [eventually_ge_atTop t] with s h; exact ⟨_,notch_up (loomD Λ) t s h z⟩
noncomputable def pitchBeat (v: weft Λ) (s:ℕ) := if h:∃ n:ℤ, notch (loomD Λ) s n=v then h.choose else 0
@[simp] lemma beats_here (v:δ) {s:ℕ} {n:ℤ} (h:notch (loomD Λ) s n=v) : pitchBeat v s=n:=by unfold pitchBeat; rw [dif_pos ⟨n,h⟩]; apply notch_tight _ s; rw [h]; exact Exists.choose_spec (p:=fun n=>notch (loomD Λ) s n=v) (by exact ⟨n,h⟩)

lemma cruise_fit (J:Calibration) (s:ℕ) (j:Axis)(z:ℤ)(x:Dome J)(p:x ∈ insideAt Λ l J q y s) : cruise j J z x∈ insideAt Λ l J q (slides (eject j (glint Λ s z)) y) s := by
  have ht:slides (eject j (glint Λ s z)) y= steer j (glint Λ s z) '' y:=by
    unfold slides; congr 1; funext x i; rw [steer]; by_cases h:i=j <;> simp [h]
  rw [ht,insideAt]; have he:= Algebra.mem_inf.mp (show x ∈ keep Λ l s J true (handstamp y)⊓ _ from p); apply Algebra.mem_inf.mpr; refine ⟨hand_steer j J z Λ l s y he.1,?_⟩
  cases q
  · exact Algebra.mem_top
  exact aureoleEnclave J j z (aureoleEnclave J j 0 he.2)

lemma climb_all (s t:ℕ) (j:Axis)(z:ℤ)(f:Dome K) : spreadTo Y H G s t (cruise j K z f)= cruise j K (castor (loomD Λ) s t z) (spreadTo Y H G s t f) := by
  apply Subtype.ext
  rw [spreadTo_val, sailsTo,sailsTo, spreadTo_val, acreage_X Y H G j s (t-s) ((marque ..).1 f.property),castor,show (loomD Λ).L=Λ.R.L.val from rfl]

noncomputable def trek (J:Calibration) (j:Axis)(a: weft Λ): Sky J →ₗ[ℂ] Sky J:= skySemilinear (fun s=> (cruise j J (pitchBeat a s)).toLinearMap)
@[simp] lemma trek_coe (j:Axis)(x:δ) (f : ℕ→ Dome J): trek J j x (↑f)= ↑(fun i=> cruise j J (pitchBeat x i) (f i)):= rfl
lemma trek_mark (j:Axis)(x:δ)(s:ℕ)(z:ℤ)(p : notch (loomD Λ) s z=x)(f:Dome (tent Y H)) : trek (tent Y H) j x (ticket Y H G s f)= ticket Y H G s (cruise j K z f) := by
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_ge_atTop s] with t h
  change cruise j K (pitchBeat x t) (spreadTo Y H G s t f) = _; rw [beats_here x ((notch_up (loomD Λ) s t h z).trans p), ← climb_all]
lemma trek_region (j:Axis)(x:δ)(f:Sky (tent Y H))(p:f∈ D q y): trek (tent Y H) j x f ∈ D q (slides (eject j (x:ℝ)) y) := by
  obtain ⟨s,⟨n,h⟩,v,b,rfl⟩:= ((eventually_pitched x).and ((domain_eventually Y H G).1 p)).exists
  rw [trek_mark Y H G j x s n h, show (x:ℝ)= glint Λ s n from (congrArg Subtype.val h).symm.trans (ruler_weft ..)]; exact ticket_mem Y H G (cruise_fit K s j n v b)

@[simp] lemma trek_zero (Λ:Preparation)(j:Axis)(f:Sky J):trek J j (0:weft Λ) f=f:=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr (Eventually.of_forall fun s=>?_); change cruise j J (pitchBeat (0:weft Λ) s) (f s)= f s; rw [beats_here _ (notch_zero _ _),sailsBack]
lemma trek_add (j:Axis)(x y:δ)(f:Sky J): trek J j x (trek J j y f)= trek J j (x+y) f:=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr ?_; filter_upwards [eventually_pitched x,eventually_pitched y] with s ⟨v,h⟩ ⟨w,t⟩
  change cruise j J (pitchBeat x s) (cruise j J (pitchBeat y s) (f s))=cruise j J (pitchBeat (x+y) s) (f s); rw [beats_here _ h,beats_here _ t, beats_here (x+y) ((notch_add (loomD Λ) s v w).trans (congrArg₂ (·+·) h t)),sailsBy]
lemma trek_cross (x y:δ)(j i:Axis)(f:Sky J): trek J j x (trek J i y f)=trek J i y (trek J j x f):=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr (Eventually.of_forall fun s=> Subtype.ext ?_)
  exact Tower.twin_slide j i _ _ ((marque ..).1 (f s).property).paid.choose_spec
lemma trek_mul (x:δ) (j:Axis)(f g:Sky J) : trek J j x (f*g)= trek J j x f* trek J j x g:= by
  let H := fun i : ℕ=> ⇑(cruise j J (pitchBeat x i))
  change skyChange H (f*g)=skyChange H f *skyChange H g
  exact sky_change_mul H (Eventually.of_forall fun i : ℕ=> fun p w=> map_mul (cruise j J (pitchBeat x i)) p w) f g
lemma trek_flip (x:δ)(j:Axis)(f:Sky J): trek J j x (flipMark j J f)= flipMark j J (trek J j (-x) f):=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr ?_; filter_upwards [eventually_pitched x] with s ⟨v,h⟩
  change cruise j J (pitchBeat x s) (aureole J j 0 (f s))= aureole J j 0 (cruise j J (pitchBeat (-x) s) (f s)); rw [beats_here _ h,beats_here (-x) (show notch (loomD Λ) s (-v)= -x from ?_)]
  · apply Subtype.ext; exact Tower.chime_diag J j _ 0 ((marque ..).1 (f s).property).paid.choose_spec
  apply Subtype.ext; rw [←h]; change bell _ _ _ = - bell _ _ _; simp [bell]
lemma trek_other (x:δ)(j i:Axis)(h:j≠i)(f:Sky J): trek J j x (flipMark i J f)= flipMark i J (trek J j x f):=by
  induction f using Filter.Germ.inductionOn with | _ f=>?_
  refine Filter.Germ.coe_eq.mpr (Eventually.of_forall fun s=> Subtype.ext ?_)
  exact Tower.straddle _ _ h _ _ ((marque ..).1 (f s).property).paid.choose_spec
local notation "τ′" => marks (timeMesh Λ)
local notation "τ" => marks (dainty Λ)
lemma tone (Λ:Preparation) (s:ℕ)(z:ℤ): bell (dainty Λ) s z= bell (loomD Λ) s (2*z):=(ruler_perch ..).trans (ruler_weft ..).symm
lemma admits (Λ:Preparation): marks (dainty Λ) ≤ marks (loomD Λ):=by
 intro x p; obtain ⟨s,v,h⟩:= notch_exists (dainty Λ) ⟨x,p⟩
 have h':bell (dainty Λ) s v=x:=congrArg Subtype.val h; rw [←h',tone]; exact (notch (loomD Λ) s (2*v)).property
def accept (Λ:Preparation): marks (dainty Λ) →+ marks (loomD Λ):= AddSubgroup.inclusion (admits Λ)
lemma admits_pitch (Λ:Preparation) (s:ℕ) (v:ℤ) : (accept Λ) (notch (dainty Λ) s v) = notch (loomD Λ) s (2*v) := Subtype.ext (tone ..)
lemma advance_even (a:Axis)(x:τ): trek J a (accept Λ x)= stride J a x:=by
 ext1 f; induction f using Filter.Germ.inductionOn with |_ f=>?_
 refine Filter.Germ.coe_eq.mpr ?_; filter_upwards [eventually_toned x] with s ⟨v,h⟩
 change cruise a J (pitchBeat ((accept Λ) x) s) (f s) = cruise a J (2*Nymph.beatAt x s) (f s)
 rw [Pitch.beats_here _ ((admits_pitch Λ s v).symm.trans (congrArg (accept Λ) h)), Nymph.beats_here x h]
lemma advance_first (a:Axis)(x:τ′): trek (tent Y H) a (accept Λ (finerNow Λ x)) = move K (eject a x) := (advance_even ..).trans (earlier_here ..)

-- factor through parity. Need exact representative at one pitch.
lemma duo (p:δ) : ∃ t: marks (dainty Λ), accept Λ t=p+p:=by
 obtain ⟨s,v,rfl⟩:= notch_exists (loomD Λ) p; exact ⟨_,(admits_pitch Λ s v).trans (by rw [two_mul,notch_add])⟩
lemma twinD (p:τ): ∃ t: weft Λ,accept Λ p=t+t:=by
 obtain ⟨s,v,rfl⟩:= notch_exists (dainty Λ) p; exact ⟨_,(admits_pitch Λ s v).trans (by rw [two_mul,notch_add])⟩
noncomputable def eyeD(Λ:Preparation): weft Λ:= notch (loomD Λ) 0 1
lemma eye_steps (Λ:Preparation): (eyeD Λ:ℝ)=1:= by change bell (loomD Λ) _ _=_; simp [bell,mill,loomD]

lemma eyeD_at {t:ℕ}: eyeD Λ= notch (loomD Λ) t ((Λ.R.L.val:ℤ)^t):=by
 have h:= (notch_up (loomD Λ) 0 t (Nat.zero_le t) 1).symm; rwa [castor,show (loomD Λ).L=Λ.R.L.val from rfl,Nat.sub_zero,mul_one] at h
lemma eyeD_odd (Λ:Preparation) : ¬ ∃ t:perch Λ, accept Λ t=eyeD Λ:= by
 rintro ⟨t,h⟩; obtain ⟨s,v,rfl⟩:= notch_exists (dainty Λ) t; rw [admits_pitch, eyeD_at (t:=s)] at h
 obtain ⟨w,p⟩:= (@Odd.pow ℤ _ _ s Λ.R.odd_side.natCast) -- cast
 have x:= notch_tight _ _ h; omega
lemma couple (p:δ): ∃ q: perch Λ,p=accept Λ q ∨ p= eyeD Λ+accept Λ q:=by
 obtain ⟨s,v,rfl⟩:= notch_exists (loomD Λ) p
 obtain ⟨w,h⟩:= (@Odd.pow ℤ _ _ s Λ.R.odd_side.natCast) -- cast
 by_cases g:v%2=0
 · refine ⟨notch (dainty Λ) s (v/2),Or.inl ?_⟩; rw [admits_pitch]; exact congrArg _ (show v=_ from by omega)
 refine ⟨notch (dainty Λ) s ((v-(Λ.R.L.val:ℤ)^s)/2),Or.inr ?_⟩; rw [eyeD_at (t:=s),admits_pitch,← notch_add]; exact congrArg _ (show v=_ from by omega)
-- keep regions rigid and commute with flips etc independent of price
lemma forward_bar (x:δ)(j:Axis)(a b:ℝ) (p:b ≤ a+(x:ℝ)) (f:Sky (tent Y H))(h:f∈D q (flank j a)) : trek K j x f∈D q (flank j b):=by
 apply domain_mono Y H G _ (trek_region Y H G j x f h); rintro _ ⟨v,h,rfl⟩; change b≤v j+eject j (x:ℝ) j; rw [eject_at]; exact p.trans (add_le_add_left (show _≤v j from h) _)
lemma free_play (x:δ)(j:Axis)(f:Sky (tent Y H))(h:f∈D q Set.univ): trek K j x f∈D q Set.univ:=by
 have he:= trek_region Y H G j x f h; rwa [slides_univ] at he
lemma spectator_play (x:δ)(j i: Axis)(e:j≠i)(a:ℝ)(f:Sky (tent Y H))(h:f∈D q (flank j a)): trek K i x f∈ D q (flank j a):=by
 apply domain_mono Y H G _ (trek_region Y H G i x f h); rintro _ ⟨v,h,rfl⟩; change a≤ v j+ eject i (x:ℝ) j; simpa [e] using (show a≤v j from h)
lemma trek_vac (J:Calibration)(x:δ)(a:Axis): trek J a x 1=1 := by
 refine Filter.Germ.coe_eq.mpr ?_; exact Eventually.of_forall fun s:ℕ=> map_one (cruise a J (pitchBeat x s))
noncomputable def plusLaw (a:Axis)(x:δ) : (D false Set.univ) →ₗ[ℂ] (D false Set.univ) where
 toFun f:=⟨trek K a x f.val,free_play Y H G x a _ f.property⟩
 map_add' f g:= Subtype.ext (map_add (trek K a x) f.val g.val)
 map_smul' k f:= Subtype.ext (map_smul (trek K a x) k f.val)
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
