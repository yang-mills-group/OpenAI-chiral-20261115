import YM.SU5.FiniteGaugeData.Concord.Sightline
import YM.SU5.FiniteGaugeData.Concord.Scene
import YM.CF.Buffered.Application
/-! # Fixed spacing on our Traced data. Selected banner read and reduction.

Use SAME `Bilinear.word` (non-wrapping segment away from aligned plane).
For this course K.ℓ= reserve Λ l, and `K.vertex` is from Journeys, positive and large (not an
additional tolerance proof). Wording any FIXED s so can submit bounds for which it is expected;
resolution s spacing L^{-s} level0 gauge units, plane always at z=K.plane0 in the s units,
in particular for s=0 submit to full common halo. This native-plane reservation can be considered
first at one resolution using `diagonals`, not all-resolution invariance under translation.
The strict inequalities are outstanding; we track this same Y state. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct ComplexConjugate
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
namespace Banner
open Bilinear
section native
variable (K : Calibration)
local notation "S'=>" => Bilinear.support K -- token fix
local notation "T'"=> nodeC creatorSite
local notation "v'"=>K.plane0
local notation "Θ'"=> turn K 3 K.plane0
private lemma front : nodeC creatorSite∈ Bilinear.support K := by cases t : segment K <;> simp [Bilinear.support,t,visits]
private lemma farthest : nodeC (removerSite K) ∈ Bilinear.support K := by
 rw [←end_node,Bilinear.support,List.mem_toFinset]; apply show ∀ s : Cover, ∀ l:Walk, stop s l∈visits s l from ?_
 intro s l; induction l generalizing s <;> simp_all [stop,visits]

-- variant of the private support lemmas in Word
lemma situated : starboard 3 K.plane0 K.ℓ (Bilinear.support K) ∧
    ∃ m:Cover,m=nodeC (removerSite K) ∧ m∈Bilinear.support K ∧ nodeC creatorSite ∈ Bilinear.support K ∧ m=nodeC creatorSite+(2*K.vertex) • step 3:=by
 refine ⟨fun i p=>?_,_,rfl,farthest K,front K,(end_node K).symm.trans (Sods.swifts ..)⟩
 obtain ⟨x,_,rfl⟩:= Cube.range_leg _ (posDir 3) (2*K.vertex) _ (List.mem_toFinset.mp p)
 have he:2*K.ℓ≤4*K.B.val*(K.vertex/(2*K.B.val)):=K.line
 have hv: K.plane0 = -(↑(4*K.B.val*(K.vertex/(2*K.B.val))):ℤ) := by unfold Calibration.plane0 Calibration.ζ gaugeShift; push_cast; ring
 apply le_trans (b:=0) (by omega); simp [nodeC,creatorSite]; omega

lemma heart_paid : InTest K true (Bilinear.support K) false (word K) := by
 refine .smul _ (InTest.sum _ _ fun p _=> InTest.sum _ _ fun q _ =>.mul (.seed (Coeff.fromC _ _ ?_ ?_)) (.mul (.remover q (by decide) (farthest K)) (.creator p (by decide) (front K))))
 · exact (matter_cont.comp (Wilson.continuous_travel _ _)).matrix_elem p q
 intro X Y h; unfold D5; exact congrArg (fun t:SU.E=> (matter t).val p q) (travel_local _ _ X Y (fun e u v=> h e (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v)))

def bulb : junior K:=⟨word K, (allowed K true).forget⟩
lemma bulb_b : bulb K∈ club K (Bilinear.support K):= heart_paid K
lemma bulb_color : bulb K ∈ singlets K:= show Gaugeable (bulb K) from word_covariant K
lemma bulb_place: bulb K∈ wing K 3 K.plane0 K.ℓ:= (suitableWing ..).2 ⟨_,bulb_b K,(situated K).1⟩

def center (x:ℂ): junior K := bulb K-x • 1
def centered_echo (x y:ℂ):junior K:= turn K 3 K.plane0 (center K x)*center K y
def zone (K:Calibration):= shadow (3:Axis) K.plane0 (Bilinear.support K) ∪ Bilinear.support K

lemma center_zero : center K 0=bulb K:=by rw [center,zero_smul,sub_zero]
lemma center_color (x:ℂ): center K x∈singlets K:= (singlets _).sub_mem (bulb_color K) ((singlets _).smul_mem (singlets _).one_mem x)
lemma center_house (x:ℂ): center K x∈club K (Bilinear.support K):= (club _ _).sub_mem (bulb_b K) ((club _ _).smul_mem (club _ _).one_mem x)
lemma center_heart (x:ℂ): center K x∈ club K (zone K):= lodge K _ subset_union_right (center_house ..)
lemma center_admit (x:ℂ): center K x∈ wing K 3 K.plane0 K.ℓ := (wing _ _ _ _).sub_mem (bulb_place K) ((wing _ _ _ _).smul_mem (wing _ _ _ _).one_mem x)
lemma center_ref (x:ℂ): turn K 3 K.plane0 (center K x)∈club K (zone K):= lodge K _ subset_union_left (turn_support _ _ (center_house ..))
lemma echo_house (x y:ℂ): centered_echo K x y∈club K (zone K):= (club _ _).mul_mem (center_ref ..) (center_heart ..)
lemma echo_color (x y:ℂ): centered_echo K x y∈singlets K:= (singlets _).mul_mem (turn_gauge _ _ (center_color K x)) (center_color K y)

-- concrete norm pledge
lemma meter_D5 (p q:SU.Slot)(V:LinksC): ‖D5 K p q V‖ ≤ 1:=by unfold D5; exact (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (matter _).property).le
lemma heart_norm (m:Side)(v:Fields (K.c m)): ‖word K m v‖ ≤ 5*(K.vertex:ℝ)^3 := by
 let V(p q:SU.Slot) := Buffered.scalar K ((D5 K p q) ∘ Prod.fst)* (removal K (removerSite K) 2 q*creation K creatorSite 0 p)
 let C:ℂ:= (K.vertex:ℂ)^3/5
 have ht : ‖C‖= (K.vertex:ℝ)^3/5:= by unfold C; rw [norm_div,norm_pow,Complex.norm_natCast]; norm_num
 have hf: (↑five.card:ℝ)=5:=by have he:five.card=5:=(colors_card _).trans rfl; norm_num [he]
 have he(p q): ‖V p q m v‖ ≤ 1:=by
   let F:PairsC→ℂ:=((D5 K p q) ∘ Prod.fst)
   let x:Blot:= (creatorSite,0,p); let y:Blot:= (removerSite K,2,q)
   have hp: removal K (removerSite K) 2 q = chord K y:= (if_neg (by decide: (2:SpinIdx) ∉ plusHalf)).symm -- IF expansion?
   have hq: creation K creatorSite 0 p=chord K x:= (if_pos (by decide : (0:SpinIdx) ∈ plusHalf)).symm
   unfold V; rw [hp,hq]; change ‖(F _ • (1:FC _) * (chord K y m v*chord K x m v))‖ ≤ 1
   rw [Algebra.smul_mul_assoc,one_mul,norm_smul]; apply mul_le_one₀ (meter_D5 ..) (norm_nonneg _); exact (norm_mul_le ..).trans (mul_le_one₀ (moderate ..) (norm_nonneg _) (moderate ..))
 change ‖-C • ((∑ p∈ five, ∑ q∈ five, V p q) m v)‖ ≤ _
 simp_rw [norm_smul,norm_neg,Finset.sum_apply]; refine le_trans (mul_le_mul_of_nonneg_left (le_trans (norm_sum_le ..) (sum_le_sum (fun (p:SU.Slot) _ => (norm_sum_le ..).trans (sum_le_sum (fun q _=> he p q))))) (norm_nonneg C)) ?_
 simp_rw [sum_const,nsmul_eq_mul,hf, ht]; exact le_of_eq (by ring)

abbrev voice (K:Calibration)(x:ℂ) := 5*(K.vertex:ℝ)^3 + ‖x‖
lemma voice_pos (x:ℂ) : 0 ≤ voice K x := by unfold voice; positivity
lemma beacon (x:ℂ)(m:Side)(v:Fields (K.c m)): ‖(center K x).val m v‖ ≤ voice K x:=by
 change ‖word _ _ v-x • (1:FC _)‖ ≤ _; exact (norm_sub_le ..).trans (add_le_add (heart_norm ..) (by rw [norm_smul,norm_one,mul_one]))
lemma beacon_echo (x y:ℂ)(m:Side)(v:Fields (K.c m)): ‖(centered_echo K x y).val m v‖ ≤ voice K x * voice K y:=
 (norm_mul_le (blade 3 K.plane0 (center K x).val m v) _).trans (mul_le_mul (blade_bound 3 _ m (fun _=> beacon ..) _) (beacon K y m v) (norm_nonneg _) (voice_pos ..)) -- definition semilinear

-- actual terminal distance in torus units (eventually), native s. Reflected plane specified atop.
lemma leg (m:Side)(p:2*(2*K.vertex) ≤ (More m).val) :
    separation (wrap (More m) (nodeC creatorSite)) (wrap (More m) (nodeC (removerSite K)))= 2*K.vertex:=by
 let v:=2*K.vertex; let T:Cover:=v • step 3
 have he: lift (wrap (More m) T)=T := by
   apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; have h:= m.property; change _ ≤ m.val*2 at p
   unfold T; by_cases k:i=3 <;> simp [k]
   · -- split
     unfold v; have hp:= K.positiveR; omega

 rw [separation_comm,separation,←map_sub]; obtain ⟨s,rfl,_,_,t⟩:= (situated K).2 -- rfl direction cleanup
 rw [t,add_sub_cancel_left]
 have h:= component_le (wrap (More m) T) 3; rw [he] at h; simp [T] at h -- expands RHS??
 refine le_antisymm (Finset.sup_le (fun i w=>?_)) h
 change (lift (wrap (More m) T) i).natAbs≤_; rw [he]; by_cases k:i=3 <;> simp [T,v,k]<;> omega
end native
end Banner
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.Banner.leg
#print axioms YM.CF.Buffered.Concord.Banner.heart_norm
