import YM.SU5.FiniteGaugeData.Chrono.Turnkin
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Nacre Charm
namespace Chrono
set_option quotPrecheck false
variable (S: Finset Cover)(K:Calibration)(m:Side)(a:Axis)
-- denseLe.Geometry. On axis support somewhere within box width R. Enough. T=antipode phase = K.c m.val.
-- property Reserve >0 fixed, enforce h. 
abbrev wall := S.sup (fun x=>univ.sup fun i:Axis=> (x i).natAbs)
lemma wall_p {j:Cover}(p:j∈ S) : -((wall S):ℤ)≤ j a ∧ j a≤ (wall S):=by have he:= (le_sup (f:=fun i:Axis=> (j i).natAbs) (mem_univ a)).trans (le_sup (f:=fun y=>univ.sup fun i:Axis=> (y i).natAbs) p); unfold wall; omega
local notation "C"=> K.c m
local notation "Δ"=> dist
local notation "N"=> (K.c m).val
local notation "B"=> tic K
abbrev hours := (((K.c m).val-(wall S+K.ℓ))/tic K)
local notation "H"=> hours S K m
abbrev fareWidth := 2*wall S+tic K+K.ℓ
local notation "D"=> fareWidth S K
private lemma costs (p:wall S+K.ℓ ≤ N) : (wall S)+K.ℓ+(tic K)*hours S K m ≤ N ∧ N < (wall S)+K.ℓ + (tic K)+ (tic K)*hours S K m:=by
 have hz:=(Nat.div_add_mod ((K.c m).val-(wall S+K.ℓ)) (tic K)); have ht:= Nat.mod_lt ((K.c m).val-(wall S+K.ℓ)) (tic_pos K); unfold hours; omega
variable {S m}
private lemma fare {x:Cover} (t:x∈hour K S a (hours S K m))(p:wall S+K.ℓ≤N): (N:ℤ) -fareWidth S K ≤ x a∧ x a ≤ N - (K.ℓ:ℤ) :=by
 obtain ⟨x,tz,rfl⟩:=mem_image.mp t; change _ ≤ beat K a (H:ℤ) x a ∧ beat K a (H:ℤ) x a ≤ _; have w:= wall_p S a tz; have c:=costs S K m p;
 rw [beat_same,← Nat.cast_mul]; unfold fareWidth; omega
variable (S m)
lemma cost_tic (p:wall S+K.ℓ≤N) (i:Axis) : rest K m (region (refract a 0 (hour K S a (hours S K m)) ∪ (hour K S a H)) C) i (2*fareWidth S K) := by
 by_cases e:i=a
 · subst i; refine ⟨(N:ℤ)- (D:ℤ),fun x t=> ?_⟩; obtain ⟨y,u,rfl⟩:=mem_image.mp t; rcases mem_union.mp u with w|w
   · obtain ⟨y,v,rfl⟩:= mem_image.mp w; obtain ⟨w',h'⟩:= fare K a v p
     let v:ℤ:= (plane a 0).motion y a; have he:v= -y a:= by unfold v; rw [fling_move,if_pos rfl]; simp
     refine ⟨v+(↑(More (K.c m)).val :ℤ), ?_,?_,?_⟩; rotate_left 2
     · simp only [wrap_here, Int.cast_add, Int.cast_natCast, show ↑(More (K.c m)).val=(0:Per (More (K.c m))) from ZMod.natCast_self _, add_zero] -- tune simp also removes part lhs
       rfl
     · rw [show (More C).val=N*2 from rfl]; omega
     · rw [show (More C).val=N*2 from rfl]; omega
   obtain ⟨u,v⟩:= fare K a w p; exact ⟨y a,u,by omega,rfl⟩
 -- others
 refine ⟨-(wall S:ℤ),fun x t=> ?_⟩; obtain ⟨y,u,rfl⟩:=mem_image.mp t;
 have he {x:Cover}(t:x∈hour K S a H): -((wall S):ℤ)≤ x i∧ x i≤ ↑(wall S):=by obtain ⟨y,tQ,rfl⟩:= mem_image.mp t; change _ ≤ beat K a H y i ∧ beat K a H y i ≤ _; rw [beat_slant K i a H y (Ne.symm e)]; exact wall_p S i tQ
 have h: -((wall S):ℤ)≤ y i∧ y i≤ ↑(wall S):= by
    rcases mem_union.mp u with w|w; · obtain ⟨z,h,rfl⟩:=mem_image.mp w; rw [fling_move,if_neg (Ne.symm e)]; exact he h
    exact he w
 exact ⟨y i, h.1, by unfold fareWidth; omega,rfl⟩
lemma hours_band (p:wall S+K.ℓ≤N){k:ℕ}(g:k≤hours S K m)(h:Ahead a 0 K.ℓ S) : region (hour K S a k) C ⊆ band C a 0 K.ℓ:=by
 intro x r; obtain ⟨y,u,rfl⟩:=mem_image.mp r; obtain ⟨y,v,rfl⟩:=mem_image.mp u; specialize h y v; have w:= wall_p S a v; have e:= (costs S K m p).1; have hv:= Nat.mul_le_mul_left (tic K) g;
 let t:= beat K a k y; have hl: (K.ℓ:ℤ) ≤ t a∧ t a+(K.ℓ:ℤ)≤ N:= by unfold t; rw [beat_same,← Nat.cast_mul]; omega
 apply (band_spec ..).mpr
 have he:0 ≤ t a:=by omega
 have h':(t a).toNat < (More (K.c m)).val:= by have hx:0<(N:ℤ):=Nat.cast_pos.mpr (K.c m).property; rw [show (More C).val=N*2 from rfl]; omega
 change _ ≤ ZMod.val ((wrap (More C) t) a - ((0:ℤ):Per (More C))) ∧ ZMod.val ((wrap (More C) t) a - ((0:ℤ):Per (More C)))+ _≤ _; rw [Int.cast_zero,sub_zero, wrap_here,show (↑(t a):Per (More C)) = ↑(t a).toNat from ?_, ZMod.val_natCast_of_lt h'] -- tune
 · omega
 rw [← Int.cast_natCast, Int.toNat_of_nonneg he]
lemma antipodes : ∀ᶠ m:Side in atTop,(wall S)+K.ℓ≤ (K.c m).val ∧ 2*(fareWidth S K)+addgap K≤ (K.c m).val:=by filter_upwards [(c_grows K).eventually_ge_atTop ((wall S)+K.ℓ), (c_grows K).eventually_ge_atTop (2*fareWidth S K+addgap K)] with m u v using ⟨u,v⟩
lemma hours_grow : Tendsto (hours S K) atTop atTop:= tendsto_atTop.2 fun r=> by
 filter_upwards [(c_grows K).eventually_ge_atTop ((wall S)+K.ℓ+r*tic K)] with m h
 exact (Nat.le_div_iff_mul_le (tic_pos K)).mpr (by change _≤ (K.c m).val at h; omega)
#print axioms cost_tic
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
