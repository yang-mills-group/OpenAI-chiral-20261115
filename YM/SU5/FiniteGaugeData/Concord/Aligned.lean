import YM.SU5.FiniteGaugeData.Concord.CoverGauge
/-!
# Aligned plane options for the generated FiniteGaugeData net

Impose positivity on concrete reflection (scaled integer plane & `theta` including Spin and
anti-wrap), AND support conventions (`wing`, margin in native units always includes the physical
buffer). Show positivity separately rather than assuming a payment of `Printed`; that exact
common-bare purchase was not used (and remains open here).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted
open Afterglow Afterglow.Sound Afterglow.Satin
open Reed (Fine)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
section basic
-- Eligible.lean counterpart for general axis
variable {K : Calibration} {wide : Bool} {S : Finset Cover} {f g : Family K} {b : Bool}
def blade (a:Axis)(s:ℤ)(f:Family K) : Family K:=fun m=> reflMark a s (f m)
variable (aξ : Axis) (s : ℤ)
local notation "X" => plane aξ s
local notation "Y" => blade (K:=K) aξ s
lemma blade_plus : Y (f+g)=Y f+Y g := funext fun _=> funext fun _=> theta_add ..
lemma blade_scale (a : ℂ) : Y (a • f)=star a • Y f := funext fun _=> funext fun _=> theta_smul ..
lemma blade_times : Y (f*g)=Y f*Y g := funext fun _=> funext fun _=> theta_mul ..
lemma blade_identity : Y 1=1 := funext fun _=> funext fun _=> theta_one _
private lemma opposite_spin : twist (pinLift aξ) (cutM plusHalf) = cutM plusHalfᶜ := by
 rw [dim_cut, raising,Fir.Adef.symm]; exact angleX (mirrorX aξ) true
private lemma reflected_scalar (f : PairsC→ℂ) (p : Coeff wide S f) : InTest K wide (S.image ((plane aξ s).motion)) false (Y (scalar K f)) := by
 let F := moveC aξ s; let g(x:PairsC):=star (f (F x.1,F x.2))
 have ht: Y (scalar K f)=scalar K g:= by funext m x; unfold scalar blade reflMark; rw [theta_smul,theta_one]; apply congrArg (fun u :ℂ=> u • 1); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
 rw [ht]; refine .seed ⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y a b=>?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ a) (moved_agree _ _ b))
private lemma reflected_creation_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (creation K x i b) = -Complex.I • ∑ j, star (Mir.pin aξ j i) • removal K ((plane aξ s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold blade reflMark creation removal
 rw [(flips_basisC aξ s (K.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma reflected_removal_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (removal K x i b) = Complex.I • ∑ j, Mir.pin aξ j i • creation K ((plane aξ s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold blade reflMark creation removal
 rw [(flips_basisC aξ s (K.c m) x i b).2]; simp only [map_sum,map_smul]
lemma bladeTest (p : InTest K wide S b f) : InTest K wide (S.image ((plane aξ s).motion)) b (Y f) := by
 induction p with
 | @creator x i b t v=>
   rw [reflected_creation_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∉ plusHalf
   · refine .smul _ (.remover b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   rw [show pin aξ j i=0 from Fine.entry (opposite_spin _) t (by simpa using not_not.mp w),star_zero,zero_smul]; exact .zero
 | @remover x i b t v=>
   rw [reflected_removal_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∈ plusHalf
   · refine .smul _ (.creator b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   have ht: twist (pinLift aξ) (cutM plusHalfᶜ)=cutM plusHalf:= by rw [dim_cut,map_sub,map_one,opposite_spin,dim_cut]; abel
   rw [show pin aξ j i=0 from Fine.entry ht (by simpa only [mem_compl] using t) w, zero_smul]; exact .zero
 | seed p=> exact reflected_scalar aξ s _ p
 | zero=> rw [show Y 0=0 from funext fun _=>funext fun _=> theta_zero _]; exact .zero
 | one=> rw [blade_identity]; exact .one
 | add _ _ a b=> rw [blade_plus]; exact .add a b
 | mul _ _ a b=> rw [blade_times]; exact .mul a b
 | smul a _ ih=> rw [blade_scale]; exact .smul _ ih
lemma descends (f:junior K) : blade aξ s f.val ∈ junior K := by
  obtain ⟨x,y⟩:= supported K f; exact also _ (bladeTest aξ s (show InTest K true x false f.val from y))

def turn (K:Calibration)(a:Axis)(s:ℤ) : junior K →ₗ⋆[ℂ] junior K where
  toFun f := ⟨blade a s f.val, descends a s f⟩
  map_add' := fun _ _=> Subtype.ext (blade_plus ..)
  map_smul' := fun _ _=> Subtype.ext (blade_scale ..)
lemma turn_coe (f:junior K) : (turn K aξ s f).val=blade aξ s f.val:=rfl
lemma turn_mul (f g:junior K) : turn K aξ s (f*g)=turn K aξ s f * turn K aξ s g:=Subtype.ext (blade_times ..)
lemma turn_one : turn K aξ s 1=1:=Subtype.ext (blade_identity ..)
lemma turn_twice : Function.Involutive (turn K aξ s):= by intro f; apply Subtype.ext; obtain ⟨T,v⟩:= (show TestFamily K true f.val from f.property).paid; exact funext fun m=> AtSupport.refl_refl aξ s (v.support m) -- order?

def shadow (aξ:Axis)(s:ℤ)(S:Finset Cover) := S.image (plane aξ s).motion

lemma turn_support {f:junior K}(t:f ∈ club K S): turn K aξ s f ∈club K (shadow aξ s S):= bladeTest aξ s (show InTest K true S false f.val from t)
lemma turn_gauge {f:junior K}(p:f∈singlets K): turn K aξ s f∈singlets K:=by intro m; obtain ⟨S,t⟩:= (show TestFamily K true f.val from f.property).paid; exact covariant_reflected (t.support m) ((show Gaugeable f from p) m) s aξ

private def turnL (K:Calibration)(a:Axis)(z:ℤ)(S:Finset Cover) : Palette S →ₗ⋆[ℂ] Palette (shadow a z S) := by
  let T:= shadow a z S; let f(x:Palette S):= polish K T (turn K a z (music K S x)) (turn_support a z (cleft ..))
  have he(x):music K T (f x)= _ := (show _=turn K a z (music K S x) from polish_eq ..)
  exact {toFun:=f
         map_add' := fun x y=> music_inj K T (by rw [he,map_add,map_add,map_add,he,he])
         map_smul' := fun t x=> music_inj K T (by rw [he,map_smul (music K S),map_smulₛₗ (f:=turn K a z),map_smul,he]) }

private lemma sheared (f:Palette S) : music K (shadow aξ s S) (turnL K aξ s S f)= turn K aξ s (music K S f):= polish_eq K _ _ (turn_support _ _ (cleft ..))
lemma blade_bound {f:Family K}(m:Side){c:ℝ}(p:∀ x,‖f m x‖≤c) (x:Fields (K.c m)):‖blade aξ s f m x‖≤c:=by unfold blade reflMark theta; rw [twist_norm,norm_cc]; exact p _

def mirrorL (K:Calibration)(aξ:Axis)(s:ℤ)(S:Finset Cover): Palette S→SL[starRingEnd ℂ] Palette (shadow aξ s S):= (turnL K aξ s S).mkContinuous (count S) (fun x=> by
  obtain ⟨m,h⟩:= (suitable (shadow aξ s S) K).exists; refine palette_norm (shadow aξ s S) K h (fun y=>?_); have he:= congrArg Subtype.val (sheared (K:=K) aξ s x); change pigment _ _ _ = blade aξ s (pigment S K x) at he; rw [native_formula,he]; exact blade_bound aξ s m (fun _=> pigment_bound ..) _)
lemma mirror_run (f:Palette S) : turn K aξ s (music K S f) = music K (shadow aξ s S) (mirrorL K aξ s S f):=(sheared ..).symm
end basic

-- buffered physical support per observable at its own contribution level
variable {Λ:Py.Rate.LocalLimit.Preparation}{l:ℕ}
open Afterglow.Journey

def starboard (a:Axis)(z:ℤ)(r:ℕ)(S:Finset Cover):Prop:= ∀ x∈S, z+r ≤ x a

section before
variable (K:Calibration)(a:Axis)(z:ℤ)(r:ℕ)
/-- Use lower margin only (opposite plane goes to infinity before this use). -/
lemma hosted {S:Finset Cover} (p:starboard a z r S): ∀ᶠ m:Side in atTop,region S (K.c m)⊆ band (K.c m) a z r:=by
  have he:∀ᶠ m:Side in atTop, ∀ x∈ S,x a + r ≤ z+(K.c m).val := by
    rw [S.eventually_all]; intro x w
    filter_upwards [(c_grows K).eventually_ge_atTop (x a + (r:ℤ)-z).toNat] with m w
    omega
  filter_upwards [he] with m t i v; obtain ⟨x,b,rfl⟩:= mem_image.mp v; apply (band_spec ..).mpr
  let n:=K.c m; let i:=x a-z; have hi:=t x b; have hv:=p x b; have hz:0<(K.c m).val:=(K.c m).property
  have hg:0 ≤ i:=by unfold i; omega
  have hw:i.toNat<(More n).val:=by change _<n.val*2; unfold n i at *; omega
  rw [show (wrap (More n) x) a-(z:Per (More n))=(i.toNat:Per (More n)) from ?_, ZMod.val_natCast_of_lt hw]; swap
  · rw [←Int.cast_natCast, Int.toNat_of_nonneg hg,show (i:Per (More n))= (↑(x a) : Per (More n))-(z:Per (More n)) from Int.cast_sub ..]; rfl
  unfold i; omega

def wing : Subalgebra ℂ (junior K) where
  carrier :={f|∃ S:Finset Cover, f∈club K S ∧ starboard a z r S}
  mul_mem' :=by
    rintro x y ⟨T,v,k⟩ ⟨S,h,w⟩; exact ⟨T∪S,Subalgebra.mul_mem _ (lodge K _ subset_union_left v) (lodge K _ subset_union_right h),fun i t=> (mem_union.mp t).elim (k i) (w i)⟩
  add_mem' :=by
    rintro x y ⟨T,v,k⟩ ⟨S,h,w⟩; exact ⟨T∪S,Subalgebra.add_mem _ (lodge K _ subset_union_left v) (lodge K _ subset_union_right h),fun i t=> (mem_union.mp t).elim (k i) (w i)⟩
  algebraMap_mem' c:=⟨∅,(club K ∅).algebraMap_mem c,fun i p=>False.elim (Finset.notMem_empty _ p)⟩
lemma suitableWing {f:junior K} : f∈ wing K a z r ↔ ∃ S:Finset Cover,f∈club K S∧starboard a z r S := Iff.rfl
lemma starboarded {S:Finset Cover} (p:starboard a z (Journey.reserve Λ l) S): starboard a ((Λ.R.L.val:ℤ)*z) (Journey.reserve Λ l) (swept Λ l S):=by
  rintro i t; obtain ⟨y,v,t⟩:= mem_biUnion.mp t; obtain ⟨x,w,rfl⟩:=mem_image.mp v; obtain ⟨y,h,rfl⟩:= mem_image.mp t
  let m:= Journey.reserve Λ l; let r:= seamWidth Λ l; let L:=(Λ.R.L.val:ℤ); change _≤y a + L*x a
  have ht : (m:ℤ)+r ≤ L*m := by unfold m r L seamWidth; exact_mod_cast margin_step (Journey.prepared Λ l) Λ.R.coarse
  have hv : - (r:ℤ) ≤ y a:= (box_test.mp h).1 a
  have hg : 0 ≤ L:= by unfold L; positivity
  have hp:= mul_le_mul_of_nonneg_left (p x w) hg; rw [mul_add] at hp; linarith -- implicit m
end before
end YM.CF.Buffered.Concord
