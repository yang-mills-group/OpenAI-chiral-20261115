import YM.CF.Buffered.Eligible

/-!
# Eligibility on fixed support -> eventually fits with the SAME margin
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable (K : Calibration) {m : Side}
lemma csize : (K.c m).val = m.val*2*K.B.val := by simp only [Calibration.c, cell,mesh,pow_zero,mul_one]; rfl
lemma side_lower : m.val ≤ (K.c m).val := by rw [csize]; exact (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ K.B.property)
lemma opposite_multiple (u : K.takes m) (j : ℕ) : ∃ b:ℕ, (cell m K.B K.R.L j).val = 4*K.B.val*b := by
 obtain ⟨x,h⟩:= K.even u; refine ⟨x*(K.R.L^j).val,?_⟩; change m.val*(K.R.L^j).val*2*K.B.val= _; rw [h]; ring
lemma past_period (r : ℕ) : ∀ᶠ m:Side in atTop, r < m.val := by
 let p:Side:=⟨r+1,by positivity⟩; filter_upwards [eventually_ge_atTop p] with m w; exact w
lemma c_grows : Tendsto (fun m:Side => (K.c m).val) atTop atTop := tendsto_atTop.2 fun i=> (past_period i).mono fun _ h=> h.le.trans (side_lower K)
-- finite-period margin condition using lifted coordinates (also prevents coincidence across seams).
-- can pay arbitrary larger transverse sizes in the limit too.
def allocated (m:Side) (S : Finset Cover) := ∀ x∈ S, x 3 + K.ℓ ≤ K.plane0 + (K.c m).val
lemma allocates (S : Finset Cover) : ∀ᶠ m:Side in atTop, allocated K m S := by
 classical
 unfold allocated; rw [S.eventually_all]; intro x h
 let a:= x 3 + K.ℓ - K.plane0; filter_upwards [(c_grows K).eventually (eventually_ge_atTop a.toNat)] with m w; change _ ≤ (K.c m).val at w; unfold a at w; omega
lemma band_of_size (m : Side) (S : Finset Cover) (p : allocated K m S) (v : goodSet K S) :
    S.image (wrap (More (K.c m))) ⊆ K.fits m := by
 intro x hx; obtain ⟨x,h,rfl⟩:= mem_image.mp hx; apply (band_spec ..).mpr
 let i:= x 3 - K.plane0; let n:=K.c m; have hp:= p x h; have hu:= v x h; have hz:0<(K.c m).val:= (K.c m).property
 have hg:0 ≤ i:=by unfold i; omega
 have hw:i.toNat<(More n).val:=by change _<n.val*2; unfold n i at *; omega
 rw [show (wrap (More (K.c m)) x) 3 - (K.plane0 : Per (More n))=(i.toNat:Per (More n)) from ?_, ZMod.val_natCast_of_lt hw]; swap; · rw [←Int.cast_natCast, Int.toNat_of_nonneg hg,show (i:Per (More n))=(↑(x 3) : Per (More n)) - (K.plane0:Per (More n)) from Int.cast_sub ..]; rfl
 unfold i; omega
lemma fits_eventually (S : Finset Cover) (p : goodSet K S) : ∀ᶠ m in atTop, S.image (wrap (More (K.c m))) ⊆ K.fits m := (allocates K S).mono fun x h=> band_of_size K x S h p
lemma Eligible.fits_time {K : Calibration} {f : Family K} {wide : Bool} (a : Eligible K wide f) : ∀ᶠ m in atTop, AtSupport false (K.fits m) (f m) := by
 obtain ⟨s,t,p⟩:= a.support; exact (fits_eventually K s p).mono fun m h=> (t.support m).mono h
-- Can require true embedding on these same tests (and their fixed qualified
-- margined boxes including the two measured words in square, apply this with any such finite pad).
lemma separates (S : Finset Cover) : ∀ᶠ m in atTop, Set.InjOn (wrap (More (K.c m))) (↑S : Set Cover) := by
 classical
 have he : ∀ᶠ m:Side in atTop, ∀ x∈ S, ∀ i:Axis, -((More (K.c m)).val:ℤ) < 2*x i ∧ 2*x i ≤ (More (K.c m)).val := by
   rw [S.eventually_all]; intro i v; rw [eventually_all]; intro j
   filter_upwards [(c_grows K).eventually (eventually_gt_atTop (i j).natAbs)] with m w; change _ < (K.c m).val at w; rw [show (More (K.c m)).val=(K.c m).val*2 from rfl]; omega
 filter_upwards [he] with m w; exact (wrap_injOn (More (K.c m))).mono (fun _ u=> w _ u)
end YM.CF.Buffered
