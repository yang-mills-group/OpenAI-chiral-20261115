import YM.CF.Fixed.RiftGauge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Flight differs macroscopically. Ratio with the vacuum removal tested here
is uniform relative matching of the `heat->line` ingredients on the reflection
pairs (inside Cap). Not the integrated Schwinger data! See RTC. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll SU Bulk
open Reed.Bare Cube
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {N:Side}{u v:ℕ}{x z y:ℝ}{p:Side}

def tollHelps(N:Side):ℝ:= chip/32*N.val
def area_t (N:Side) : ℕ := Nat.floor (tollHelps N)
def small_band (N:Side) := Finset.univ.filter (fun i:Ion N=> i.2=Reed.Bare.ply 0 ∧ ∀ j,|zmom i.1 j|≤chip)
lemma mass_are : area_t N ≤ N.val :=by
  unfold area_t; apply Nat.le_of_lt; apply (Nat.floor_lt (show 0≤ tollHelps N from mul_nonneg (div_nonneg chip_p.le (by norm_num)) (Nat.cast_nonneg _))).mpr
  unfold tollHelps; have hx : 0<(N.val:ℝ):=by exact_mod_cast N.property
  nlinarith [chip_u]
lemma count_works : area_t N ^ 3 ≤ (small_band N).card:=by
  let m:=area_t N; let f(v:Fin 3→ Fin m):Ion N:=(fun i=>↑(v i).val, ply 0)
  have he(v:Fin 3→Fin m)(i): (f v|>.1 i).val=(v i).val:= ZMod.val_natCast_of_lt ((v i).isLt.trans_le mass_are)
  have hf: Injective f:= by intro i j p; funext v; apply Fin.ext; rw [←he i v, p, he]
  rw [← show Fintype.card (Fin 3→Fin m)=_ from (by simp [m] : Fintype.card (Fin 3→Fin m)=area_t N^3), ←Finset.card_univ, ←Finset.card_image_of_injective Finset.univ hf]; refine Finset.card_le_card ?_
  intro x p; obtain ⟨v,-,rfl⟩:=Finset.mem_image.mp p; apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,rfl,fun j=>?_⟩
  let a :Per N:= (f v|>.1 j); have hw:= winding_bounds a; let L:ℝ:= (v j).val; have hn: (N.val:ℝ)>0:=by exact_mod_cast N.property
  have hp: ((v j).val:ℝ)+1≤tollHelps N:= by refine le_trans (show _ ≤ (m:ℝ) by exact_mod_cast (v j).isLt) (Nat.floor_le ?_); exact mul_nonneg (div_nonneg chip_p.le (by norm_num)) (Nat.cast_nonneg _)
  have ht:winding a≤ chip:=by
    have hy : (2*L+1)/N.val≤chip/16:=by apply (div_le_iff₀ hn).mpr; unfold tollHelps at hp; unfold L; linarith -- nlinarith
    unfold winding; rw [show a.val=_ from he v j]; exact le_trans (mul_le_mul_of_nonneg_right hy Real.pi_pos.le) (le_trans (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (div_nonneg chip_p.le (by norm_num))) (by linarith [chip_p]))
  change |Lat.principal a|≤_; rw [Lat.principal, if_pos (by linarith only [le_trans ht chip_u,Real.pi_gt_three]), abs_of_pos hw.1]; exact ht

-- use budget on a specific 2-point system. all K exposures can be any depth.
def harrow (N:Side) (x y:ℝ): Op (Model N):= (frame matter (Cube.links (airy N x y)) (anticut N)).H
def hearth (N:Side)(z:ℝ):ℝ:= (area_t N:ℝ)^3 * (z^2/16)
lemma harry (h:N.val=2*p.val)(w:1<p.val)(x:ℝ)(v:0<x)(u:x≤chip) (S0:Safe (harrow N 0 0))(S1:Safe (harrow N 0 x))(S2:Safe (harrow N x 0))(S3:Safe (harrow N x x)) : hearth N x ≤ energy (harrow N x x)+energy (harrow N 0 0)-energy (harrow N 0 x)-energy (harrow N x 0):=by
  have hp: 2<N.val:= by omega
  let F(a b:ℝ)(i:Ion N):=timed (freqZ (θ_issue N a b) i); have hx(s t:ℝ)(u:Safe (harrow N s t)): (∀ i,Safe (F s t i)) ∧ energy (harrow N s t)=∑ i,energy (F s t i):= energy_arrange _ _ (blank N s t hp) u
  obtain ⟨l1,p1⟩:=hx 0 x S1; obtain ⟨l2,p2⟩:=hx x 0 S2; obtain ⟨l0,p0⟩:=hx 0 0 S0; obtain ⟨l3,p3⟩:=hx x x S3; rw [p3,p0,p1,p2, ←sum_add_distrib,←sum_sub_distrib,←sum_sub_distrib]
  let g(i:Ion N):=energy (F x x i)+energy (F 0 0 i)-energy (F 0 x i) -energy (F x 0 i)
  have he(i:Ion N) : 0≤g i ∧ (i∈small_band N → x^2 /16 ≤ g i):=by
    specialize l0 i; specialize l1 i; specialize l2 i; specialize l3 i; unfold g F at *; simp_rw [freq_spread] at *
    refine ⟨sustain h w (phase_b 0 _) (phase_b x _) _ l1 l0 l2 l3|>.trans_eq (show _ = _ by abel),?_⟩; intro p; obtain ⟨t,Q⟩:= (mem_filter.mp p).2; rw [t] at l0 l1 l2 l3 ⊢; simp_rw [phase_ok] at *; exact (warmer (zmom i.1) _ hp ((Real.norm_of_nonneg v.le)|>.trans_le u) Q v l0 l2 l1 l3).trans_eq (by ring)
  unfold hearth; refine le_trans (b:= ((small_band N).card:ℝ)*(x^2/16)) ?_ ?_ -- tune usehe
  · have ht : ((area_t N:ℝ)^3) ≤ (small_band N).card:=by exact_mod_cast (count_works (N:=N))
    exact mul_le_mul_of_nonneg_right ht (by positivity)
  have hs: (∑ i∈ small_band N, x^2/16)= ((small_band N).card:ℝ)*(x^2/16):= by simp
  rw [← hs]; exact le_trans (Finset.sum_le_sum (g:=g) (fun i p=> (he i).2 p)) (sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _=> (he i).1)
lemma min_area (p:2 ≤ tollHelps N) : (tollHelps N)/2 ≤ (area_t N:ℝ) :=by have hx:=Nat.lt_floor_add_one (tollHelps N); unfold area_t; linarith

abbrev qSide (x:ℝ): Fin 2→ℝ:= ![0,x]
/-- property for reflected kernel positivity at fixed plane data. -/
structure SymmetricPair (W: Fin 2→Fin 2→ Bkg (More N)) : Prop where
  mirror (i j:Fin 2): reflConfig N 0 (W i j)=W j i
  one_leg (i j k:Fin 2): Agrees (RP.north N 0) (W i j) (W i k)
lemma team_stamp (h:2<N.val):
    let W(i j:Fin 2):= airy N (qSide x i) (qSide x j); SymmetricPair W:=by -- define below
    intro W; exact ⟨fun i j=> airy_p _ _ h, fun i j k=> share_north _ _ h _⟩

lemma diag_price (A: Matrix (Fin 2) (Fin 2) ℂ)(p:A.PosSemidef): ‖A 0 1‖ * ‖A 1 0‖ ≤ ‖A 0 0‖*‖A 1 1‖:=by
  let a:= A 0 0; let b:=A 1 1; let u:=A 1 0; have hx: 0≤a:= p.diag_nonneg; have ht:0≤b:=p.diag_nonneg; have he:=p.det_nonneg; have hu:A 0 1=star u:= (show star u=A 0 1 from Matrix.ext_iff.mpr p.1 (0:Fin 2) 1).symm; rw [Matrix.det_fin_two,hu, sub_nonneg] at he
  have h : 0 ≤ star u * u := star_mul_self_nonneg _; rw [hu, ←norm_mul,← norm_mul]; have hp(x y:ℂ) (hx:0≤x)(h:x≤y): ‖x‖≤ ‖y‖:=by
    have he:= h; nth_rw 1 [←RCLike.norm_of_nonneg' hx, ← RCLike.norm_of_nonneg' (hx.trans h)] at he; exact_mod_cast (he : (↑‖x‖:ℂ) ≤ ↑‖y‖)
  exact hp _ _ h he
end YM.CF.Fixed.Rift
