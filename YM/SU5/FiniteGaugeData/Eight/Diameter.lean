import YM.SU5.FiniteGaugeData.Eight.Train
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
variable {K:Calibration}{m n:Side} {d p r:ℕ}{a i:Axis}{S T:Finset Cover}{D k:Axis→ℕ}{b:ℤ}
local notation "N"=> K.c m
private lemma funnel (i:Axis)(k:ℕ){d:ℕ}(h:2^k*(d+addgap K) ≤ (N).val){S:Support (More N)}(w:rest K m S i d)(f:Mark (K.c m)) : ∃ T:Support (More N),∃ y:Mark (K.c m), Mirror K.B K.ℓ (K.c m) S f T y (2^k) ∧ ∀ j:Axis,j≠i→ ∀ d,rest K m S j d→ rest K m T j d:=by
 induction k generalizing d S f with
 | zero=> exact ⟨_,_,by simpa using Mirror.self (B:=K.B) (f:=f) (S:=S) (u:=K.ℓ),fun _ _ _ h=>h⟩
 | succ k ih=>
    obtain ⟨z,u,v,e⟩:= twice i w ((Nat.le_mul_of_pos_left _ (pow_pos two_pos _)).trans h)
    obtain ⟨A,B,q,t⟩:= ih (d:=2*d+addgap K) (by rw [pow_succ] at h; exact h.trans' (le_of_eq (by ring))) v (reflMark i (Heat.gaugeShift K.B z) f * f)
    exact ⟨_,_, pow_succ' 2 k ▸ Mirror.trans (Mirror.grow _ z u) q, fun j p d h=> t j p d (e j p d h)⟩
lemma plans (k:Axis→ℕ){d:Axis→ℕ}(G:Finset Axis)(h:∀ i:Axis,i∈ G→ 2^(k i)*(d i+addgap K)≤(N).val){S:Support (More N)}(w:∀ i∈G,rest K m S i (d i))(f:Mark (K.c m)) : ∃ T y, Mirror K.B K.ℓ (K.c m) S f T y (∏ i∈G,2^(k i)):=by
 have hf {S':Support (More N)}(F:Finset Axis)(e:F⊆G)(w:∀ i∈ F, rest K m S' i (d i))(f:Mark (K.c m)): ∃ T y, Mirror K.B K.ℓ (K.c m) S' f T y (∏ i∈F,2^(k i)):=by
    induction F using Finset.induction_on generalizing S' f with
    | empty=> simp only [prod_empty]; exact ⟨_,_,Mirror.self⟩
    | @insert i R v ih=> obtain ⟨T,y,p,q⟩:=funnel i (k i) (h i (e (mem_insert_self ..))) (w i (mem_insert_self ..)) f; obtain ⟨U,z,u⟩:=ih (Subset.trans (subset_insert ..) e) (fun j hj=> q j (fun x=>v (x ▸ hj)) (d j) (w j (mem_insert_of_mem hj))) y; rw [prod_insert v]; exact ⟨U,z,p.trans u⟩
 exact hf G (Subset.refl _) w f
private lemma densL {x y:ℕ}(h:0<y)(p:y≤x):∃ k:ℕ,2^k*y≤x∧x ≤ 2* (2^k)*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ h)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e:Nat.find ht=k
  cases k with
  | zero=> simpa using p
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
abbrev film (p:ℤ)(d:ℕ)(S:Finset Cover)(i:Axis): Prop:=∀ x∈ S,p ≤ x i ∧ x i≤ p+d
lemma film_rest (F:film b d S i):rest K m (region S N) i d:=by
 refine ⟨b,fun z v=>?_⟩; obtain ⟨j,q,rfl⟩:=mem_image.mp v; exact ⟨_, (F j q).1,(F j q).2,(wrap_here ..).symm⟩
lemma film.tick (f:film b d S i)(v:a≠i)(z:ℤ): film b d (hour K S a z) i:= by intro x w; obtain ⟨x,p,rfl⟩:= mem_image.mp w; have he:= beat_slant K i a z x v; change b≤ beat K a z x i∧ beat K a z x i≤ _; rw [he]; exact f x p
lemma film.ref (f:film b d S i)(v:a≠ i)(z:ℤ): film b d (refract a z S) i:=by intro x v'; obtain ⟨x,p,rfl⟩:=mem_image.mp v'; rw [fling_move, if_neg v]; exact f x p
lemma film.glue (f:film b d S i)(g:film b d T i): film b d (S∪T) i:= fun x t=> (mem_union.mp t).elim (f x) (g x)
lemma film.go (p:film b r S i)(t:a≠ i)(n:ℕ):film b r (proceed_set K a d S n) i:= by
 induction n with
 | zero=> intro i hi; rw [proceed_set] at hi; simp at hi
 | succ n ih=> exact (p.glue (p.ref t _)).glue (ih.tick t _)
lemma film.terrace (p:film b r S i)(t:a≠ i)(n:ℕ):film b r (SalonG.terrace (K:=K) a d n S) i:= by
 have he:= film.go (K:=K) (d:=d) p t n; have hv:= (he.ref t 0).glue he; exact hv.glue (hv.ref t _)
-- compression geometry: Body =4 H (cuts over time real phase size). Trans width exteriors already inside S. volume. Budget unchanged WP4 even!
private lemma volumeB (t:yard K d≤2*(D a+addgap K)) (x:∀ j∈ univ.erase a, (K.c m).val≤2*2^(k j)*(D j+addgap K))(q:0<p)(f:PaidSpan K m d p): sites (K.c m)≤ ↑(4*p*(∏ j∈univ.erase a,2^(k j):ℕ))*capR K D:=by
 let Q:= (More N).val; let l(a:Axis):=(D a+addgap K); let M(a:Axis):=4*l a; let J(a):=2^(k a); let F:= univ.erase a
 have he:= f.upper; have hκ: (yard K d) ≤ yard K d*p:= Nat.le_mul_of_pos_right _ q; have hu: Q ≤ 4*p*M a:= by
    apply le_trans (Nat.mul_le_mul_right 2 he); unfold proceed M l at *; nlinarith -- ≥ 16*p.C normal sum lower≥? N≤2HG+2G ≤4HG, Q≤ 8HG ≤16H.D yes margin equal.
 have hh(i:Axis)(v:i∈ univ.erase a): Q ≤ J i*M i:=by apply le_trans (Nat.mul_le_mul_right 2 (x i v)); exact le_of_eq (by unfold J M l; ring)
 have hv:= prod_le_prod (s:=F) (f:=fun _=>Q) (fun i _=> Nat.zero_le _) hh
 have hz:insert a F= univ:= Finset.insert_erase (mem_univ _); have hp:F.card+1=4:=by rw [← card_insert_of_notMem (show a ∉F from fun d=>by simp [F] at d),hz]; exact card_fin _
 let B:= 4*p*(∏ i∈F,J i)
 have hw:Q^4 ≤ B* ∏ i:Axis,M i:=by rw [←hz, prod_insert (show a∉ F from fun d=>by simp [F] at d)]; rw [← hp,pow_succ',← prod_const Q]; apply (Nat.mul_le_mul hu hv).trans; rw [prod_mul_distrib]; exact le_of_eq (by unfold B; ring) -- prod_const args tune `←hz` rewrites F body? let F.
 change (Q:ℝ)^4 ≤ (B:ℝ)* ↑(∏ i:Axis,M i); exact_mod_cast hw
lemma Mansion {T:Finset Cover}(h:n=K.c m)(q:0<p)(f:PaidSpan K m d p)(t:yard K d≤2*(D a+addgap K))(u:∀ i∈ univ.erase a,D i+addgap K ≤ (K.c m).val) (v:∀ i:Axis,i≠a→∃ b:ℤ,film b (D i) T i): ∃ x:ℕ,0<x∧sites n ≤ (↑(4*p*x:ℕ):ℝ)* capR K D ∧ ∀ f:Mark n, ∃ V F,Mirror K.B K.ℓ n (region (terrace a d p T (K:=K)) n) f V F x:=by
 subst n; have he:∀ i:Axis, ∃ k:ℕ,i∈univ.erase a → 2^k*(D i+addgap K) ≤ (N).val∧ (N).val ≤ 2*2^k*(D i+addgap K):= fun i=> by 
    by_cases h:i∈univ.erase a; · obtain ⟨b,g⟩:= densL (lt_of_lt_of_le addgap_pos (Nat.le_add_left ..)) (u i h); exact ⟨b,fun _=>g⟩
    exact ⟨0,fun a=>(h a).elim⟩
 choose k hk using he; refine ⟨_, Finset.prod_pos (s:=univ.erase a) (f:=fun i:Axis=>(2:ℕ)^(k i)) (by intros; positivity), volumeB t (fun i h=>(hk i h).2) q f, fun f=>plans k _ (fun i h=> (hk i h).1) (fun i h=> film_rest (film.terrace (d:=d) ((v i (mem_erase.mp h).1).choose_spec) (mem_erase.mp h).1.symm p)) f⟩
-- a-d shift arrangement choose two aligned endpoints. 
lemma duty (p:film b d S a): ∃ z:ℤ,∃ v:ℕ,0<v∧ Studio a 0 (yard K v) K.ℓ (hour K S a z) ∧ yard K v ≤ 2*(d+addgap K):=by
 let q:ℤ:=tic K; have he:0<q:=Nat.cast_pos.mpr (tic_pos K)
 let z:= ( (K.ℓ:ℤ)-b)/q+1; let u:= b+q*z; have hx:u≥ K.ℓ∧ u≤ (K.ℓ:ℤ)+q:=by
    unfold u z; have hv:=Int.emod_nonneg ((K.ℓ:ℤ)-b) he.ne'; have hu:=Int.emod_lt_of_pos ((K.ℓ:ℤ)-b) he; have h':= Int.emod_add_mul_ediv ((K.ℓ:ℤ)-b) q; rw [mul_add,mul_one]; omega
 let v:= (u+d+K.ℓ)/q+1; have hv:0 < v:=by unfold v; apply Int.add_pos_of_nonneg_of_pos (Int.ediv_nonneg (by omega) he.le) (by omega) -- lemma?
 have h0: ↑(yard K v.toNat)=q*v:=by rw [←yard_le,Int.toNat_of_nonneg hv.le] -- infer Int?
 let F:= q*v; have h':u+d+ K.ℓ ≤ F∧ F ≤ u+d+ K.ℓ+q:=by
    unfold F v; have hv:= Int.emod_nonneg (u+d+K.ℓ) he.ne'; have hu:=Int.emod_lt_of_pos (u+d+K.ℓ) he; have hf:=Int.emod_add_mul_ediv (u+d+K.ℓ) q; rw [mul_add,mul_one]; omega
 have hz{i}(h:i∈ hour K S a z): u ≤ i a∧ i a ≤ u+d:=by obtain ⟨x,v,rfl⟩:=mem_image.mp h; change u ≤ beat K a z x a∧ beat K a z x a≤ u+d; unfold u; rw [beat_same]; have he:= p x v; unfold q; omega
 refine ⟨z,v.toNat,(by omega),⟨fun y v=> ?_,fun y v=> ?_⟩,?_⟩
 · have he:= hz v; unfold F at h'; omega
 · have he:= hz v; omega
 have hk: K.ℓ*2 + tic K= addgap K:=by unfold tic addgap stepgap; omega
 unfold F q at *; omega
#print axioms duty
#print axioms Mansion
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
