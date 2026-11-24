import YM.SU5.Reconstruction.Trap.Rebate
/-!
# Fitting against positive ray purchases
-/
set_option autoImplicit false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock
variable {H D K:Hilbert} {a b : Axis} (r:b≠a) (S:OS.Semigroup H a) (Q:OS.Semigroup D b) (C:Clasp K H D) (M : Mesh)
local notation "P₀"=> trans S
local notation "Q₀"=> trans Q
local notation "Γ"=> marks M
abbrev argSpace (S:OS.Semigroup H a)(r:b≠a)(d t:ℝ≥0):=S.U ((t:ℝ) • cross a b r)*S.E d
private lemma upwind {H:Hilbert}{a b:Axis}(S:OS.Semigroup H a)(r:b≠a)(x:H)(u v:ℝ≥0){f g:ℕ→ℝ≥0}(p:Tendsto f atTop (𝓝 u))(t:Tendsto g atTop (𝓝 v)): Tendsto (fun i=> argSpace S r (f i) (g i) x) atTop (𝓝 (argSpace S r u v x)):=
 by
 let W(i:ℝ≥0 × ℝ≥0):= S.U ((i.2:ℝ) • cross a b r) (S.E i.1 x)
 have h : Continuous W := cont_cross S (fun i : ℝ≥0 × ℝ≥0=>S.E i.1 x) (fun i : ℝ≥0 × ℝ≥0 => (i.2:ℝ) • cross a b r) ((S.continuousE x).comp continuous_fst) (by fun_prop)
 have ht:Tendsto (fun i=> W (f i,g i)) atTop (𝓝 (W (u,v))):=(h.tendsto _).comp (p.prodMk_nhds t)
 simp only [argSpace,mul_apply_eq_comp] -- tune
 exact ht
lemma timeBeam (h:∀ (x y:Γ), 0≤ (x:ℝ)→0≤ (y:ℝ)→C.Pass (argSpace S r (x:ℝ).toNNReal (y:ℝ).toNNReal) (argSpace Q r.symm (y:ℝ).toNNReal (x:ℝ).toNNReal)): Beam r S Q C:= by
 intro x y; let k (x:ℝ≥0)(i:ℕ):=⌊ x / mill M i⌋₊+1; let f(x:ℝ≥0)(i:ℕ):= whenly M i (k x i); let w(x:ℝ≥0)(i:ℕ):= notch M i ((k x i):ℤ)
 have hv(x:ℝ≥0)(i:ℕ):(w x i:ℝ)=(f x i:ℝ):= natural_time ..
 refine C.passLimit atTop (u:=fun i =>argSpace S r (f x i) (f y i)) (v:=fun i=>argSpace Q r.symm (f y i) (f x i)) (a:=argSpace S r x y) (b:=argSpace Q r.symm y x) ?_ ?_ ?_
 · intro i; exact upwind S r i x y (shade M x) (shade M y)
 · intro i; exact upwind Q r.symm i y x (shade M y) (shade M x)
 refine Eventually.of_forall (fun i=>?_); let p:=w x i; let q:=w y i
 have he:=h p q (by unfold p; rw [hv]; positivity) (by unfold q; rw [hv]; positivity)
 unfold p q at he; rw [hv,hv, Real.toNNReal_coe, Real.toNNReal_coe] at he; exact he
lemma priceL (h:∀ (ν:Axis),ν≠a→ν≠b→∀ p:Γ,C.Pass (trans S ((p:ℝ) • basis ν)) (trans Q ((p:ℝ) • basis ν))): Behind S Q C:=by
 have he(i:Axis)(v:i≠a)(p:i≠b)(z:ℝ): C.Pass (trans S (z • basis i)) (trans Q (z • basis i)):= by
   obtain ⟨k,q,t⟩:= mem_closure_iff_seq_limit.mp (daylight M z)
   exact C.passLimit atTop (fun x=> ((S.unit.moves x).tendsto _).comp (t.smul tendsto_const_nhds)) (fun x=> ((Q.unit.moves x).tendsto _).comp (t.smul tendsto_const_nhds)) (Eventually.of_forall (fun u=> h i v p (⟨k u,q u⟩:Γ)))
 intro x v y
 have ht(z:E4) : ∑ i:Axis, z i • basis i=z:= by ext1 i;simp
 suffices ∀ p:Finset Axis,C.Pass (trans S (∑ i∈p,x i • basis i)) (trans Q (∑ i∈p,x i • basis i)) by simpa [ht] using this Finset.univ
 intro p; induction p using Finset.induction_on with
 | empty => simp only [Finset.sum_empty, trans, Orbit.origin]; exact C.one
 | insert i p d ih=>
    rw [Finset.sum_insert d]; by_cases u:i=a
    · simp_rw [u,v,zero_smul,zero_add]; exact ih
    by_cases hb:i=b
    · simp_rw [hb,y,zero_smul,zero_add]; exact ih
    rw [trans_sum,trans_sum]; exact (he i u hb _).times ih
end YM.Picket
