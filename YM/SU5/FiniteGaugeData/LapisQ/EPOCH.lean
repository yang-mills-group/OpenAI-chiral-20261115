import YM.SU5.FiniteGaugeData.LapisQ.Lyre
/-! # Torus epoch WP22A. With same P(cost.Structure). actual gate still not substitute Fin tests.See Occupe.
-/
set_option autoImplicit false
set_option maxHeartbeats 620000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06 Complex
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical ComplexOrder
set_option quotPrecheck false
namespace Tulipe
open Vulcan Willow Nosh Cordon
variable {α:Type} [Fintype α] {n:Side} {ρ C Δ ε σ K:ℝ} [DecidableEq α]
variable (m:ℕ→Side) (v:Tendsto (fun i=>(m i).val) atTop atTop)
variable (s s':Melody m)(x y:Phase4) (ℓ:ℕ)
private lemma fee_δ (z y x v d:ℂ)(h:‖z-x‖≤ ε/3)(p:‖y-v‖ ≤ ε/3) (t: ‖x-v-d‖ ≤ ε/3) : ‖z-y-d‖≤ ε:=by
 calc _= ‖((z-x)-(y-v))+(x-v-d)‖ := by congr 1; ring
      _ ≤ (ε/3+ε/3)+ε/3:= (norm_add_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add h p)) t)
      _ = _:=by ring
include v
lemma ocho (σ ρ K:ℝ) : ∃ (s p q:Melody m),∀ᶠ r:ℕ in atTop,∀ᶠ i:ℕ in atTop, r+1<(m i).val ∧∀ {u:Stage}{P:Bed}{C:ℝ}{A:Matrix (Body 2 (m i)) (Body 2 (m i)) ℝ}, Gate u P ρ C σ K (m i) A → MtRequest (s i) ℓ (p i) (q i) (road A r) :=by
 let e:= payable ℓ/3; have he: 0<e:=by have hx:= part_p ℓ; unfold e; positivity
 obtain ⟨x,u,h⟩:= carriage σ ρ K he; obtain ⟨t,L,hT⟩:= buildH ℓ x u he
 obtain ⟨s,p⟩:= aria m v (uniformM t) (by funext; simp [uniformM]); choose y hv using fun i:Axis=> aria m v (rung L i) (by funext t; by_cases he:t=i <;> simp [he,rung,pureW] -- tune eq
                                                                            )
 let P(a:Axis)(j:colorX ℓ):= fun i:ℕ=> y a i+ shiftU (s i) ℓ j
 have hx(a:Axis)(j:colorX ℓ):note m (P a j) (dyad ℓ j t L a):= nOrder m _ _ _ _ (hv a) (leadR m s (uniformM t) ℓ p j)
 let F(j:colorX ℓ)(a:Axis):= Exterior.q (dyad ℓ j t L a)
 have hX(a:Axis)(j:colorX ℓ)(z:F j a≠0)(v0:‖F j a‖<x) : ∀ᶠ r:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ {u:Stage}{P':Bed}{C:ℝ}{A:Matrix (Body 2 (m i)) (Body 2 (m i)) ℝ}, Gate u P' ρ C σ K (m i) A → ‖road A r (P a j i)-camp (F j a) f0 f0‖ ≤ e:=by
    obtain ⟨δ,q,c⟩:= h (F j a) z v0; filter_upwards [c] with r f; filter_upwards [v.eventually_gt_atTop (r+1),(Metric.tendsto_nhds.mp (hx a j) δ q)] with i v h u P' C A g; exact f g v (le_of_lt (show ‖harp (P a j i)-F j a‖<δ from (by rwa [dist_eq_norm] at h)))
 refine ⟨s,y 0,y 2,?_⟩
 have he(j:colorX ℓ):= hT j; let P' := (Tendsto (fun x:ℕ=>x) atTop atTop)
 filter_upwards [(eventually_all.mpr (fun i=> hX 0 i (hT i).1 (hT i).2.2.1)),eventually_all.mpr (fun i=> hX 2 i (hT i).2.1 (hT i).2.2.2.1)] with r p h
 filter_upwards [v.eventually_gt_atTop (r+1),eventually_all.mpr p,eventually_all.mpr h] with i u p h; exact ⟨u,fun g j=> fee_δ _ _ _ _ _ (p j g) (h j g) (hT j).2.2.2.2⟩
-- to all periods. eventually on r uniform k.
omit v
private abbrev Pplus (i:ℕ):Side:=⟨i+1,by omega⟩
private lemma leads : Tendsto (fun i=>(Pplus i).val) atTop atTop:=by
 refine tendsto_atTop.mpr (fun i=>(eventually_ge_atTop i).mono (fun z v=> le_trans v (Nat.le_succ _)))
lemma catchMX (σ ρ K:ℝ): ∀ᶠ r:ℕ in atTop,∃ N:ℕ,∀ n:Side,N≤n.val→ r+1<n.val ∧∃ s p q:Site n,∀ {u:Stage}{P:Bed}{C:ℝ}{A:Matrix (Body 2 n) (Body 2 n) ℝ},Gate u P ρ C σ K n A → MtRequest s ℓ p q (road A r):=by
 obtain ⟨s,p,q,H⟩:= ocho Pplus leads ℓ σ ρ K; filter_upwards [H] with r y; obtain ⟨N,u⟩:= eventually_atTop.mp y; refine ⟨N+1,fun n v=>?_⟩; let i:= n.val-1; have w:N≤ i:= (by omega); let b:= Pplus i; have he: n=Pplus i:=Subtype.ext (by change n.val=i+1; omega); rw [he]; exact ⟨(u i w).1,s i,p i,q i,(u i w).2⟩ -- dep eq error rwp.C.
-- now real gauge coefficient.YA.UV statistic witness
omit m in
private lemma fareMX(r ℓ:ℕ):∃ c:ℝ,0<c∧tariffMX r ℓ c<1/2:=by
 -- use filter due denominator tiny.L.
 let f(x:ℝ):= tariffMX r ℓ x; have hh:f 0=0:=by simp [f,tariffMX]
 have hp:Tendsto f (𝓝[>] 0) (𝓝 0):=by simpa only [hh] using ((show Continuous f from (by unfold f tariffMX; fun_prop)).continuousAt (x:=0)|>.tendsto).mono_left (@nhdsWithin_le_nhds ℝ _ 0 (Set.Ioi 0)) -- syntax
 obtain ⟨c,h,u⟩:= ((hp.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).and self_mem_nhdsWithin).exists; exact ⟨c,u,h⟩
omit m in
abbrev songV(A: Matrix (Body 2 n) (Body 2 n) ℝ)(x:Site n):ℝ:= A (0,f0) (x,f0)
lemma fleetMX (σ ρ K:ℝ): ∃ c:ℝ,0<c∧∃ r N:ℕ,∀{n:Side}{u:Stage}{P:Bed}{C:ℝ}{A:Matrix (Body 2 n) (Body 2 n) ℝ},Gate u P ρ C σ K n A →N≤ n.val→ ∃ y∈ marketZ r,lapse ℓ y∧ c< |songV A (wrap n y)|:=by
 obtain ⟨r,N,u⟩:= (catchMX ℓ σ ρ K).exists; obtain ⟨c,h,t⟩:=fareMX r ℓ; refine ⟨c,h,r,N,fun {n u' P C A} g v=>?_⟩; obtain ⟨he,s,p,q,h'⟩:=u n v; by_contra! y
 let X:=machine s ℓ p q (road A r); let U(x: Site n):ℂ:= ↑(songV A x); refine t.not_ge ((earnsMX s p q ℓ _ (h' g)).trans (priceMX s p q ℓ r U he h.le (fun x t v=> by unfold U; rw [Complex.norm_real]; exact y x t v)))
end Tulipe
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Tulipe.fleetMX
