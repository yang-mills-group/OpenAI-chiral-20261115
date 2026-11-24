import YM.CF.Tarn.Eon
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
local instance : Nonempty (Tab S):=⟨⟨Classical.choice (Tree.select _ S.patch.odd_side),Classical.ofNonempty⟩⟩
structure Wick (F:Tab S→ FileM c G)(M:Tab S→DirP c)(k n:ℕ)(σ A C:ℝ):Prop where
 axis(t:Tab S)(i j:Site c) : M t i j≠0→separation i j ≤ k
 vows(t:Tab S)(i j:Site c): Urge (M t i j) i 2 1 k n σ A 0
 patch(t t':Tab S)(i j:Site c): Kind S t t' (pavilion k i)→M t i j=M t' i j
 better(t:Tab S)(i:Site c):Urge (F t i+dict (M t) i) i 2 2 k n σ A C
lemma tuft (n:ℕ)(h:2≤n)(Z: SU.group.Color→ₗᵢ[ℝ] SU.group.Color):∃ M K,CapY M∧(∀ i,i ≤ M i)∧ nib K∧ ∀{c f:Side}(S:StepData (More c) f)(r:ℕ)(Φ:Tab S→FileM (More c) G)(σ A C:ℝ),0<σ→σ ≤1 → 0≤ C→ C≤ A→ M r< (More c).val → (∀ t t':Tab S,∀ i:Site (More c), Kind S t t' (pavilion r i)→Φ t i=Φ t' i)→(∀ t i,CakeF (Φ t i) i r n σ A ∧ cFoot 2 (satX (Φ t i)))→(∀ t,Prox (Φ t) 2 C)→ let F:FileM (More c) G:=fun i=>aria (fun t=> Φ t i); LayerP c F→Head (More c) Z F→∃ D,Wick Φ D (M r) n σ (A*K r) (C*K r):=by
 obtain ⟨R,K,hR,h,hK,H⟩:=pool_t n h Z; let N:= fun i=> R i+i; let X(v:ℕ):ℝ:=(Arena.wage v:ℝ)
 let P(v:ℕ):ℝ:=2+plot v*2 + (X v)^2*2
 let S(v):= P v+K v; have hN':∀ i,R i ≤ N i:=fun i=>Nat.le_add_right ..; have hx:nib X:=by unfold X Arena.wage; push_cast; exact (nib_const 1 zero_le_one).add ((plot_n (CapY.lives.add CapY.lives)).mul (nib_const _ (by positivity)))
 have hp:nib P:= ((nib_const _ (by positivity)).add ((plot_n CapY.lives).mul (nib_const _ (by positivity)))).add ((hx.pow 2).mul (nib_const _ (by positivity))); have hS:nib S:= hp.add hK
 refine ⟨N,S,hR.add CapY.lives,fun i=> (h i).trans (hN' i),hS,?_⟩; intro c f S' r Φ σ C D hs hσ hD hC Hx hP ht hx' F hv hΦ
 have hp(t i):Urge (Φ t i) i 2 1 r n σ C 0:= Foot.change (ht t i).2 le_rfl (by decide) le_rfl (ht t i).1; have ha(i): Urge (F i) i 2 1 r n σ C 0:= urgeM _ (fun v:Tab S'=> hp v _) hs (by omega) (by omega); have h0: ‖(0:InputZ G (More c))‖<σ:=by simpa using hs
 have hb:0 ≤ C:=hD.trans hC; obtain ⟨U,u₁,u₂,u₃⟩:= H r σ C D hs hσ hD hC c F hv hΦ ((hN' r).trans_lt Hx) (fun i=>⟨(ha i).1,(ha i).2.1⟩) (voyage Φ 2 hx' fun V t=>(((ht V t).1.ledger _ h0).order (by assumption)).smooth)
 obtain ⟨Z,hZ⟩:= isthmus (Site (More c)) (M:=SpaceX G (More c)) univ; let L(t:Tab S'):= zig Φ t Z
 let V(t):=L t + U; have hN:=hN' r; have hd:r≤N r:= (h r).trans hN; have h0:0 ≤ X r:=hib hx r; have hl:2≤P r:=by unfold P; linarith only [Nat.cast_nonneg (α:=ℝ) (plot r),pow_nonneg h0 2]
 refine ⟨V,⟨?_,?_,?_,?_⟩⟩
 · intro t i j hp; by_contra! hu; apply hp; change L t i j+U i j=0; rw [show U i j=0 from not_not.mp (mt (u₁ i j) (not_le.mpr (lt_of_le_of_lt hN hu))),show L t i j=0 from zig_p hP i j ((separation_comm ..).symm ▸ (lt_of_le_of_lt hd hu)), add_zero]
 · intro t i j; let a:SpaceX G (More c):= L t i j; let b:=U i j; have hp':Urge a i 2 1 r n σ (C+C) (0+0):= zig_U (F:=Φ) (Z:=Z) i j hp (by omega) (by omega) hs
   refine (urge_add a b (hp'.under le_rfl le_rfl hd) ((u₂ i j).under le_rfl le_rfl hN) hs (by omega) (by omega)).under ?_ (by norm_num) le_rfl
   unfold S; nlinarith only [mul_le_mul_of_nonneg_left hl hb]
 · intro t v i j p; change L _ i j+_ = L _ i j + _; rw [show L t i j=L v i j from boardS i j hP (kind_m p (by intro u hu; exact (theatre ..).mpr (((theatre ..).mp hu).trans hd)))] -- tune shadows
 intro t i; let A:= aria (fun v:Tab S'=> imp Φ t v Z r i)
 have he: Φ t i + dict (V t) i= A+ (F i + dict U i):=by
    have hi:Φ t i= F i+∑ j,L t i j:= zig_sum hZ i
    unfold V; rw [hi,dict_p]; unfold dict L; rw [zig_tot _ hP]; unfold A; abel
 have ht:Urge A i 2 2 (N r) n σ (C*P r) (D*P r):=by
    refine urgeM _ ?_ hs (by omega) (by omega); intro y
    obtain ⟨hc,u,v⟩:= merge_v Φ t y Z hP i hs (k:=2) (by omega) ht hx' (by omega) hD
    refine ⟨hc.under le_rfl (Nat.add_le_add_right (h r) _) ?_,u,fun i a b=>?_⟩
    · have he: ((plot r:ℝ)*2) ≤ P r:=by unfold P; linarith only [pow_nonneg h0 2]
      nlinarith only [mul_le_mul_of_nonneg_left he hb]
    rw [le_antisymm b a]; apply v.trans; let K:ℕ:=plot (r+r)* Fintype.card (TypeFace 1 × SU.group.ColorIndex); have hu:(K:ℝ)^2 ≤ (X r)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_add_left K 1)) _
    apply (mul_le_mul_of_nonneg_right hu (add_nonneg hD hD)).trans; unfold P; nlinarith only [hD,mul_nonneg hD (Nat.cast_nonneg (plot r) (α:=ℝ))]
 rw [he]; exact (urge_add _ _ ht ((u₃ i).under le_rfl le_rfl hN) hs (by omega) (by omega)).under (le_of_eq (Eq.symm (mul_add ..))) (le_of_eq (Eq.symm (mul_add ..))) le_rfl
end YM.CF.Tarn
