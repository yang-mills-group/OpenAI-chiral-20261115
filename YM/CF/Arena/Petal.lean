import YM.CF.Arena.Water
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
section currents
variable {A:ℝ} {M W p k:ℕ}
lemma Foot.change{v:Site c}{f:SpaceX G c}{j:ℕ}(h:cFoot p (satX f))(hp:k≤ p)(hv:j < p)(hA:0 ≤ A)(he:CakeF f v M n σ C): Urge f v k j M n σ C A:=by
 refine ⟨he,fun i h'=>h _ (h'.trans_le hp),fun i _ u=>?_⟩; unfold cake; rw [h _ (u.trans_lt hv),smul_zero,norm_zero]; exact hA
lemma kind_m {V W:Tab S}{X Y:Support c}(h:Kind S V W X)(hp:Y ⊆ X):Kind S V W Y:=⟨fun i q=>h.up _ (hp q),fun i q=>h.ht _ (hp q),fun i q=>h.site _ (hp q),fun i q=>h.edge _ (hp q)⟩
lemma urgeS(i:Site c)(v:Site c){P:SpaceX G c}(h:Urge P 0 k p M n σ C A)(he:0<σ)(hp:k ≤ n)(hK:p ≤ n): Urge (Sean v P i) i k p M n σ C A:=by
 let Q:=Sean v P i; let s:=tide v i h.1; have hz: ‖(0:InputZ G c)‖<σ:=by rw [norm_zero]; exact he
 refine ⟨s,prism_food v i h.2.1 (((h.1.ledger _ hz).order hp).smooth) (((s.ledger _ hz).order hp).smooth),?_⟩
 intro j w u
 -- pull along te preserves norm. 
 let X:= satX P; let z:=pulseP v i; let G':ℂ→L[ℝ]ℂ:= ContinuousLinearMap.lsmul ℝ ℂ z; let L:=tagT G i; have hL: ‖L‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p=> by rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>norm_le_pi_norm p _
 have ht:‖G'‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun k=>by rw [show ‖G' k‖= _ from norm_mul z k,pulse_a]
 have hg: ContDiffAt ℝ (j:ℕ∞ω) X (L 0):= (map_zero L).symm ▸ ((h.1.ledger _ hz).order (u.trans hK)).smooth
 apply le_trans ?_ (h.2.2 j w u); unfold cake; rw [show satX (Sean v P i)=G' ∘ X ∘ L from funext fun v=>by change z * P (Lattice.translate _ _)=_; rw [←trn]; rfl,G'.iteratedFDeriv_comp_left (hg.comp _ L.contDiff.contDiffAt) le_rfl, Push.Uniform.iter_lin_at hg,map_zero,norm_smul,norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le ..).trans; refine (mul_le_of_le_one_left (norm_nonneg _) ht).trans ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)); exact Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=> hL)
end currents
section launch
local instance : Nonempty (Tab S):=⟨⟨Classical.choice (Tree.select _ S.patch.odd_side),Classical.ofNonempty⟩⟩
structure Woven (F:Tab S→FileM c G)(M:Tab S→ DirP c)(r k n:ℕ)(σ C D:ℝ):Prop where
 dawn(t:Tab S)(i j:Site c) : M t i j≠0→separation i j ≤ r
 crew(t:Tab S)(i j:Site c): Urge (M t i j) i 2 k r n σ C D
 tracks(t t':Tab S)(i j:Site c) :Kind S t t' (pavilion r i)→M t i j=M t' i j
 power(t:Tab S)(i:Site c): Urge (F t i+dict (M t) i) i 2 4 r n σ C D
abbrev wage(p:ℕ):ℕ:= 1+(plot (p+p)* Fintype.card (TypeFace 1 × SU.group.ColorIndex))
-- 2 hammer. usable beforeL
lemma weave(n:ℕ)(h:5 ≤ n):∃ M K, CapY M ∧ nib K ∧ (∀ l,l≤M l)∧ ∀ {c f:Side}(S:StepData (More c) f) (Φ:Tab S→FileM (More c) G) (r:ℕ)(σ C D:ℝ), 0<σ→σ ≤1→0≤D→D≤C→ M r < (More c).val → (∀ V W i,Kind S V W (pavilion r i)→ Φ V i=Φ W i) → (∀ t: Tab S,∀ p,Urge (Φ t p) p 2 2 r n σ C D) → (∀ t:Tab S,∀ i:ℕ, 2 ≤ i→i ≤ 4→ Prox (Φ t) i D) → shapeV 0 (fun i=>aria (fun v:Tab S=>Φ v i)) → ∃ A:Tab S→DirP (More c),Woven Φ A (M r) 2 n σ (C*K r) (D*K r):=by
 obtain ⟨R,K,hR,h,hK,H⟩:=trunkM G n Thera.yet_one h; let N:= fun i=> R i+i; let X(v:ℕ):ℝ:=(wage v:ℝ)
 let P(v:ℕ):ℝ:=2+plot v*2 + (X v)^4*2
 let S(v):= P v+(K v+K v); have hN':∀ i,R i ≤ N i:=fun i=>Nat.le_add_right ..; have hx:nib X:=by unfold X wage; push_cast; exact (nib_const 1 zero_le_one).add ((plot_n (CapY.lives.add CapY.lives)).mul (nib_const _ (by positivity)))
 have hp:nib P:= ((nib_const _ (by positivity)).add ((plot_n CapY.lives).mul (nib_const _ (by positivity)))).add ((hx.pow 4).mul (nib_const _ (by positivity))); have hS:nib S:= hp.add (hK.add hK)
 refine ⟨N,S,hR.add CapY.lives,hS,fun i=>(h i).trans (hN' i),?_⟩; intro c f S' Φ r σ C D hs hσ hD hC Hx hP ht hx' hΦ
 let Y(i):= aria (fun v:Tab S'=> Φ v i); have hz:=hib hK r; have he:0 ≤ P r:=hib hp r; have ha(i): Urge (Y i) i 2 2 r n σ C D:= urgeM _ (fun v:Tab S'=> ht v _) hs (by omega) (by omega); have h0: ‖(0:InputZ G (More c))‖<σ:=by simpa using hs
 have hb:0 ≤ C:=hD.trans hC; obtain ⟨B,Q,W,hB,hQ,hW,HQ,HW,hY⟩:= H r σ hs hσ D C hD hC Y hΦ ((hN' r).trans_lt Hx) (fun i=>(ha i).1) (ha 0).2.1 ((ha 0).2.2 2 le_rfl le_rfl) (fun i u v=> voyage Φ i (fun t=>hx' t _ (by omega) v) fun V t=>(((ht V t).1.ledger _ h0).order (v.trans (by omega))).smooth)
 obtain ⟨U,u₁,u₂,u₃⟩:= river hB hs (by omega)
 obtain ⟨Z,hZ⟩:= isthmus (Site (More c)) (M:=SpaceX G (More c)) univ; let L(t:Tab S'):= zig Φ t Z
 let V(t):=L t + U; have hN:=hN' r; have hd:r≤N r:= (h r).trans hN; have hl:2≤P r:=by unfold P; have hv:=Nat.cast_nonneg (α:=ℝ) (plot r); linarith only [hv,(show 0 ≤ (X r)^4 from by have hc:= hib hx r; positivity)]
 refine ⟨V,⟨?_,?_,?_,?_⟩⟩
 · intro t i j hp; by_contra! hu; apply hp; change L t i j+U i j=0; rw [show U i j=0 from not_not.mp (mt (u₁ i j) (not_le.mpr (lt_of_le_of_lt hN hu))),show L t i j=0 from zig_p hP i j ((separation_comm ..).symm ▸ (lt_of_le_of_lt hd hu)), add_zero]
 · intro t i j; obtain ⟨h1,h2⟩:=u₂ i j; let a:SpaceX G (More c):= L t i j; let b:=U i j
   have hp:Urge b i 2 2 (N r) n σ (C*K r) 0:= Foot.change h2 (by decide) (by decide) le_rfl (h1.under le_rfl hN le_rfl); have ht:Urge a i 2 2 r n σ (C+C) (D+D):= zig_U (F:=Φ) (Z:=Z) i j ht (by omega) (by omega) hs; have hv:P r+K r ≤ S r:=by unfold S; linarith only [hz]
   refine (urge_add a b (ht.under le_rfl le_rfl hd) hp hs (by omega) (by omega)).under ?_ ?_ le_rfl
   · nlinarith only [mul_le_mul_of_nonneg_left hv hb,mul_le_mul_of_nonneg_left hl hb]
   nlinarith only [mul_le_mul_of_nonneg_left hv hD,mul_le_mul_of_nonneg_left hl hD,mul_nonneg hD hz]
 · intro t v i j p; change L _ i j+_ = L _ i j + _; rw [show L t i j=L v i j from boardS i j hP (kind_m p (by intro u hu; exact (theatre ..).mpr (((theatre ..).mp hu).trans hd)))] -- tune shadows
 intro t i
 let A:= aria (fun v:Tab S'=> imp Φ t v Z r i)
 have he: Φ t i + dict (V t) i= Sean 0 (Q+W) i+A:=by
    have hi:Φ t i= Y i+∑ j, L t i j:= zig_sum hZ i
    unfold V; rw [hi,dict_p]; rw [←u₃,←hY,show Sean 0 (Y 0+B) i=Y i+Sean 0 B i from ?_]; unfold dict L; rw [zig_tot _ hP]; unfold A; abel
    ext1 v; change _=Y i v+ _; rw [show Y i v=_ from hΦ i v]; exact mul_add ..
 have hQ':Urge (Sean 0 Q i) i 2 4 (R r) n σ (C*K r) (D*K r):= urgeS i _ ⟨hQ.under le_rfl le_rfl (mul_le_mul_of_nonneg_right hC hz),HQ,fun j _ u=> pollen hs hQ (by omega)⟩ hs (by omega) (by omega)
 have hX: Urge (Sean 0 W i) i 2 4 (R r) n σ (C*K r) 0:= urgeS i _ (Foot.change HW (by decide) (by decide) le_rfl hW) hs (by omega) (by omega)
 let J:=plot r; have hh:1 ≤ X r:=Nat.one_le_cast.mpr (show 1 ≤ wage r from Nat.le_add_right ..)
 let A':= C*P r; let D':= D*P r; have hA:Urge A i 2 4 (N r) n σ A' D':=by
    refine urgeM _ ?_ hs (by omega) (by omega); intro y
    have hy (k:ℕ)(p:2 ≤ k)(hx:k ≤ 4):=merge_v Φ t y Z hP i hs (k:=2) (show 2 ≤ n by omega) (fun v i=>⟨(ht v i).1,(ht v i).2.1⟩) (fun v=>hx' v k p hx) (l:=k) (show k≤n by omega) hD; obtain ⟨h1,h2,h3⟩:=hy 2 le_rfl (by decide)
    have he: ((plot r:ℝ)*2) ≤ P r:=by unfold P; have hf: 0≤ X r:= zero_le_one.trans hh; linarith only [(pow_nonneg hf 4)]; -- tune
    refine ⟨h1.under le_rfl (Nat.add_le_add_right (h r) _) (by unfold A'; nlinarith only [mul_le_mul_of_nonneg_left he hb]),h2,fun i p v=>?_⟩
    let K:ℕ:=plot (r+r)* Fintype.card (TypeFace 1 × SU.group.ColorIndex); have ht : (K:ℝ)^i ≤ (X r)^4:= le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_add_left K 1)) _) (pow_le_pow_right₀ hh v)
    refine (hy i p v).2.2.trans ?_; change (K:ℝ)^i*(D+D) ≤ D'; refine (mul_le_mul_of_nonneg_right ht (add_nonneg hD hD)).trans ?_; unfold D' P; nlinarith only [hD,mul_nonneg hD (Nat.cast_nonneg (plot r) (α:=ℝ))]
 rw [he,show Sean 0 (Q+W) i= _ from scroll_p 0 i]; refine (urge_add _ _ ((urge_add _ _ hQ' hX hs (by omega) (by omega)).under le_rfl le_rfl hN) hA hs (by omega) (by omega)).under ?_ ?_ le_rfl
 · unfold A' S; exact le_of_eq (by ring)
 unfold D' S; nlinarith only [mul_nonneg hD hz]
end launch
end YM.CF.Arena
