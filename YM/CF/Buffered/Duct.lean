import YM.CF.Buffered.Oblique
/-! Price Tone channels comparison for 3x tiling. Size edge simple per cell.
No frame determinant on the gluing: assign all crossings. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Crust.Grid
open Function Filter Finset Lattice Wilson RG PathData Work.F03
open Cube Region Roost Rush
open scoped InnerProductSpace Matrix.Norms.Frobenius BigOperators Topology
variable {G:Gauge}{N P D:Side}{a b r C L β:ℝ}{u: ℤ}{s:ℕ}
local notation "Q" => Tower D
private lemma flags_turn (s:Signed)(x:ℝ)(U:Config G P): flags x (pull s 0 U)=∅ ↔ flags x U=∅:=by classical rw [← Work.H03.flags_send (U:=U) s 0 x, Finset.image_eq_empty]
variable (Y:Tower D→ Config G P)(K:Planck N P D) {A:Config G N}
namespace Plan
variable (X:Signed)
abbrev rot (p:Signed) (P:Side) := p.actEquiv (R:=Per P)
def faces (X:Signed) := ((Equiv.prodCongr (Equiv.refl Q) (rot X P).toEquiv).trans (send K)).trans (rot X N).symm.toEquiv
variable {Y K}
private lemma lforge (U:Config G N)(V:Config G P)(x:Site N)(y:Site P)(z:Site N)(e:affine X 0 x=z) (h:Legend s a U V z (affine X 0 y)) : Legend (G:=G) s a (pull X 0 U) (pull X 0 V) x y:=by
 intro l g
 let L:=l.map (·.rotate X); have ht:L.length=l.length:= List.length_map ..
 have h₁: Lattice.travel (pull X 0 U) x l=Lattice.travel U z L:=by rw [travel_pull, e]
 have h₂: Lattice.travel (pull X 0 V) y l=Lattice.travel V (affine X 0 y) L:=travel_pull ..
 rw [h₁,h₂,← ht]; exact h L (ht.trans_le g) -- Nat ℓ
private lemma hearth (t:Tower D)(x:Site P) : affine X 0 (faces K X (t,x))=send K (t,affine X 0 x):=by unfold affine; rw [add_zero,add_zero]; exact (rot X N).apply_symm_apply (send K (t,X.act x)) -- tune
lemma legends (h:∀ t: Tower D,∀ x: Site P, Legend s a A (Y t) (send K (t,x)) x) (t:Tower D) (u:Site P) : Legend s a (pull X (0:Site N) A) (pull X (0:Site P) (Y t)) (faces K X (t,u)) u :=
 lforge X A (Y t) (faces K X (t,u)) u _ (hearth X t u) (h t _)
private lemma workPiece {F:PathData G}{p:BudgetPoint}{c:Clip}{N:Side}(U:Config G N)(g:F.Bounds c r C L)(h:0≤β): |F.principal c p β U-β*∑ x,F.baseTerm c p U x| ≤ Graph.taxY N β p.threshold C L:= by
 obtain ⟨u,v⟩:=Graph.oath g p U; unfold PathData.principal Graph.taxY; rw [mul_add,add_assoc, add_sub_cancel_left] -- wrong rw
 exact (abs_add_le ..).trans (add_le_add (by rw [abs_mul,abs_of_nonneg h]; exact mul_le_mul_of_nonneg_left u h) v)
def cellsCost(N D P:Side)(β t C L:ℝ)(s:ℕ)(a r d:ℝ):= β*Fintype.card (Face (Per N))*bend_cost s a r C d + (Graph.taxY N β t C L +(Fintype.card (Tower D):ℝ)*Graph.taxY P β t C L) -- change s Nat
private lemma priced {F:PathData G}{p:BudgetPoint}{T:Clip}(g:F.Bounds T r C L)(t:∀ k:Tower D,∀ x: Site P,Legend s a A (Y k) (send K (k,x)) x)(u:0≤a)(p₀:flags p.threshold A=∅)(p₁:∀ i:Tower D,flags p.threshold (Y i)=∅)(k:2≤ s)(w:0≤C)(b:0≤β):
 F.principal T p β (pull X 0 A) ≤ ∑ i:Tower D, F.principal T p β (pull X 0 (Y i))+ cellsCost N D P β p.threshold C L s a r T.direct:=by
 let rB(x:Site N)(i:PlaqAxes):= F.baseTerm T p (pull X 0 A) (x,i)
 let rQ(x:Tower D)(y:Site P)(i:PlaqAxes):= F.baseTerm T p (pull X 0 (Y x)) (y,i)
 let Z:=cellsCost N D P β p.threshold C L s a r T.direct
 let M:=faces K X; let A':=∑ x: Face (Per N), rB x.1 x.2; let S(i):=∑ x:Face (Per P),rQ i x.1 x.2
 let k':=Graph.taxY P β p.threshold C L; let w':= Graph.taxY N β p.threshold C L; let U:=bend_cost s a r C T.direct; let D':=(Fintype.card (Tower D):ℝ); let E: ℝ:=Fintype.card (Face (Per N)); let p''(i:Tower D):=F.principal T p β (pull X 0 (Y i))
 have he : A' ≤ (∑ i, S i)+ E*U := by
    have hx(i: Tower D × Site P) (k':PlaqAxes): rB (M i) k'≤ rQ i.1 i.2 k'+U:=by rw [add_comm (rQ _ _ _)]; exact sub_le_iff_le_add.mp (Legend.toll g (legends X t _ _) k u ((flags_turn ..).2 p₀) ((flags_turn ..).2 (p₁ _)) w _) -- tune occurrence
    let V:= Equiv.prodCongr M (Equiv.refl PlaqAxes); have ht: E=((Fintype.card ((Tower D× Site P)×PlaqAxes)):ℝ):=by unfold E; rw [Fintype.card_congr V.symm] -- defeq
    unfold A'; rw [←Equiv.sum_comp V (fun x:Face (Per N)=>rB x.1 x.2)]; apply le_trans (sum_le_sum (fun x _=> hx x.1 x.2)); unfold S; rw [sum_add_distrib,sum_const, card_univ,nsmul_eq_mul,ht]; simp_rw [Fintype.sum_prod_type]; exact le_rfl
 change F.principal _ _ _ _ ≤ ∑ i:Tower D,p'' i+Z
 have hu: F.principal T p β (pull X 0 A)-β*A' ≤ w':= (le_abs_self _).trans (workPiece _ g b)
 have hx(i): β*S i - k' ≤ p'' i:= by have ht: |p'' i-β*S i| ≤ k':= workPiece _ g b; linarith only [(abs_le.mp ht).1]
 have hz := sum_le_sum (s:=univ) fun i _=> hx i; rw [sum_sub_distrib,sum_const,←mul_sum,card_univ,nsmul_eq_mul] at hz
 change β*(∑ i,S i)-D'*k'≤∑ i,p'' i at hz; change _≤_ + (β*E*U + (w'+D'*k')); nlinarith only [hz,mul_le_mul_of_nonneg_left he b,hu] -- ring poly
lemma grouped {F:PathData G}{p:BudgetPoint}{T:Clip}(g:F.Bounds T r C L)(t:∀ k:Tower D,∀ x: Site P,Legend s a A (Y k) (send K (k,x)) x)(u:0≤a)(p₀:flags p.threshold A=∅)(p₁:∀ i:Tower D,flags p.threshold (Y i)=∅)(k:2≤ s)(w:0≤C)(b:0≤β) :
 F.inChannels T p β A ≤ ∑ i:Tower D,F.inChannels T p β (Y i)+cellsCost N D P β p.threshold C L s a r T.direct:=by
 let x:=cellsCost N D P β p.threshold C L s a r T.direct; let N':ℝ:=Fintype.card Signed
 unfold inChannels; refine le_trans (mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> priced i g t u p₀ p₁ k w b) (by positivity)) ?_; rw [sum_add_distrib, sum_comm, ←mul_sum, sum_const, card_univ, nsmul_eq_mul]; rw [mul_add, inv_mul_cancel_left₀] -- tune rhs sum outside. positivity
 positivity
end Plan
end YM.CF.Buffered.Crust.Grid
#print axioms YM.CF.Buffered.Crust.Grid.Plan.grouped
