import YM.SU5.Relativistic.OddBook
import YM.SU5.Relativistic.OddLimit

/-! # Support-wise literal lift. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
local notation "W"=>wingspan Λ l
variable (i' k':ℕ) (S : Finset Cover) {b c:Bool}
variable {f g: Family (tent Y H)}
private lemma transSpan {n i:Side}(p:n=i){f g:Mark n} (h: ship p f=ship p g): f=g:=by subst p; exact h
lemma parked (p:InTest K true S b f):AtSupport b (Satin.region S (side Y i' s)) (distribute Y H s i' f):= ship_box _ _ (p.support _)
lemma charge_ext (p:Tivoli S ((K).c (momentm Y i' s))) (h:InTest K true S b f)(e:InTest K true S b g) (w:distribute Y H s i' f=distribute Y H s i' g): f=g:=by
 cases b; exact stationary_ext _ _ _ _ _ p.hosp h e w; exact single_ext _ _ p.hosp h e (transSpan (terrain Y H ..) w)
lemma descendBack {f:Mark (side Y i' s)}{b:Bool}(h:AtSupport b (Satin.region S (side Y i' s)) f)(w:Tivoli S ((K).c (momentm Y i' s))) : ∃ F:Family (tent Y H),InTest K true S b F∧ distribute Y H s i' F=f:=by
 cases b
 · exact ⟨_,stationed_back Y H s S i' f h,authorized_back Y H s S i' f h w⟩
 let p:= terrain Y H (Y.ir i') s
 have hx:= ship_box p.symm S h; refine ⟨FermionSlab.extendAtlas S _ _ w (ship p.symm f),OddList S _ _ w (ship p.symm f) hx,?_⟩; unfold distribute; rw [refunded S _ _ w (ship p.symm f) hx]; exact reverse _ _
lemma qualify {S:Finset Cover}(p:legalAt Y s i' k')(x:InTest K true S b f)(u:Tivoli (W S) ((K).c (momentm Y i' (s+1)))) : ∃ g: Family (tent Y H), InTest K true (wingspan Λ l S) b g∧ distribute Y H (s+1) i' g= Tapestry.ascender Y s i' k' (distribute Y H s i' f):= descendBack Y H (s+1) i' _ (Tapestry.ascendSupport Y s i' k' S p (parked Y H s i' S x)) u

noncomputable def moveUp (b:Bool)(F:Family (tent Y H)) : Family (tent Y H):= if p:InTest K true S b F ∧ legalAt Y s i' k' ∧ Tivoli (W S) ((K).c (momentm Y i' (s+1))) then (qualify Y H s i' k' p.2.1 p.1 p.2.2).choose else 0
local notation "M"=>moveUp Y H s i' k'
lemma stay (F:Family (tent Y H)) (b:Bool): InTest K true (W S) b (M S b F):=by
 unfold moveUp; split
 next p=> exact (qualify Y H s i' k' p.2.1 p.1 p.2.2).choose_spec.1
 next p=> exact InTest.zero
lemma rebased (p:legalAt Y s i' k')(x:InTest K true S b f)(u:Tivoli (W S) ((K).c (momentm Y i' (s+1)))): distribute Y H (s+1) i' (M S b f) = Tapestry.ascender Y s i' k' (distribute Y H s i' f):=by unfold moveUp; rw [dif_pos ⟨x,p,u⟩]; exact (qualify Y H s i' k' p x u).choose_spec.2
lemma base_even (p:legalAt Y s i' k')(x:InTest K true S false f)(u:Tivoli (W S) ((K).c (momentm Y i' (s+1)))): M S false f=block Y H s i' k' S f:=charge_ext Y H (s+1) i' _ u (stay ..) (booked ..) ((rebased Y H s i' k' S p x u).trans (reserved Y H s S i' k' p x u).symm)
lemma together {T: Finset Cover}(p: Detached Λ l S T) (q:Host Y H i' s (S∪T))(t:legalAt Y s i' k') (x:InTest K true S b f)(y: InTest K true T c g) :
 M (S∪T) (b.xor c) (f*g) = M S b f * M T c g:=by
 have hv:= q.usable 1
 refine charge_ext Y H (s+1) i' (W (S∪T)) hv (stay ..) (((stay Y H s i' k' S f b).mono (wingspan_mono subset_union_left)).mul ((stay Y H s i' k' T g c).mono (wingspan_mono subset_union_right))) ?_
 rw [rebased Y H s i' k' _ t ((x.mono subset_union_left).mul (y.mono subset_union_right)) hv,(distribute_arith Y H (s+1) i' _ _ 1).2.1,rebased Y H s i' k' S t x ((Host.shrink Y H subset_union_left q).usable 1),rebased Y H s i' k' T t y ((Host.shrink Y H subset_union_right q).usable 1),(distribute_arith Y H s i' f g 1).2.1]; unfold Tapestry.ascender nextMark
 let Q:=((Y.voyage i').X (Y.uv k')).gram; let A:= ((Y.voyage i').X (Y.uv k')).wave; let K₁:= steps Λ.V (Y.ir i') Λ.block (Y.uv k'); let Y':= (Y.voyage i').CapeT; let G:= (Vale.apt (Y.ir i') Λ.block Λ.R.L s); let u:= (fullness Y i' k' t.1).cap_grant
 obtain ⟨t'⟩:= u.grant s t.2; obtain ⟨u',v,aX,F0,j⟩:= t'.cap
 exact separated_mult G (K₁ s) Λ.K.j ((A s).val) (Q (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Q (s+1)).beta (Y' s) (R:=aliasLaw Λ) (show Stencil.LaurentRadius _ Λ.R.L _ from Journey.legal Λ) F0.bill (u.branch s t.2) t'.legal.1 t'.legal.2 _ _ (parked Y H s i' _ x) (parked Y H s i' _ y) (tissue Y i' s) (Host.far Y H p q 0)
variable (a:Axis)(z:ℤ)
local notation "L₁"=> (Λ.R.L.val * z:ℤ)
local notation "S'"=>reflectedBox a z S
local notation "T₀"=> reflectedBox a (L₁) (W S)
-- for operator norm estimates later
lemma festive : ∀ᶠ i in atTop,∀ k:ℕ,legalAt Y s i k→∀ f:Family (tent Y H), InTest K true S b f→ moveUp Y H s i k (S') b (mirror K a z f)=mirror K a (L₁) (moveUp Y H s i k S b f):=by
 filter_upwards [turning Y H (s+1) (W S), turning Y H (s+1) (W (S')), turning Y H (s+1) (W (S')∪(T₀))] with i u v w k p f x
 let g':=moveUp Y H s i k S b f; let g:=moveUp Y H s i k (S') b (mirror K a z f)
 apply charge_ext Y H (s+1) i _ w ((stay Y H s i k (S') _ b).mono subset_union_left) ((axial K a (L₁) (stay Y H s i k S _ b)).mono subset_union_right)
 rw [(distribute_arith Y H (s+1) i g' g' 0).2.2.2.2, rebased Y H s i k _ p (axial _ _ _ x) v, rebased Y H s i k _ p x u,(distribute_arith Y H s i f f 0).2.2.2.2]; unfold Tapestry.ascender nextMark
 let Z:=((Y.voyage i).X (Y.uv k)).gram; let A:= ((Y.voyage i).X (Y.uv k)).wave; let K₁:= steps Λ.V (Y.ir i) Λ.block (Y.uv k); let V:= (Y.voyage i).CapeT; let G:= (Vale.apt (Y.ir i) Λ.block Λ.R.L s); let h:= (fullness Y i k p.1).cap_grant
 obtain ⟨t⟩:= h.grant s p.2; obtain ⟨y,u',v',F0,s'⟩:=t.cap
 exact rising G (K₁ s) Λ.K.j ((A s).val) (Z (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Z (s+1)).beta (V s) a z (h.aligned s p.2) (parked Y H s i S x) (h.branch s p.2) F0 (show Stencil.LaurentRadius _ Λ.R.L (aliasLaw Λ) from Journey.legal Λ) t.legal.1 t.legal.2
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
