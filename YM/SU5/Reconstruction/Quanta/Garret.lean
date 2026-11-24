import YM.SU5.Reconstruction.Quanta.Core
import YM.SU5.Reconstruction.Quanta.Tokens
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)

/-! # Lift the actual POS witnesses even odd. Resolution keeps parity upon transfer. -/
open QuantaCore NorthTapes
namespace Garret
variable {g₀:Bool}{S Z:Finset Cover}{f g:Family (tent Y H)}
local notation "W" =>wingspan Λ l
local notation "B" => Λ.block
local notation "L"=>Λ.R.L.val
local notation "↑ₗ" t:max =>(L:ℤ)*t
section pier
variable (n k':ℕ)
local notation "Mx" s:max=>((K).c (momentm Y n s))
local notation "N" s:max=> side Y n s
local notation "Px" s:max=> terrain Y H (Y.ir n) s
local notation "D" s:max=> distribute Y H s n
local notation "Ω"=> aboveD Y H s n k'
variable (t:legalAt Y s n k')
lemma locates (x:InTest K true S g₀ f): AtSupport g₀ (Satin.region S (side Y n s)) (distribute Y H s n f):=ship_box (Px s) S (x.support (momentm Y n s))
include t
lemma beam_size (x:InTest K true S g₀ f) : AtSupport g₀ (Satin.region (W S) (N (s+1))) (Ω f):= (polar_fit_grows Y n k' s ((D s) f) t (locates Y H s n x)).mono (next_contains S _ (N s) (Vale.apt ..)) -- argument? see
omit t
-- honest next height choice for odd or even probes at this native pair
noncomputable def pick (g₀:Bool)(S:Finset Cover)(x:Family (tent Y H)): Family (tent Y H):=
 if h:Tivoli (W S) (Mx (s+1)) then outAtlas (W S) K (momentm Y n (s+1)) h (ship (terrain Y H (Y.ir n) (s+1)).symm (Ω x)) g₀ else 0
-- use specific plane supports below when purchasing square
include t
lemma lamp_jump (x:InTest K true S g₀ f)(h:Tivoli (W S) (Mx (s+1))):
 InTest K true (W S) g₀ (pick Y H s n k' g₀ S f) ∧ (D (s+1)) (pick Y H s n k' g₀ S f)= Ω f:=by
 have he:=ship_box (terrain Y H (Y.ir n) (s+1)).symm (W S) (beam_size Y H s n k' t x)
 rw [pick, dif_pos h]; refine ⟨gradeBook (W S) K (momentm Y n (s+1)) h _ he,?_⟩
 unfold distribute; rw [payed_both _ _ _ h _ he,Tower.reverse]
variable (a:Axis)(z:ℤ)
local notation "z₀"=> ((Λ.R.L.val:ℤ)*z)
lemma beam_reflect (x:InTest K true S g₀ f): Ω (mirror K a z f)= reflMark a z₀ (Ω f):=by
 let Q:=((Y.voyage n).X (Y.uv k')).gram; let A:= ((Y.voyage n).X (Y.uv k')).wave; let K₁:= steps Λ.V (Y.ir n) Λ.block (Y.uv k'); let Y':= (Y.voyage n).CapeT; let g:= (Vale.apt (Y.ir n) Λ.block Λ.R.L s); let p:= (fullness Y n k' t.1).cap_grant
 obtain ⟨t'⟩:= p.grant s t.2; obtain ⟨u',v,aX,F0,j⟩:= t'.cap
 unfold aboveD; rw [(distribute_arith Y H s n f f (0:ℂ)).2.2.2.2]; exact rising g (K₁ s) Λ.K.j ((A s).val) (Q (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Q (s+1)).beta (Y' s) a z (p.aligned s t.2) (locates Y H s n x) (p.branch s t.2) F0 (show Stencil.LaurentRadius _ Λ.R.L _ from Journey.legal Λ) t'.legal.1 t'.legal.2
local notation "Cr"=> (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l))
variable (p:region a z (reserve Λ l) S)
lemma beam_sep (x:InTest K true S g₀ f){τ:Bool}(y:InTest K true Z τ g)(v:∀ i∈Satin.region S (Mx s),∀ j∈Satin.region Z (Mx s), Cr < separation i j): Ω (f*g) = (Ω f)*(Ω g):=by
 let Q:=((Y.voyage n).X (Y.uv k')).gram; let A:= ((Y.voyage n).X (Y.uv k')).wave; let K₁:= steps Λ.V (Y.ir n) Λ.block (Y.uv k'); let Y':= (Y.voyage n).CapeT; let g':= (Vale.apt (Y.ir n) Λ.block Λ.R.L s); let p:= (fullness Y n k' t.1).cap_grant
 obtain ⟨t'⟩:= p.grant s t.2; obtain ⟨u',v₁,aX,F0,j⟩:= t'.cap
 unfold aboveD; rw [(distribute_arith Y H s n f g 0).2.1]; rw [terrain Y H (Y.ir n) s] at v; exact separated_mult g' (K₁ s) Λ.K.j ((A s).val) (Q (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Q (s+1)).beta (Y' s) (R:=aliasLaw Λ) (show Stencil.LaurentRadius _ Λ.R.L _ from Journey.legal Λ) F0.bill (p.branch s t.2) t'.legal.1 t'.legal.2 _ _ (locates Y H s n x) (locates Y H s n y) (tissue Y n s) v
omit t
lemma pole_right (f f':Family (tent Y H))(g₀:Bool): distribute Y H s n (poleForm K a z g₀ f f')= Reflect.chord g₀ • (reflMark a z ((D s) f)* (D s) f'):=by
 unfold poleForm; rw [(distribute_arith Y H s n (mirror K a z f*f') f  (Reflect.chord _)).2.2.1, (distribute_arith Y H s n (mirror K a z f) f' 0).2.1,(distribute_arith Y H s n f f 0).2.2.2.2]
local notation "S'"=> reflectedBox a z S
local notation "S₀"=> reflectedBox a z₀ (W S) ∪ W S
include t
lemma consumes (x:InTest K true S g₀ f)(y:InTest K true S g₀ g)(a₀:InTest K true Z false (poleForm K a z g₀ f g))
    (v:∀ i∈Satin.region (S') (Mx s),∀ j∈Satin.region S (Mx s), Cr < separation i j)(d₁:Tivoli (W S) (Mx (s+1)))(d₂:Tivoli (W Z) (Mx (s+1)))(d₃:Tivoli ((W Z)∪S₀) (Mx (s+1))):
    block Y H s n k' Z (poleForm K a z g₀ f g) = poleForm K a z₀ g₀ (pick Y H s n k' g₀ S f) (pick Y H s n k' g₀ S g):=by
 obtain ⟨A₁,P₁⟩:=lamp_jump Y H s n k' t x d₁; obtain ⟨A₂,P₂⟩:=lamp_jump Y H s n k' t y d₁
 apply stationary_ext Y H (s+1) ((W Z)∪S₀) n d₃.hosp ((Tower.booked _ _ _ _ _ Z _).mono subset_union_left) ((NorthTapes.statement a z₀ A₁ A₂).mono subset_union_right)
 rw [reserved Y H s _ _ _ t a₀ d₂, pole_right Y H (s+1) n a,P₁,P₂]; unfold poleForm; rw [above_scale, beam_sep Y H s n k' t (axial K a z x) y v, beam_reflect Y H s n k' t a z x]
-- d₃ etc purchasable even when only given p
end pier
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.consumes
