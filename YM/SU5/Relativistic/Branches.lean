import YM.SU5.Relativistic.FermiConvergence
import YM.SU5.Relativistic.Wade
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ} (Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (s:ℕ)(S:Finset Cover)
local notation "W"=>wingspan Λ l

local notation "M" r:max S:max b':max => moveUp Y H s (i (a r)) (k (b r)) S b'
local notation "L₀"=> Λ.R.L.val
local notation "I₁"=>i∘a
local notation "K₁"=>k∘b

abbrev Bedside (s:ℕ)(b':Bool)(S:Finset Cover) (m:Side)(u:ℕ→ℕ) : Prop:= (∃ C:ℝ,0 < C∧∀ᶠ n in atTop,∀ (x:Rough b' (tent Y H) S×Fields ((tent Y H).c m)), ‖moveUp Y H s (i (a (u n))) (k (b (u n))) S b' x.1.val m x.2‖ ≤ C) ∧ SeenAll (fun (n:ℕ) (x:Rough b' (tent Y H) S×Fields ((tent Y H).c m))=> moveUp Y H s (i (a (u n))) (k (b (u n))) S b' x.1.val m x.2)

local notation "D₀"=> Bedside Y H (i:=i) (a:=a) (k:=k) (b:=b)
lemma anotherPage (s:ℕ)(d:Bool)(S: Finset Cover)(m:Side) {u y x:ℕ→ℕ}(p:Tendsto y atTop atTop)(t:x=ᶠ[atTop] u ∘ y)(h:D₀ s d S m u) : D₀ s d S m x:= by
 obtain ⟨⟨c,v,A⟩,D,h⟩:=h
 refine ⟨⟨c,v,?_⟩,D,fun e z=>?_⟩
 · filter_upwards [p.eventually A,t] with n a q x; rw [q]; exact a x
 filter_upwards [p.eventually (h _ z),t] with n K' g x'; show ‖moveUp Y H _ _ _ _ _ _ _ _ - D x'‖≤_; rw [g]; exact K' _

include V Q
lemma evenPocket (S:Finset Cover) (m: Side)(s:ℕ) (u:ℕ→ℕ)(p:Tendsto u atTop atTop) : D₀ s false S m u:=by
 have grow:Tendsto (fun n:ℕ=>i (a (u n))) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp (Q.growsA.tendsto_atTop.comp p)
 obtain ⟨C,p',q⟩:=Q.implements s S
 let O:= Rough false (tent Y H) S×Fields ((tent Y H).c m)
 let Z':O→Family (tent Y H):=fun x=>D s x.1.val
 refine ⟨⟨C,p',?_⟩,(fun x:O=> Z' x m x.2),fun e v=>?_⟩
 · filter_upwards [p.eventually (q _ zero_lt_one),grow.eventually (turning Y H (s+1) (W S)),p.eventually (Q.finance (s+1))] with i u w v x
   rw [base_even Y H s _ _ S ⟨v.depth,v.enters⟩ x.1.property.1 w]; exact ((u _ x.1.property.1 1 x.1.property.2).2.1 m x.2).trans_eq (mul_one C)
 filter_upwards [p.eventually (q e v),grow.eventually (turning Y H (s+1) (W S)),p.eventually (Q.finance (s+1))] with n u w v x
 change ‖moveUp Y H s _ _ S false x.1.val _ _ - D s x.1.val m x.2‖ ≤ _; rw [base_even Y H s _ _ S ⟨v.depth,v.enters⟩ x.1.property.1 w]; exact ((u _ x.1.property.1 1 x.1.property.2).2.2.1 m x.2).trans_eq (mul_one e)

lemma allStepColors : ∃ u:ℕ→ℕ, StrictMono u∧ ∀ s:ℕ,∀ (S:Finset Cover),∃ m:Side, Tivoli (wingspan Λ l S) ((tent Y H).c m) ∧ ∀ d: Bool, Bedside Y H (i:=i) (k:=k) (a:=a) (b:=b) s d S m u:=by
 let P (x:ℕ × Finset Cover) (u:ℕ→ℕ):Prop:=∃ m:Side,Tivoli (W x.2) ((tent Y H).c m)∧D₀ x.1 true x.2 m u
 suffices t:∃ u:ℕ→ℕ,StrictMono u∧∀ x,P x u by
    obtain ⟨u,h,v⟩:= t
    refine ⟨u,h,fun s S=>?_⟩
    obtain ⟨m,h',q⟩:= v (s,S); exact ⟨m,h',fun d=>by cases d; exact evenPocket Y H V Q S m s u h.tendsto_atTop; exact q⟩
 refine threadSequence (P:=P) ?_ ?_
 · rintro ⟨s,S⟩ u h; obtain ⟨z,hz,g⟩:= airing (Λ:=Λ) (l:=l) S (0:Axis)
   obtain ⟨n,t,v⟩:= ((turning Y H s (reflectedBox 0 ((L₀:ℤ)*z) (W S) ∪ W S)).and (turning Y H s (W S))).exists
   let m:= momentm Y n s
   obtain ⟨C,p,u',w,l,q⟩:=portRoot Y H V Q s S 0 z hz g m (t.hosp) h.tendsto_atTop; exact ⟨w,l,m,v,⟨C,p,l.tendsto_atTop.eventually u'⟩,q⟩
 rintro ⟨s,S⟩ u f g p v ⟨m,w,h⟩; exact ⟨m,w,anotherPage Y H s true S m p v h⟩ -- arg order

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
