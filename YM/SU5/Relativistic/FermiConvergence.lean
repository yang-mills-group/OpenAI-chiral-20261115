import YM.SU5.Relativistic.PolarRoot
import YM.SU5.Relativistic.AirTwo

/-! # Normalizing the limiting odd lift tensor norm, at operator estimate level. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
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
abbrev Rough (b:Bool)(K':Calibration)(S:Finset Cover) := {f:Family K' // InTest K' true S b f∧ pay f 1}
variable (j:Axis)(z:ℤ) (p: Detached Λ l (reflectedBox j z S) S) (t: Detached Λ l (reflectedBox j ((Λ.R.L.val)*z) (wingspan Λ l S)) (wingspan Λ l S))
local notation "S'"=> reflectedBox j z S
local notation "L₁"=> (Λ.R.L.val * z:ℤ)
local notation "Y'"=>reflectedBox j (L₁) (W S)
local notation "M" r:max=>moveUp Y H s (i (a r)) (k (b r)) S true
local notation "Pt"=> Rough true (tent Y H) S


include p Q V t
lemma truer (m:Side)(hp:Hosp (Y'∪W S) ((K).c m)) {u : ℕ→ℕ}(lt:Tendsto u atTop atTop):
 let A:=Pt × Fields ((K).c m); let J:=Satin.region (Y') ((K).c m); let T:= Satin.region (W S) ((K).c m); let L(A:A):=mirror K j z A.1.val; let B(A:A):=A.1.val
 let τ'(A:A):=reflFields j (L₁) A.2; let c'(A:A×A):Fields ((K).c m):= setTwo J (τ' A.1) A.2.2
 let Y₁(A:A×A):= L A.1 * B A.2
 let X(n:ℕ)(a:A):= (M (u n)) (B a)
 let C (n:ℕ) (a:A) := X n a m a.2
 let E₀(n:ℕ) (a:A) := mirror K j (L₁) (X n a) m (τ' a)
 let Φ(x:A×A):= D s (Y₁ x) m (c' x)
 Jars (fun n (x:A×A)=> E₀ n x.1*C n x.2) Φ ∧ ∃ K0:ℝ,∀ x, ‖Φ x‖≤ K0:=by
 intro A J T L B tau c' Y₁ X C E₀ Φ
 obtain ⟨tq,eq⟩:= sectorsDis («K»:=(tent Y H)) (n:=m) (Tower.Selected.detached_disjoint t) hp
 have h(a:A): InTest K true (S') true (L a):= axial K j z a.1.property.1
 let U:= S' ∪ S
 have hz(A:A×A): InTest K true U false (Y₁ A):= ((h A.1).mono subset_union_left).mul (A.2.1.property.1.mono subset_union_right)
 have hZ (x:A×A): pay (Y₁ x) 1:= by intro r τ₀; exact (pay_mul (pay_flips K x.1.1.property.2 j z) x.2.1.property.2 r τ₀).trans_eq (mul_one _)
 obtain ⟨r,y,q⟩:=Q.implements s U
 have grow:Tendsto (fun n:ℕ=>i (a (u n))) atTop atTop:= V.pick.grow_i.tendsto_atTop.comp (Q.growsA.tendsto_atTop.comp lt)
 have hi:Jars (fun n (x:A×A)=> E₀ n x.1*C n x.2) Φ:=by
    intro e v; filter_upwards [lt.eventually (q e v),lt.eventually (Q.finance (s+1)),grow.eventually (eventually_host Y H s U),grow.eventually (festive Y H s S (b:=true) j z)] with n T₁ T₂ T₃ W' x
    let o:=i (a (u n)); let l':=k (b (u n)); have ht:legalAt Y s o l':=⟨T₂.depth,T₂.enters⟩ -- defeq
    have hw (v:A): moveUp Y H s o l' (S') true (L v)=mirror K j (L₁) (X n v):=W' _ ht _ v.1.property.1
    have he: block Y H s o l' U (Y₁ x) = mirror K j (L₁) (X n x.1)*X n x.2 := (base_even Y H s o l' U ht (hz x) (T₃.usable 1)).symm.trans ((together Y H s o l' (S') p T₃ ht (h x.1) x.2.1.property.1).trans (congrArg (fun (F:Family K)=>F * X n x.2) (hw x.1)))
    have h': E₀ n x.1*C n x.2 = block Y H s o l' U (Y₁ x) m (c' x):= by rw [he]; symm; exact seamTwo true true tq ((axial K j _ (stay Y H s o l' S (B x.1) true)).support m) ((stay Y H s o l' S (B x.2) true).support m) (tau x.1) x.2.2
    rw [h']; exact ((T₁ _ (hz x) 1 (hZ x)).2.2.1 m (c' x)).trans_eq (mul_one e)
 have hP: ∃ K0:ℝ,∀ x, ‖Φ x‖≤ K0:=by
    obtain ⟨n,w⟩:=(q _ zero_lt_one).exists; exact ⟨r,fun x=>( (w _ (hz x) 1 (hZ x)).1 m (c' x)).trans_eq (mul_one r)⟩
 exact ⟨hi,hP⟩

lemma portRoot (m:Side)(hp:Hosp (Y'∪W S) ((K).c m)) {u : ℕ→ℕ}(lt:Tendsto u atTop atTop):
 ∃ C:ℝ,0<C ∧ (∀ᶠ n in atTop,∀ (x:Rough true (tent Y H) S×Fields ((tent Y H).c m)),‖(M (u n)) x.1.val m x.2‖ ≤ C) ∧
 ∃ w:ℕ→ℕ,StrictMono w ∧ SeenAll (fun (n:ℕ)(x:Rough true (tent Y H) S×Fields ((tent Y H).c m))=> (M (u (w n))) x.1.val m x.2) :=by
 let A:=Pt × Fields ((K).c m); let J:=Satin.region (Y') ((K).c m); let T:= Satin.region (W S) ((K).c m); let L(A:A):=mirror K j z A.1.val; let B(A:A):=A.1.val
 let τ'(A:A):=reflFields j (L₁) A.2; let c'(A:A×A):Fields ((K).c m):= setTwo J (τ' A.1) A.2.2
 let Y₁(A:A×A):= L A.1 * B A.2
 let X(n:ℕ)(a:A):= (M (u n)) (B a)
 let C (n:ℕ) (a:A) := X n a m a.2
 let E₀(n:ℕ) (a:A) := mirror K j (L₁) (X n a) m (τ' a)
 let Φ(x:A×A):= D s (Y₁ x) m (c' x)
 obtain ⟨tq,eq⟩:= sectorsDis («K»:=(tent Y H)) (n:=m) (Tower.Selected.detached_disjoint t) hp
 have ht(n a): InTest K true (W S) true (X n a):= stay ..
 have he(n a):InTest K true (Y') true (mirror K j (L₁) (X n a)):= axial K j _ (ht n a)
 have h₁(n:ℕ)(a:A): Sector (modesIn ((K).c m) J) true (E₀ n a):= (( (he n a).support m).allV _).sector
 have h₂(n:ℕ)(a:A): Sector (modesIn ((K).c m) T) true (C n a):= (((ht n a).support m).allV _).sector
 have hu (w) x : ‖E₀ w x‖=‖C w x‖:=normaM j (L₁) («K»:=tent Y H) (f:=X w x) m x.2
 have h0 : Jars (fun n (x:A×A)=> E₀ n x.1*C n x.2) Φ ∧ ∃ K0:ℝ,∀ x, ‖Φ x‖≤ K0:= truer Y H V Q s S j z p t m hp lt
 obtain ⟨hi,hP⟩:= h0
 obtain ⟨n₀,v',q⟩:= sponsor (R:=C) (D:=Φ) (Q:=E₀) eq h₁ h₂ hu hi hP
 obtain ⟨w,h,t⟩:= flock (R:=C) (D:=Φ) (Q:=E₀) eq h₁ h₂ hu hi hP
 refine ⟨n₀,v',?_,w,h,?_⟩
 · exact q
 exact t
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.portRoot
