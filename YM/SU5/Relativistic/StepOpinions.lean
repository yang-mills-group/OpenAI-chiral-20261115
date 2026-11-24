import YM.SU5.Relativistic.GaugeBand
import YM.SU5.Relativistic.ColorGrade
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
local notation "W"=>wingspan Λ l

variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(u:ℕ→ℕ)(p: StrictMono u)
local notation "A" r:max=>i (a (u r))
local notation "B" r:max=>k (b (u r))
local notation "L₁" r:max s:max S:max b':max => moveUp Y H s (i (a (u r))) (k (b (u r))) S b'
local notation "Σ₀"=>Bedside Y H (i:=i) (k:=k) (a:=a) (b:=b)


include V Q p
lemma paidStep (s:ℕ)(S:Finset Cover):∀ᶠ r in atTop,legalAt Y s (A r) (B r) ∧ Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y (A r) (s+1))):=(p.tendsto_atTop.eventually (Q.finance (s+1))).mono (fun i h=> ⟨h.depth,h.enters⟩) |>.and ((V.pick.grow_i.tendsto_atTop.comp (Q.growsA.tendsto_atTop.comp p.tendsto_atTop)).eventually (turning Y H (s+1) (W S)))
omit V Q p
structure Baring (s:ℕ)(S:Finset Cover)(b':Bool)(F:Family (tent Y H)→Family (tent Y H)) (c:ℝ):Prop where
 pos : 0<c
 tags (x:Family (tent Y H)) (h:InTest K true S b' x):InTest K true (wingspan Λ l S) b' (F x)
 bdd (x:Family (tent Y H)) (h:InTest K true S b' x) (y:ℝ)(t:pay x y): pay (F x) (c*y)
 converges (e:ℝ)(p:0<e): ∀ᶠ j:ℕ in atTop,∀ x,InTest K true S b' x→∀ y:ℝ,pay x y→pay ((L₁ j s S b') x) (c*y)∧pay ((L₁ j s S b') x-F x) (e*y)
local notation "Bp"=> Baring (i:=i) (a:=a) (k:=k) (b:=b) Y H u
namespace Baring
variable {s:ℕ} {S:Finset Cover} {b':Bool}{F F': Family (tent Y H)→Family (tent Y H)}{c c':ℝ}
variable (h:Baring (i:=i) (a:=a) (k:=k) (b:=b) Y H u s S b' F c){x y:Family (tent Y H)}(t:InTest (tent Y H) true S b' x)
include h t
lemma costs_gone (e:ℝ)(p:0<e):∀ᶠ r in atTop,pay ((L₁ r s S b') x-F x) e:=by
 obtain ⟨g,a₀⟩:= Journey.valuation Y H t; let b:= max 1 g; have hv:0<b:=lt_max_of_lt_left zero_lt_one; refine (h.converges _ (div_pos p hv)).mono fun i r j k=> ((r x t b (fun i j=>(a₀ ..).trans (le_max_right ..))).2 j k).trans_eq (div_mul_cancel₀ e hv.ne')
lemma personally (m:Side)(z:Fields ((tent Y H).c m)): Tendsto (fun r=>((L₁ r s S b') x) m z) atTop (𝓝 (F x m z)):= by
 refine Metric.tendsto_nhds.mpr fun e p=>?_
 filter_upwards [costs_gone Y H u h t _ (half_pos p)] with i k; rw [dist_eq_norm]; exact (k m z).trans_lt (half_lt_self p)
include V Q p
lemma across_support {T:Finset Cover}(f:Bp s T b' F' c')(v:S ⊆ T) : F x=F' x := by
 funext m z; apply tendsto_nhds_unique_of_eventuallyEq (personally Y H u h t m z) (personally Y H u f (t.mono v) m z)
 filter_upwards [paidStep Y H V Q u p s S,paidStep Y H V Q u p s T] with r a b
 exact congrFun (congrFun ((glued Y H s _ _ a.1 a.2 t v b.2).symm) _) _
lemma plusStep (v:InTest (tent Y H) true S b' y) : F (x+y) = F x+ F y:=by
 funext m z; apply tendsto_nhds_unique_of_eventuallyEq (personally Y H u h (t.add v) m z) ((personally Y H u h t m z).add (personally Y H u h v m z)); exact (paidStep Y H V Q u p s S).mono fun i d=>congrFun (congrFun (addMove Y H s _ _ d.1 d.2 t v) m) z
lemma scaleStep (w:ℂ): F (w • x)=w • F x:=by
 funext m z; apply tendsto_nhds_unique_of_eventuallyEq (personally Y H u h (InTest.smul w t) m z) ((personally Y H u h t m z).const_smul w); exact (paidStep Y H V Q u p s S).mono fun i d=> congrFun (congrFun (scaleMove Y H s _ _ d.1 d.2 t w) _) _
open Tapestry
lemma transCover (e:InTest (tent Y H) true S b' y)(a':Cover→SU.E)(v:Circular S (parentGauge Λ a') x y) : Circular (wingspan Λ l S) a' (F x) (F y):=by
 intro i A₀ z t'
 apply tendsto_nhds_unique_of_eventuallyEq (personally Y H u h t i (simultaneous A₀ t')) ((breeze _).continuousAt.tendsto.comp (personally Y H u h e i t'))
 exact (paidStep Y H V Q u p s S).mono fun r h=>splash Y H s _ _ S h.1 h.2 t e a' v _ A₀ z t'
lemma across_step (a:Axis)(z:ℤ)(f:Bp s (reflectedBox a z S) b' F' c') : F' (mirror K a z x)=mirror K a (Λ.R.L.val*z) (F x):=by
 funext m u'
 apply tendsto_nhds_unique_of_eventuallyEq (personally Y H u f (axial _ _ _ t) m u') ((Fock.theta_cont _).continuousAt.tendsto.comp (personally Y H u h t m (reflFields a (Λ.R.L.val*z) u')))
 filter_upwards [((V.pick.grow_i.tendsto_atTop.comp (Q.growsA.tendsto_atTop.comp p.tendsto_atTop)).eventually (festive Y H s S (b:=b') a z)),paidStep Y H V Q u p s S] with i a o
 exact congrFun (congrFun (a _ o.1 x t) _) _
lemma detachedMul {T}{F₀}{d:Bool}{c₀:ℝ}(a: Detached Λ l S T)(f:Bp s T d F' c') (g:Bp s (S∪T) (b'.xor d) F₀ c₀)(q:InTest K true T d y) : F₀ (x*y)= F x * F' y:=by
 funext m u'; apply tendsto_nhds_unique_of_eventuallyEq (personally Y H u g ((t.mono subset_union_left).mul (q.mono subset_union_right)) m u') ((personally Y H u h t m u').mul (personally Y H u f q m u'))
 filter_upwards [((V.pick.grow_i.tendsto_atTop.comp (Q.growsA.tendsto_atTop.comp p.tendsto_atTop)).eventually (eventually_host Y H s (S∪T))), paidStep Y H V Q u p s S] with r z b
 exact congrFun (congrFun (together Y H s _ _ S a z b.1 t q) _) _
omit h t
lemma preserves {s:ℕ}{S:Finset Cover} {F:Family K → Family K}{c:ℝ}(h:Bp s S false F c){x:Family K}(t:InTest K true S false x):F x=D s x:=by
 funext m n; obtain ⟨C,p',q⟩:=Q.implements s S
 apply tendsto_nhds_unique (personally Y H u h t m n); obtain ⟨Y₀,e⟩:= Journey.valuation Y H t
 let C':= max 1 Y₀; have hc:0<C':=lt_max_of_lt_left zero_lt_one
 refine Metric.tendsto_nhds.mpr fun ε g=>?_
 filter_upwards [p.tendsto_atTop.eventually (q _ (show 0<ε/2/C' from by positivity)),paidStep Y H V Q u p s S] with i z k
 rw [base_even Y H s _ _ S k.1 t k.2,dist_eq_norm]; exact ((z _ t C' (fun i j=>(e ..).trans (le_max_right ..))).2.2.1 m n).trans_lt ((div_mul_cancel₀ (ε/2) hc.ne').trans_lt (half_lt_self g))
end Baring

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
