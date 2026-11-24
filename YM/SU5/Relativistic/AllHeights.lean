import YM.SU5.Relativistic.StepOpinions
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

variable (s:ℕ)

local notation "Bp" => Baring (i:=i) (a:=a) (k:=k) (b:=b) Y H u
structure GradesAll (T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)) : Prop where
 thins:StrictMono u
 links (S:Finset Cover)(s:ℕ)(v:Bool): ∃ c,Baring (i:=i) (k:=k) (a:=a) (b:=b) Y H u s S v (T s v) c

include V Q
lemma grades_at : ∃ (u:ℕ→ℕ)(T:ℕ→Bool→Family (tent Y H) →Family (tent Y H)), GradesAll (i:=i) (a:=a) (k:=k) (b:=b) Y H u T:=by
 obtain ⟨u,p,h⟩:= allStepColors Y H V Q
 have hv(s:ℕ)(v:Bool)(S:Finset Cover): ∃ c F,Baring (i:=i) (a:=a) (k:=k) (b:=b) Y H u s S v F c:=by
    obtain ⟨m,e,x⟩:= h s S; obtain ⟨c,F,p',g,q⟩:= uniformBand Y H V Q u p s (b':=v) ⟨m,e,x _⟩
    exact ⟨c,F,p',fun x t=>(g x t).1,fun x t=>(g x t).2,q⟩
 choose c F g using hv
 let T (s:ℕ)(v:Bool)(x:Family K): Family (tent Y H):= if t:∃ S: Finset Cover,InTest K true S v x then F s v t.choose x else 0
 have ht {s:ℕ}{v:Bool}{S:Finset Cover}{x:Family (tent Y H)}(z:InTest K true S v x) : T s v x=F s v S x:=by
    let p0:∃ S:Finset Cover, InTest K true S v x:=⟨S,z⟩; let U:=p0.choose∪S
    unfold T; rw [dif_pos p0]
    exact (Baring.across_support Y H V Q u p (g ..) p0.choose_spec (g s v U) subset_union_left).trans (Baring.across_support Y H V Q u p (g ..) z (g s v U) subset_union_right).symm
 refine ⟨u,T,p,?_⟩; intro S s v; let h:=g s v S; refine ⟨c s v S,h.pos,fun x w=>by rw [ht w]; exact h.tags x w,fun x w y t=>by rw [ht w]; exact h.bdd x w y t,fun e p=> (h.converges e p).mono ?_⟩
 intro i v x t y g; rw [ht t]; exact v x t y g

variable {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=i) (a:=a) (k:=k) (b:=b) Y H u T)
variable {S:Finset Cover}{v:Bool}{x:Family (tent Y H)}
namespace GradesAll
include t
omit V Q
lemma pays (z:InTest K true S v x): InTest K true (wingspan Λ l S) v (T s v x):= (t.links S s v).choose_spec.tags x z
include V Q
variable {y:Family (tent Y H)}(z:InTest (tent Y H) true S v x)
include z
lemma addL (p:InTest K true S v y): T s v (x+y)=T s v x+T s v y:= Baring.plusStep Y H V Q u t.thins (t.links ..).choose_spec z p
lemma scaleL (c:ℂ): T s v (c • x)=c • T s v x:=Baring.scaleStep Y H V Q u t.thins (t.links ..).choose_spec z c
open Tapestry
lemma post (u':InTest K true S v y)(c:Cover→SU.E) (e:Circular S (parentGauge Λ c) x y): Circular (wingspan Λ l S) c (T s v x) (T s v y):=Baring.transCover Y H V Q u t.thins (t.links ..).choose_spec z u' c e
lemma bless (h:CovCover K x): CovCover K (T s v x):= (harmonicHere (S:=wingspan Λ l S)).2 (fun c=> t.post Y H V Q u s z z c ((harmonicHere (S:=S)).1 h _)) -- args
lemma lay (j:Axis)(a:ℤ): T s v (mirror K j a x)=mirror K j (Λ.R.L.val*a) (T s v x):= Baring.across_step Y H V Q u t.thins (t.links S s v).choose_spec z j a (t.links ..).choose_spec
lemma sealPair {W₀:Finset Cover}{d:Bool}(u':InTest K true W₀ d y)(p:Detached Λ l S W₀) : T s (v.xor d) (x*y)=T s v x * T s d y:=Baring.detachedMul Y H V Q u t.thins (t.links ..).choose_spec z p (t.links ..).choose_spec (t.links ..).choose_spec u'
omit z
lemma formerly {x: Family K}(h:TestFamily K true x): T s false x=D s x:=by obtain ⟨s',p⟩:=h.paid; exact Baring.preserves Y H V Q u t.thins (t.links s' s false).choose_spec p
lemma wagesUnit:T s false 1=1:= (t.formerly Y H V Q u s TestFamily.oneT).trans (Q.circuit.unit s)
end GradesAll

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
