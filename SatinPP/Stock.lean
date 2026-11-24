import SatinThinCanvas

/-!
Mesh-slab operations, represented at all later readings. Same heat units as
the experiments (realWidth = a number of s-ticks × mill s).
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
variable {n w:ℕ}
local notation "X"=> P.ColorHil j x
local notation "W"=> P.calibration
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L.val
local notation "Q" n:max s:max =>(P.par.R.L.val^(s-n))
local notation "Φ"=> P.colorSpace j x
local notation "μ"=> P.birthF j
local notation "ν"=> P.viewF j x
local notation "S"=>P.shifts j
local notation "T"=>timeMesh P.par
local notation "E"=> (P.physicalEnergy j x).E

def Acts (s w:ℕ)(f:P.Test)(A:(P.ColorHil j x).Op) := 
 ∀ z:P.Test,∀ h:μ s z, ∃ p:μ s (f * S (w:ℤ) z), ν s p=A (ν s h)

def Stock (n w:ℕ)(f:P.Test)(A:(P.ColorHil j x).Op):Prop:= 
 ∀ s:ℕ,n ≤ s → P.Acts j x s (Q n s * w) (P.conveying n (s-n) f) A

lemma stock_unique {f:P.Test}{A B:(P.ColorHil j x).Op}
 (a:P.Stock j x n w f A)(b:P.Stock j x n w f B): A=B:=by
 apply ContinuousLinearMap.ext_on (P.native_dense j x)
 intro y h
 obtain ⟨s,h⟩:=Set.mem_iUnion.mp h; obtain ⟨g,rfl⟩:=h
 let u:=max n s; let z:=P.voxTest j s g.val; have d:μ s z:=⟨g,rfl⟩
 rw [← P.holdsF j x s d g rfl, ←P.view_rig j x s u d (le_max_right ..)]
 exact (a u (le_max_left ..) _ (P.rig j s u d (le_max_right ..))).choose_spec.symm.trans ((b u (le_max_left ..) _ _).choose_spec) -- Prop irrelevance; underscore issue

private lemma carry_1 (n s:ℕ):P.conveying n s 1=1:=
 Subtype.ext (woven_one P.run P.large P.history.circuit ..)
lemma carry_add (n s:ℕ)(f g:P.Test):P.conveying n s (f+g)=P.conveying n s f+P.conveying n s g :=
 Subtype.ext (woven_add P.run P.large P.history.circuit _ _ ((marque ..).mp f.property) ((marque ..).mp g.property))
lemma carry_smul (n s:ℕ)(r:ℂ)(f:P.Test):P.conveying n s (r • f)=r • P.conveying n s f:=
 Subtype.ext (woven_smul P.run P.large P.history.circuit _ _ ((marque ..).mp f.property) r)
def carries (n s:ℕ) : P.Test→ₗ[ℂ]P.Test where
 toFun:=P.conveying n s
 map_add':=P.carry_add n s
 map_smul':=P.carry_smul n s



lemma issue_eq {s:ℕ}{V:(P.ColorHil j x).space}{f g:P.Test} (t:f=g)
 (p:μ s g)(e:ν s p=V): ∃ q:μ s f, ν s q=V:=t.symm ▸ (show ∃ q:μ s g, ν s q=V from ⟨p,e⟩)
variable {P j x}
variable {B:(P.ColorHil j x).Op}
variable {g:P.Test}

lemma Stock.smul (a:P.Stock j x n w g B)(c:ℂ):
    P.Stock j x n w (c • g) (c • B):=by
 intro s v z h
 obtain ⟨p,H⟩:=a s v z h
 refine P.issue_eq j x ?_ (P.birthScaleJ j s c p) ((P.viewJ_scale j x s c p).trans (congrArg (c • ·) H))
 rw [P.carry_smul, smul_mul_assoc]

lemma stock_door (e:0<w)(f:P.Card j n w)(u:P.voxTest j n f.val∈enclave W): 
    P.Stock j x n w (P.voxTest j n f.val) (Φ (P.door j n w e f u)):=by
 intro s hs z h
 let v:=Q n s*w; let d:P.Card j s v:=furnished P.run P.large n P.history j false w f s hs
 have he:0<v:=Nat.mul_pos (pow_pos P.par.R.L.property _) e
 have hy:P.voxTest j s d.val∈enclave W:=P.refine_keeps _ _ u _
 obtain ⟨p,H⟩:=P.accepted_view j x s v he d hy h 
 refine ⟨p,H.symm.trans ?_⟩
 rw [show P.door j s v he d hy=P.door j n w e f u from Subtype.ext (P.upper_tab j _ _ _ _ _ _).symm]



lemma stock_sum {ι:Type} {f:ι→P.Test}{M:ι→(P.ColorHil j x).Op}(I:Finset ι)
 (v:∀ i∈ I,P.Stock j x n w (f i) (M i)):
    P.Stock j x n w (∑ i∈ I,f i) (∑ i∈ I,M i):=by
 intro s t z h
 classical
 let L₁:=P.carries n (s-n); let Z:=S ((↑(Q n s*w:ℕ)):ℤ) z
 have a:P.conveying n (s-n) (∑ i∈ I,f i)*Z=∑ i∈ I, L₁ (f i)*Z:=calc
   _= (∑ i∈ I,L₁ (f i))*Z := congrArg (·*Z) (map_sum L₁ f I)
   _=_:= Finset.sum_mul ..
 obtain ⟨q,K⟩:=P.birthSumJ j x s I (fun i=> L₁ (f i)*Z) (fun i=> M i (ν s h)) (fun i e=>v i e s t z h)
 exact P.issue_eq j x a q (K.trans (ContinuousLinearMap.sum_apply ..).symm)



lemma Stock.plus {f:P.Test}{A:(P.ColorHil j x).Op}(p:P.Stock j x n w f A)(u:P.Stock j x n w g B):
    P.Stock j x n w (f+g) (A+B):=by
 intro t h i q
 obtain ⟨a,e⟩:=p t h i q; obtain ⟨b,d⟩:=u t h i q
 exact P.issue_eq j x (by rw [P.carry_add,add_mul]) (P.birthAddJ j t a b)
   ((P.viewJ_plus j x t a b).trans (by rw [e,d]; rfl))

variable (P)
lemma when_eq (s t r:ℕ)(h:s≤t) :
    whenly T t (Q s t*r)=whenly T s r:=by
 apply NNReal.eq
 refine (natural_time T t _).symm.trans (Eq.trans ?_ (natural_time T s r))
 have e:=congrArg (fun v:marks T=>(v:ℝ)) (notch_up T s t h (r:ℤ))
 push_cast; exact e

variable (j x)
lemma stock_one (n w:ℕ):
    P.Stock j x n w 1 (E (whenly T n w)):=by
 intro t h i q
 refine P.issue_eq j x ?_ (P.passesLater j t (Q n t*w) q)
    ((P.releasedLater j x t _ q).trans (by rw [P.when_eq n t w h]))
 rw [P.carry_1,one_mul]




variable {P j x}
lemma Stock.attach (d:P.Stock j x n w g B)(a b:ℕ):
    P.Stock j x n (a+w+b) (S a g) (E (whenly T n a) * B * E (whenly T n b)):=by
 intro t h i q
 let N:= Q n t
 let Z:=P.passesLater j t (N*b) q
 obtain ⟨α,v⟩:=d t h _ Z
 let P':=P.passesLater j t (N*a) α
 refine P.issue_eq j x ?_ P' ((P.releasedLater j x t _ α).trans ?_)
 · rw [P.walk_rig, map_mul,P.shifts_sum,P.shifts_sum]
   dsimp [MeshClock.castor,N]
   push_cast
   rw [mul_add,mul_add]; try rfl -- tune
 change _= E (whenly T n a) (B (E (whenly T n b) (ν t q)))
 rw [v]
 unfold Z; rw [P.releasedLater j x t _ q]; simp only [N,P.when_eq n t _ h]



end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
