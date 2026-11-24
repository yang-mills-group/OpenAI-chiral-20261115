import YM.SU5.FiniteGaugeData.Tower.Recharge
import YM.SU5.Verified.Satin.GroundExtension
/-! Milk the phase elevator. One path includes all Rectangular charge specs per-height norm estimates.
Adapted proof from Recharge. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)
variable {q:ℕ→ℕ}(Q: CrimsonLine (i:=i) (k:=k) (I:=I) (E:=E) Y H q)
include V
private lemma belly(s n:ℕ){u:ℝ}(h:0<u):∀ᶠ j:ℕ in atTop,Ferry Y s n (k j)→∀(f:Family K)(t: TestFamily (tent Y H) true f)(a:ℝ)(_w:pay f a),‖sharp Y H s n (k j) f-hot Y H s n (k j) f‖≤u*a:=
 (V.pick.grow_k.tendsto_atTop.eventually (transfers Y H s u h)).mono fun _ M e f t a w=>by
    obtain ⟨S,r⟩:=t.paid
    have c:pay (1:Family K) 1:=fun i x=> (norm_one : ‖(1:Fock.FC (Single ((K).c i)))‖=(1:ℝ)).le
    simpa using M _ e S ∅ f 1 r InTest.one a 1 w c
include Q
lemma purchase_more (P:ℕ→ℕ→Prop) (p:∀i,∀ᶠ k in atTop,P i k) : ∃ (D:ℕ→Family (tent Y H)→Family (tent Y H))(a b:ℕ→ℕ),
    Coherent (i:=i) (k:=k) Y H (E:=E) D (q∘a) b ∧ StrictMono a ∧ Clipped Y H (i ∘q ∘a) (k∘b) ∧ ∀ i' :ℕ,P (i (q (a i'))) (k (b i')):=by
 -- choose column threshold paying all in fixed range (no cocycle inputs moved yet)
 have hp(x y:ℕ):∃ j≥ y+1,legacy Y ((i∘q) x) (k j)∧(∀s≤x,Ferry Y s ((i∘q) x) (k j) ∧ ∀(f:Family (tent Y H))(t:TestFamily K true f)(a:ℝ)(w:pay f a), ‖sharp Y H s ((i∘q) x) (k j) f-hot Y H s ((i∘q) x) (k j) f‖≤diet Y s ((i∘q) x)*a) ∧ P ((i∘q) x) (k j):=by
    let n:=(i∘q) x
    have he(s):=belly Y H V s n (Real.exp_pos (-((Journey.side Y n s).val:ℝ)^2))
    have hk:∀ᶠ j in atTop,legacy Y n (k j):= (Y.uv_grows.tendsto_atTop.comp V.pick.grow_k.tendsto_atTop).eventually_ge_atTop _
    obtain ⟨j,sH,e,t,u,v⟩:= ((V.pick.grow_k.tendsto_atTop.eventually (p n)).and ((eventually_ge_atTop (y+1)).and (hk.and (((eventually_all_finset (Iic x)).mpr (fun i w=>he i)).and ((eventually_all_finset (Iic x)).mpr (fun i w=> V.pick.pass Y H i n)))))).exists
    exact ⟨j,e,t,fun s p=>⟨v s (by simpa),u s (by simpa) (v s (by simpa))⟩,sH⟩
 choose p hp hq using hp
 let Z:=Nat.rec (motive:=fun _=>ℕ) (p 0 0) (fun r u=> p (r+1) u)
 have hh:StrictMono Z:=strictMono_nat_of_lt_succ (fun r=>hp ..)
 have ht (x:ℕ): legacy Y ((i∘q) x) (k (Z x))∧ (∀s≤x,Ferry Y s ((i∘q) x) (k (Z x)) ∧ ∀ (f:Family K)(_v:TestFamily K true f)(a:ℝ)(_w:pay f a), ‖sharp Y H s ((i∘q) x) (k (Z x)) f-hot Y H s ((i∘q) x) (k (Z x)) f‖≤ diet Y s ((i∘q) x)*a) ∧ P ((i∘q) x) (k (Z x)):=by cases x <;> exact hq ..
 have he (r:ℕ): ∀ᶠ x:ℕ in atTop,legalAt Y r ((i∘q) x) ((k∘ Z) x):= by
    filter_upwards [eventually_ge_atTop (r+1)] with x q
    exact ⟨((ht x).2.1 _ q).1.depth, ((ht x).2.1 _ q).1.enters⟩
 obtain ⟨a,t,v⟩:=perform Y H (i∘q) (k∘Z) (V.pick.grow_i.comp Q.grows|>.tendsto_atTop) he
 let P:PathLease Y H (i:=i) (k:=k) (q:=q) a (Z∘a):=⟨t,hh.comp t,fun j=>(ht (a j)).1,v⟩
 refine ⟨_,a,Z∘a,ethic Y H V a (Z∘a) Q P,t,(fun s=>?_),fun x=> (ht (a x)).2.2⟩
 exact (t.tendsto_atTop.eventually_ge_atTop s).mono fun r e f x k p=> ((ht _).2.1 s e).2 f x k p
open SatinVerification in
lemma grant_more (P:ℕ→ℕ→Prop)(p:∀i,∀ᶠ k in atTop,P i k): ∃ G: GroundExtension (i:=i) (k:=k) (E:=E) Y H,
    ∀ i':ℕ,P (i (G.rows i')) (k (G.columns i')):=by
 obtain ⟨D,a,b,e,h,p₀,T⟩:=purchase_more Y H V Q P p; exact ⟨⟨D,q∘a,b,e,p₀⟩,T⟩
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.grant_more
