import GaugeFieldConstruction.Valle
import GaugeFieldConstruction.Canone
import GaugeFieldConstruction.Tropic
import GaugeFieldConstruction.Pliant
import GaugeFieldConstruction.Ethos
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open Fock
variable (P:Spine)
open MeasureTheory
open Afterglow -- tune
local notation "Ω"=>P.floorVec
-- Alternative Porch gives linear itself for all tests fit BEntry.B.Q. Thus prove for any p.H3 and shift stamp.
variable {P}
open Papal Papal.FrameP
open CF.XGarden CF.XGarden.MastTin ArtCart
open RG Fock CF.Rush Vale Branch Fock.Flux Tapestry
open YM.Gleam BProof.PricePort Gleam.Guide Gleam.clocks
open RG CF.Skye
open CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open scoped YM.CF.Mew
open CF.TableF TableF.Lenten TableF.Lenten.Layout Py
variable {P:Spine}{S:Finset Cover}{f:P.Test}{F:ℕ→Buffered.Family P.calibration}

/-- Const-pay raw Perse sector. All along actual P.study. -/
abbrev penIt (P:Spine)(s:ℕ): BudgetPoint:= Py.KeyUp (P.run.meter.a s)
abbrev MaleBook (P:Spine)(s n:ℕ):Tulip.Male:= (Papal.gram P.run s (P.gatePeriod n) (P.gateCut n)).J.M
abbrev betaBook (P:Spine)(s n:ℕ):ℝ:= (Papal.gram P.run s (P.gatePeriod n) (P.gateCut n)).beta
lemma billStamp (P:Spine)(s:ℕ):(P.penIt s).order≤6∧ (P.penIt s).power ≤3:= ⟨(show (P.run.meter.a s).order=6 from (P.run.meter.boot s).2.2.2.2).le,le_rfl⟩
variable {x:Cover}{s:ℕ}
def Araw (P:Spine)(s:ℕ)(x:Cover)(n:ℕ): Waves →ₗ[ℂ] Buffered.Family P.calibration:=
  (Johnℓ (d:=24) x _ (P.penIt s).threshold).comp (bush_ℓ (P.MaleBook s n) x (h:=P.par.h) (zero_lt_one.trans_le P.par.height) (P.billStamp s).2 (P.billStamp s).1)
lemma leafA (P:Spine)(s:ℕ)(x:Cover)(v:Waves)(m:ℕ):∃ q:P.Test,q.val=(P.Araw s x m v) ∧ q∈enclave P.calibration ∧ InTest P.calibration true (cartO x 28) false q.val:=by
 obtain ⟨a,b,c⟩:= (ArtCart.root_T (P.MaleBook s m) P.par.height x (P.billStamp s).2 (P.billStamp s).1 v).2.1 P.calibration
 let q:P.Test:=⟨P.Araw s x m v, aux_test a⟩
 exact ⟨q,rfl,(enclave_spec ..).mpr c,a⟩
lemma Od_still(P:Spine)(x:Cover)(s:ℕ)(v:Waves) : Spectrix.Odious (Set.range fun m=>(P.Araw s x m) v):=
 Spectrix.Od_sub (fun _ p=> by obtain ⟨i,rfl⟩:=p; exact ⟨P.MaleBook s i,rfl⟩) (Od_RawΩ x P.calibration v P.par.h (P.penIt s) (zero_lt_one.trans_le P.par.height) (P.billStamp s).2 (P.billStamp s).1)
lemma projected_one (P:Spine)(x:Cover)(s:ℕ)(v:Waves) (a:Slow):∃ b:Slow, ∃ F:P.Test,P.LongQueue (cartO x 28) (fun i=> P.Araw s x ((a.more b).subSeq i) v) F ∧ F∈enclave P.calibration:=by
 let X:= Set.range fun m=>(P.Araw s x m) v; have hp(y)(k:y∈X):∃ q:P.Test,q.val=y ∧ q ∈bay P.calibration (cartO x 28) true ∧ q∈enclave P.calibration:=by
    obtain ⟨n,rfl⟩:=k; obtain ⟨q,p,t,f⟩:= P.leafA s x v n; exact ⟨q,p,(Tapestry.locates ..).mpr f,t⟩
 obtain ⟨t,V,K,f,g⟩:= keen_bay (P:=P) _ (Od_still ..) hp _ (fun i=> Set.mem_range_self (a.subSeq i)); exact ⟨⟨t,V⟩,K,f,g⟩
lemma sunsetϕ(P:Spine){a b:Slow}(p:a.Delayed b){v:Waves}{F:P.Test}(q:P.LongQueue (cartO x 28) (fun i=> P.Araw s x (a.subSeq i) v) F):P.LongQueue (cartO x 28) (fun i=> P.Araw s x (b.subSeq i) v) F:=by
 obtain ⟨A,g,e⟩:=q.bdd
 refine ⟨fun i=> ?_,q.landing,⟨A,g,e.1, p.iff_tail (fun i=> Tower.pay (P.Araw s x i v) A) e.2⟩,fun z r=> p.iff_tail (fun i=> Tower.pay (P.Araw s x i v - F.val) z) (q.saved z r)⟩
 obtain ⟨q,r,g,h⟩:=P.leafA s x v (b.subSeq i); exact r ▸ h
lemma beta_at(P:Spine) (s:ℕ)(a:Slow):∀ᶠ i:ℕ in atTop,P.betaBook s (a.subSeq i) ∈ Set.Icc (P.urnMark s/2) (2*(P.urnMark s)):=by
 filter_upwards [(P.Coheresγ a.subSeq a.step).finance s] with i h
 have ht:=Papal.prices_plot _ s (P.gatePeriod (a.subSeq i)) _ h.enters; exact ht.2.2.2.1 -- tune
lemma slowPurchase {S:Set ℂ} (V:ℕ → ℂ)(p:∀ᶠ n:ℕ in atTop,V n∈S)(q:IsSeqCompact S):∃ a:Slow,∃ z∈S,Tendsto (V∘a.subSeq) atTop (𝓝 z):=by
 obtain ⟨i,h⟩:= eventually_atTop.mp p; let Y (n:ℕ):=i+n
 obtain ⟨A,hA,t,p,b⟩:=q (x:=V∘Y) (fun i=> h _ (Nat.le_add_right ..))
 exact ⟨⟨Y∘t,(show StrictMono Y from fun _ _ w=> Nat.add_lt_add_left w _).comp p⟩,A,hA,b⟩ -- tune
lemma slowBeta (P:Spine)(s:ℕ)(A:Slow):∃ B:Slow,∃ z∈ Set.Icc (P.urnMark s/2) (2*(P.urnMark s)), Tendsto (P.betaBook s ∘ (A.more B).subSeq) atTop (𝓝 z):=by
 let Q:=P.betaBook s; let V:=Q∘ A.subSeq; let S:= Set.Icc (P.urnMark s / 2) (2*(P.urnMark s)); obtain ⟨i,h⟩:= eventually_atTop.mp (beta_at P s A)
 let X(n:ℕ):=i+n; obtain ⟨z,v,t,q,d⟩:=isCompact_Icc.isSeqCompact (x:=V ∘ X) (s:=S) (fun n=> h _ (Nat.le_add_right ..))
 refine ⟨⟨X∘t,(show StrictMono X from ?_).comp q⟩,z,v,d⟩; intro k l hx; exact Nat.add_lt_add_left hx _

structure Heritor (P:Spine) where
 path : Slow
 β : ℕ→ℝ
 crop : ∀ s, β s∈ Set.Icc (P.urnMark s/2) (2*(P.urnMark s))
 bill : ∀ s, Tendsto (P.betaBook s ∘ path.subSeq) atTop (𝓝 (β s))
 M : ℕ → Cover → (Waves→ₗ[ℂ]P.Test)
 earned : ∀ s x v, P.LongQueue (cartO x 28) (fun i=> P.Araw s x (path.subSeq i) v) (M s x v)
 active : ∀ s x v, M s x v∈enclave P.calibration
-- after arbitrary requested slow, still can require this. preserve path
lemma Heritage (P:Spine)(a:Slow) : ∃ A:P.Heritor,a.Delayed A.path:=by
 classical
 haveI := Module.Free.of_divisionRing ℂ Waves
 let I:= Fin (Module.finrank ℂ Waves); let F:=Module.finBasis ℂ Waves
 let R: (ℕ ⊕ (ℕ × Cover × I))→ Slow→ Prop:=fun V T=> match V with
    | .inl s=> ∃ z∈ Set.Icc (P.urnMark s/2) (2*(P.urnMark s)), Tendsto (P.betaBook s ∘ (a.more T).subSeq) atTop (𝓝 z)
    | .inr (s,x,i)=>∃ f:P.Test,P.LongQueue (cartO x 28) (fun j=>P.Araw s x ((a.more T).subSeq j) (F i)) f ∧ f∈enclave P.calibration
 have ht(i)(p:Slow): ∃ b:Slow,R i (p.more b):=by
    cases i with | inl s=> exact slowBeta P s (a.more p) | inr u=> exact P.projected_one u.2.1 u.1 (F u.2.2) (a.more p)
 have hA(i T)(hT:R i T)(V:Slow)(pV:T.Delayed V):R i V:=by
   have hv:(a.more T).Delayed (a.more V):=by filter_upwards [pV] with i h; obtain ⟨k,h⟩:=h; exact ⟨k,congrArg a.subSeq h⟩
   cases i with
   | inl s=> obtain ⟨z,w,v⟩:= hT; exact ⟨z,w, Filter.tendsto_def.mpr fun S q=> hv.iff_tail (fun v=> P.betaBook s v ∈ S) (v q)⟩ -- tune
   | inr i=> rcases i with ⟨s,x,i⟩; obtain ⟨f,k,g⟩:= hT; exact ⟨f,P.sunsetϕ hv k,g⟩
 obtain ⟨t,h⟩:=Slow.selectors R ht hA
 choose β hb hk using (fun i=> h (.inl i))
 choose M hM V using (fun s x i=> h (.inr (s,x,i)))
 let L(s:ℕ)(x:Cover):Waves→ₗ[ℂ]P.Test:= F.constr ℂ (M s x)
 have hf(s x z) : L s x z=∑ i:I,F.repr z i • M s x i:= F.constr_apply_fintype .. -- tune
 refine ⟨⟨a.more t,β,hb,hk,L,?_,?_⟩, a.more_delay t⟩
 · intro s x v; rw [hf s x v]
   let A(n):=P.Araw s x ((a.more t).subSeq n)
   have hx(n):A n v = ∑ i:I,F.repr v i • A n (F i):=by
      nth_rw 1 [← F.sum_repr v]; rw [map_sum]; exact Finset.sum_congr rfl fun _ _=>map_smul ..
   change P.LongQueue _ (fun i=> A i v) _; simp_rw [hx]
   refine cash_L (P:=P) Finset.univ _ _ ?_ -- tune
   intro i _; exact (hM s x i).step (tendsto_const_nhds)
 intro s x z; rw [hf]; exact Subalgebra.sum_mem _ (fun i _=> (enclave P.calibration).smul_mem (V s x i) _)

variable {R:P.Heritor}
def Heritor.long (R:P.Heritor)(t:Slow): P.Heritor where
 path:=R.path.more t
 β:=R.β
 crop:=R.crop
 bill i:=(R.bill i).comp t.step.tendsto_atTop
 M:= R.M
 earned s x v:= LongQueue.mono t.step.tendsto_atTop (R.earned s x v)
 active:=R.active
#print axioms Heritage
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
