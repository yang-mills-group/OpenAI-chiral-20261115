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
lemma Lantern_u (P:Spine)(S:Finset Cover):P.LongQueue S (fun _=>0) 0:=LongQueue.attain _ (zero_mem (bay P.calibration S true))
lemma cash_L {I:Type*}(D:Finset I)(A:I → ℕ → Buffered.Family P.calibration)(L:I → P.Test)
 (p:∀ i∈D,P.LongQueue S (A i) (L i)):P.LongQueue S (fun j=>∑ i∈D,A i j) (∑ i∈D,L i):=by
 classical
 induction D using Finset.induction with
 | empty=> simpa using Lantern_u P S
 | insert i D h ih=>simpa only [Finset.sum_insert h] using (p i (Finset.mem_insert_self ..)).plus (ih (fun i v=> p i (Finset.mem_insert_of_mem v)))

lemma LongQueue.sameField (p:P.LongQueue S F f){g:P.Test}(u:P.LongQueue S F g): f=g:=by
 apply Subtype.ext; funext m x; by_contra v; let V:=(f.val m x); let W:=g.val m x; let a:=dist V W/4; have hp:0<a:= div_pos (dist_pos.mpr v) (by norm_num)
 obtain ⟨t,h,k⟩:= ((p.saved _ hp).and (u.saved _ hp)).exists -- tune
 have hx:dist (F t m x) V≤a:=(by rw [dist_eq_norm]; exact h m x)
 have ht:dist (F t m x) W≤a:=(by rw [dist_eq_norm]; exact k m x)
 rw [dist_comm] at hx; have hu:dist V W ≤ a+a:= (dist_triangle ..).trans (add_le_add hx ht); unfold a at *; linarith
lemma LongQueue.resize(p:P.LongQueue S F f){T:Finset Cover}(u:S⊆T):P.LongQueue T F f:=⟨fun i=>(p.whereTo i).mono u,p.landing.mono u,p.bdd,p.saved⟩
-- Selection kit for uncountably many vectors, countable poses. Keep strong convergence on ALL.
lemma compact_fun {ι:Type*}[Finite ι] {V:ℕ→ι→ℝ}{c:ℝ}(p:∀ i j, |V i j|≤c): ∃ a:ℕ→ℕ, StrictMono a∧ ∃ F:ι→ℝ,Tendsto (fun i=>V (a i)) atTop (𝓝 F):=by
 let S:Set ℝ:=Set.Icc (-c) c; let Q:Set (ι→ℝ):= Set.univ.pi fun _=>S
 have hx:∀ i, V i∈ Q:=fun i j _=> abs_le.mp (p i j)
 obtain ⟨z,g,a,b,h⟩:= (isCompact_univ_pi (fun _=> isCompact_Icc)).isSeqCompact (x:=V) hx
 exact ⟨a,b,z,h⟩
open Spectrix
lemma keen_bay(X:Set (Buffered.Family P.calibration))(p:Odious X)(v:∀ f∈X,∃ q:P.Test,q.val=f ∧ q ∈bay P.calibration S true ∧ q∈enclave P.calibration)(L:ℕ→ Buffered.Family P.calibration)(t:∀ i,L i∈ X):∃ a:ℕ→ℕ,StrictMono a∧∃ f:P.Test, P.LongQueue S (fun i=>L (a i)) f∧ f∈enclave P.calibration:=by
 classical
 obtain ⟨T,d,h,ht,q⟩:=chief p
 choose J hJ hv Q using (show ∀ i: (T:Type _),∃ q:P.Test,q.val=i.val∧ q∈bay P.calibration S true ∧ q∈enclave P.calibration from fun i=> v i.val (ht i.property))
 let Y:= L; choose Z pa pk using (fun i=> (q (L i) (t i)).pulse)
 obtain ⟨a,g,A,b⟩:= compact_fun (V:=fun i (u:(T:Type _))=>Z i u.val) (c:=d) (fun i u=> pa i u.val u.property)
 let E(i:(T:Type _))(n:ℕ):ℂ:= ↑(Z (a n) i.val)
 have he:P.LongQueue S (fun n=>∑ i:(T:Type _), E i n • (J i).val) (∑ i:(T:Type _), (↑(A i):ℂ) • J i):= cash_L _ _ _ (fun i _=> (LongQueue.attain _ (hv i)).step (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_pi_nhds.mp b i))) -- tune ℝ smul
 suffices h:(fun n=>∑ i:(T:Type _), E i n • (J i).val)= (fun n=>L (a n)) from ⟨a,g,_,h ▸ he,Subalgebra.sum_mem (enclave P.calibration) (fun i _=> (enclave P.calibration).smul_mem (Q i) _)⟩
 funext n; let i:=a n; let f(x:Buffered.Family P.calibration):= Z i x • x; rw [←pk (a n)]
 change _=∑ i∈T,f i
 rw [←Finset.sum_coe_sort T f]
 apply Finset.sum_congr rfl; intro u _; unfold f; rw [hJ u]; unfold E; rw [Complex.coe_smul]
-- diagonal selectors of sequences of properties. Needed repeatedly.
structure Slow : Type where
 subSeq : ℕ→ℕ
 step : StrictMono subSeq
namespace Slow
variable (A:Slow){P:Spine}
def slow : Slow:= {subSeq:=id,step:= strictMono_id}
def more (B:Slow): Slow:=⟨A.subSeq∘ B.subSeq,A.step.comp B.step⟩
lemma stay (p:ℕ→Prop)(h:∀ᶠ i:ℕ in atTop,p i):∀ᶠ i:ℕ in atTop,p (A.subSeq i):=A.step.tendsto_atTop.eventually h
/-- further-thin eventually. New indices on earlier parts, ok. -/
def Delayed (T U:Slow):Prop:=∀ᶠ i:ℕ in atTop,U.subSeq i∈Set.range T.subSeq
lemma Delayed.stepThrough {T U V:Slow}(p:T.Delayed U)(q:U.Delayed V):T.Delayed V:=by
 obtain ⟨k,h⟩:= eventually_atTop.mp p
 filter_upwards [q, V.step.tendsto_atTop.eventually_ge_atTop (U.subSeq k)] with i ⟨r,v⟩ hk
 rw[←v]; exact h r (U.step.le_iff_le.mp (v.symm ▸ hk))
lemma Delayed.iff_tail {T U:Slow}(p:T.Delayed U)(P:ℕ→Prop)(h:∀ᶠ i:ℕ in atTop,P (T.subSeq i)):∀ᶠ i:ℕ in atTop,P (U.subSeq i):=by
 obtain ⟨k,t⟩:= eventually_atTop.mp h
 filter_upwards [p, U.step.tendsto_atTop.eventually_ge_atTop (T.subSeq k)] with i ⟨r,v⟩ hk; rw [←v]; exact t r (T.step.le_iff_le.mp (v.symm ▸ hk)) -- tune
lemma more_delay (B:Slow): A.Delayed (A.more B):= Eventually.of_forall fun i=> Set.mem_range_self _ -- tune
lemma spineDelay (T Z:ℕ→Slow)(p:∀ i,T (i+1)= (T i).more (Z i)) :let a:=fun i=>(T i).subSeq i;StrictMono a ∧(∀ j,∀ᶠ i in atTop,a i∈ Set.range (T j).subSeq):=by
 intro a
 have hv(i j :ℕ) (w:j ≤ i): Set.range (T i).subSeq⊆ Set.range (T j).subSeq:=by
    induction i,w using Nat.le_induction with
    | base=>exact subset_rfl
    | succ i he ih=> rw[p i]; exact fun t e=>by obtain ⟨k,q⟩:=e; exact ih ⟨_,q⟩ -- need provide witness
 refine ⟨strictMono_nat_of_lt_succ (fun i=>?_),fun j=>(eventually_ge_atTop j).mono fun i h=> hv i j h (Set.mem_range_self _)⟩
 unfold a; rw [p i]; change (T i).subSeq i< (T i).subSeq ((Z i).subSeq _); exact (T i).step ((Nat.lt_succ_self _).trans_le ((Z i).step.id_le _))
lemma selectors {I:Type*} [Countable I](P:I→Slow→Prop)(h:∀ i:I,∀ A:Slow,∃ B:Slow,P i (A.more B))(t:∀ i T,P i T→∀ S,T.Delayed S→P i S):∃ A:Slow,∀ i,P i A:=by
 classical
 cases isEmpty_or_nonempty I with
 | inl p=>exact ⟨slow,fun i=>isEmptyElim i⟩
 | inr p=>
   letI:=Classical.inhabited_of_nonempty p; letI:=Encodable.ofCountable I
   let u(i:ℕ):I:= (Encodable.decode i).getD (Classical.arbitrary I)
   have q:Surjective u:= fun i=>⟨Encodable.encode i,by unfold u; rw [Encodable.encodek]; rfl⟩
   let Y(i:ℕ)(T:Slow):Slow:=(h (u i) T).choose; let Z(k:ℕ):Slow:=Nat.rec slow (fun i T=>T.more (Y i T)) k
   obtain ⟨Hf,Ha⟩:= spineDelay Z (fun i=>Y i (Z i)) (fun _=>rfl); let T:Slow:=⟨_,Hf⟩
   refine ⟨T,fun i=>?_⟩
   obtain ⟨k,rfl⟩:=q i; apply t _ (Z (k+1)) ((h (u k) (Z k)).choose_spec) T (Ha (k+1))
end Slow
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
