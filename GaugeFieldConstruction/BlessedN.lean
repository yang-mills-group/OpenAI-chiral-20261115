import GaugeFieldConstruction.CuniffN
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
open Spectrix
-- harvest variant exact LIN SPAN on covariants preserved. Need no continuity of Comparison!
lemma spanQueueN (X:Set (Buffered.Family P.calibration))(p:Odious X)(v:∀ f∈X,∃ q:P.Test,q.val=f∧ q∈bay P.calibration S true)(t:∀ i,F i ∈X)(h:P.LongQueue S F f): f∈ Submodule.span ℂ {g:P.Test|g.val∈X}:=by
 classical
 obtain ⟨T,d,k,ht,q⟩:=chief p
 choose J hJ hv using (show ∀ i: (T:Type _),∃ q:P.Test,q.val=i.val∧ q∈bay P.calibration S true from fun i=> v i.val (ht i.property))
 let Y:= F; choose Z pa pk using (fun i=> (q (F i) (t i)).pulse)
 obtain ⟨a,g,A,b⟩:= compact_fun (V:=fun i (u:(T:Type _))=>Z i u.val) (c:=d) (fun i u=> pa i u.val u.property)
 let E(i:(T:Type _))(n:ℕ):ℂ:= ↑(Z (a n) i.val)
 have he:P.LongQueue S (fun n=>∑ i:(T:Type _), E i n • (J i).val) (∑ i:(T:Type _), (↑(A i):ℂ) • J i):= cash_L _ _ _ (fun i _=> (LongQueue.attain _ (hv i)).step (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_pi_nhds.mp b i)))
 have h0:(fun n=>∑ i:(T:Type _), E i n • (J i).val)= (fun n=>F (a n)):=by
    funext n; let i:=a n; let L(x:Buffered.Family P.calibration):= Z i x • x; rw [←pk (a n)]
    change _=∑ i∈T,L i
    rw [←Finset.sum_coe_sort T L]
    apply Finset.sum_congr rfl; intro u _; unfold L; rw [hJ u]; unfold E; rw [Complex.coe_smul]
 rw [LongQueue.sameField (LongQueue.mono g.tendsto_atTop h) (h0 ▸ he)]; exact Submodule.sum_mem _ (fun i _=>Submodule.smul_mem _ _ (Submodule.subset_span (show (J i).val∈X from hJ i|>.symm ▸ ht i.property)))
variable (P:Spine)
lemma Heritor.estabN (D:P.Heritor)(s:ℕ)(x:Cover)(V:Waves): D.M s x V∈ Submodule.span ℂ {g:P.Test|g.val∈ Set.range fun i:ℕ=> P.Araw s x i V}:=by
 have hp:= D.earned s x V
 apply spanQueueN _ (P.Od_still ..) _ _ hp -- dot
 · intro f a; obtain ⟨b,rfl⟩:=a; obtain ⟨q,p,v,e⟩:= P.leafA s x V b; exact ⟨q,p,(Tapestry.locates ..).mpr e⟩
 exact fun i=> Set.mem_range_self _
lemma RailDialogN (D:P.Heritor)(s:ℕ)(x:Cover)(V:Waves)(w:Genre.pure.Room V): D.M s x V ∈ DialogueN P.calibration (cartO x 28):=by
 have he:Submodule.span ℂ {g:P.Test|g.val∈Set.range fun i:ℕ=>P.Araw s x i V} ≤ DialogueN P.calibration (cartO x 28):=by
    refine Submodule.span_le.mpr ?_; rintro u ⟨m,h⟩; obtain ⟨F,p,q⟩:=rayDialogN (K:=P.calibration) (P.MaleBook s m) (P.billStamp s).2 (P.billStamp s).1 V P.par.height w x; have hh:F=u:=Subtype.ext (p.trans h); exact hh ▸ q
 exact he (Heritor.estabN P D s x V)
#print axioms RailDialogN
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
