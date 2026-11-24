import YM.CF.Mew.Pot
import YM.CF.Pso.Clear
import YM.CF.Mew.Blow
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Mew
open Function NormedSpace Filter Metric Finset MeasureTheory Lattice Wilson RG Forge Cube Fock Lat
open Skye Scree Jet Vow Tulip Scroll Spire Peaks Pastry Scion Stilo Palot Urn Hake
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]
variable {Z:Type*}[Fintype ι][DecidableEq ι][Fintype A][DecidableEq A][Fintype Z][DecidableEq Z]
-- constant fibers under apart.H
variable {J:n→A}{D:LeanV M→A}{X:ι→leaf A}{P:Finset ι}
-- π projection hol
abbrev sheen {T:Type*}[LinearOrder T][Fintype T]:Dough T→L[ℂ] FC T:= LinearMap.toContinuousLinearMap {toFun:=Subtype.val,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
lemma yield_R{T:Type*}[LinearOrder T][Fintype T](f:Key Z→ Dough T)(h:River (fun i=>(f i).val)):River f:=by
 let g:=sheen (T:=T); have he: Injective g:= Subtype.coe_injective; obtain ⟨W,p⟩:= LinearMap.exists_leftInverse_of_injective (f:=g.toLinearMap) (LinearMap.ker_eq_bot.mpr he)
 let F:= W.toContinuousLinearMap; have hx:f= F∘ fun i=>(f i).val:=funext (fun i=>(DFunLike.congr_fun p (f i)).symm); exact (sc_V h F).cong fun x _=>congrFun hx _ -- tune
variable (H: Key Z→ ModeW J D X P)(q:Crowd A)
lemma canal (U:River (fun i=> (H i).voice))(f:∀ (z z':Key Z), (H z).knots q=(H z').knots q)(g:∀ (z z':Key Z),(H z).rhythm q=(H z').rhythm q)(p:∀ (z z':Key Z),(H z).diet q=(H z').diet q):River (fun i=> tempo (H i) q):=by
 let h:= (H 0).rhythm q; let j:= (H 0).diet q; unfold Scion.tempo; split; swap; · exact zeroR _
 let L:=LinearMap.toContinuousLinearMap ((issue ((H 0).knots q)).flip h); let P':= (ContinuousLinearMap.mul ℂ (FC (LeanV M))).flip j
 exact ((sc_V (sc_V U L) P')).cong (fun x _=>by rw [f x 0,g x 0,p x 0]; rfl)
lemma tick_sum {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X](P:Finset A)(F:A→Key Z→X)(h:∀ i∈P,River (F i)):River (fun v=>∑ i∈P,F i v):=by
 induction P using Finset.induction_on with
 | empty =>simp_rw [sum_empty]; exact zeroR _
 | insert i P u p=>simp_rw [sum_insert u]; exact dub_V (h i (mem_insert_self ..)) (p (fun j hj=> h _ (mem_insert_of_mem hj)))
lemma yorkB{X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X](f: Key Z→X)(h:River f): River (-f):=⟨h.shore.neg,fun i v j x p=> (h.slope _ v j x p).neg⟩
lemma vigR (h:∀ i:Crowd A,River (fun j=> tempo (H j) i)): River (fun j=> Scion.vigor (H j) q):=by
 induction hx:(deckX q).card using Nat.strong_induction_on generalizing q with
 | h k ih=>
   have he: q∈ deckX q:=(deckH ..).mpr le_rfl; let W:= (deckX q).erase q; let U(j)(i):= vigor (H j) i; have hv:River (fun j=>∑ i∈W,U j i):= by
      refine tick_sum W (fun i j=>U j i) fun i hi=>?_ ; have hj:= (deckH ..).mp (mem_of_mem_erase hi); apply ih _ _ _ rfl; rw [←hx]
      apply card_lt_card; exact Finset.ssubset_iff_subset_ne.mpr ⟨fun a v=> (deckH ..).mpr (((deckH ..).mp v).trans hj), fun p=> (ne_of_mem_erase hi) (le_antisymm hj ((deckH ..).mp (p.symm ▸ he)))⟩
   let g(j):= vig (H j) q; have hw(j):g j=U j q+∑ i∈W,U j i:= (recon (vig (H j)) q).symm.trans (Finset.add_sum_erase _ _ he).symm
   exact (dub_V (yield_R g (h _)) (yorkB _ hv)).cong fun x _=>by change U x q=g x+ - _; rw [hw,add_neg_cancel_right]
end YM.CF.Mew
