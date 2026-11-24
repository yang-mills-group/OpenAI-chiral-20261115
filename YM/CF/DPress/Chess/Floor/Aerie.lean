import YM.CF.DPress.Chess.Floor.Porch
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
-- Last stage cost. The viewport at top needs one extra repair average and it must still fit the aperture for RP.Str. Operator.L.Epoch. Lease once before.
namespace Porch
variable {F H: HT n}
def glean (P:Loom n)(F:HT n) : Fixed.Test n:=fun i=> ∫ j,F (i,j)∂ Robe.τ P i
local notation "Rail"=> W.crop n Wall.rail
local notation "Vpay"=> W.crop n (2*ℓ)
lemma wait_C (p:Measurable P)(h:Envelope F):Envelope (glean P F):=by
 have he:=BPress.Law.marginalP (f:=fun x:Orbit n=> F (μC P x)) (Env.along h (earn p)) (depot n); rw [show glean P F= _ from funext (fun i=>(Transit.expect _ (Robe.lever p i) (fun x=>F (i,x)) (h.meas.comp measurable_prodMk_left)).symm)]; exact he -- tune
lemma price (p:Learn W ℓ F)(v:Measurable P)(t: Firm P β d)(f:Wall.wage r d ≤ ℓ): Boss n (Rail) (glean P F):=by
 let Z:= W.grade (show ℓ ≤ 2*ℓ by omega) n; have hp:= Wall.Lot_h f; have hq:= (W.smart f n); have hu:(Vpay)⊆ (Rail):= Subset.trans Z (W.grade hp.2.2.1 _); have ht:halo d (Vpay) ⊆ (Rail):= W.surrounding (by omega) _ ; obtain ⟨h,e,H⟩:= wait_C v p.envelope; refine ⟨e, ?_ ,?_, h,H⟩
 · intro i j x; let α:=Ties SU.group (Vpay); have hr : (∫ x,F (i,x)∂ Robe.τ P i)=(∫ x,F (i,x)∂ Robe.τ P j):= Robe.samePrice t (fun x=>F (i,x)) (p.envelope.meas.comp measurable_prodMk_left) (A:= Vpay) (fun y z q=>p.bits (i,y) (i,z) ⟨(Ties SU.group (Rail)).iseqv.refl i,q⟩) (agrees_mono x (Finset.coe_subset.mpr ht)); exact hr.trans (integral_congr_ae (Eventually.of_forall fun y=> p.bits (i,y) (j,y) ⟨x,α.iseqv.refl y⟩))
 intro i; letI:= Robe.prob v i; apply Reed.Fine.sector (s:=Fixed.upperIndices n); apply Window.fine_enlarge ?_ (estate_mem (S:=Print.spaceE (Fixed.upperIndices n) (Fixed.matterRegion n (Vpay)) false) (Env.along p.envelope (g:=fun j=>(i,j)) measurable_prodMk_left) (fun i=>p.issue _)); exact fun a b=> (Fixed.mem_matterRegion ..).2 (hu ((Fixed.mem_matterRegion ..).1 b))
-- Norm order μ fixed too. B witnesses top need filtration property.
lemma piano (p:Envelope F)(v:Roof n u k r P)(x:Pane n): peer W (glean P F) x=glean P (mirror W F) x:=by
 let T:=W.θt n; let y:=W.shine n x; let G:= fun z=> F (y,z); have ht:=Robe.move W v x; letI:=Robe.prob v.bill y; have he:Envelope G:=Env.along p measurable_prodMk_left; let μ:= Robe.τ P y; change T (∫ z,G z∂μ)=_; rw [← T.integral_comp_comm (Env.integrableX he μ)]; exact (Transit.expect (W.shine n) ht (T ∘ G) (T.continuous.measurable.comp he.meas)).symm
lemma stem (p:Learn W ℓ F)(q: Learn W ℓ H)(t: Roof n u k d P)(v:Firm P u d)(h:Wall.wage r d ≤ ℓ): peer W (glean P F)*glean P H= glean P (peer_H W F H):=by
 funext i; letI:=Robe.prob t.bill i; let G y:=mirror W F (i,y); let Z y:= H (i,y); let T:= Vpay; let l:= Ties SU.group (Rail)
 let A:= W.negZ T; have hu: (Vpay) ⊆ W.crop n ℓ:= W.grade (by omega) n -- subset type? replace
 have he (B C:Support (More n))(t:B⊆ C):halo d B⊆ halo d C:= fun i q=> by obtain ⟨k,v,h⟩:=halo_spec.mp q; exact halo_spec.mpr ⟨k,t v,h⟩
 have hz:= Robe.twinP v T A i ((W.rateF h n).down le_rfl (he _ _ hu) (he _ _ (W.spans hu)))
 have hv:Uses G (Ties SU.group A):=fun x y u=> congrArg (W.θ n) (p.bits (wake W (i,x)) (wake W (i,y)) ⟨l.iseqv.refl _,W.read u⟩); have hw:Uses Z (Ties SU.group T):=fun x y u=> q.bits (i,x) (i,y) ⟨l.iseqv.refl _,u⟩; rw [Pi.mul_apply,piano W p.envelope t]; exact Eq.symm (hz.symm.money (f:=G) (g:=Z) (Env.along (mir_C W p.envelope) measurable_prodMk_left) (Env.along q.envelope measurable_prodMk_left) hv hw)
end Porch
end YM.CF.DPress.Chess
