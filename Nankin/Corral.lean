import Nankin.Coins
import Rods.Sport
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
open YM.CF.Pannier.Chancel
variable {K:Calibration}{T:Type}{m n:Side}(S:Sport K m n T)(q:T)(o:Cover)(i:Axis)(t d:ℕ)
lemma clean_front {N:Side}(h:K.ℓ+t ≤ nodeC o i)(w:nodeC o i+t+K.ℓ ≤ (N.val:ℤ)):
 Lattice.halo t {node (wrap N o)} ⊆ band N i 0 K.ℓ:=by
 rw [←scarf]
 intro x p; obtain ⟨y,g,rfl⟩:=mem_image.mp p
 obtain ⟨a,b⟩:=bands_spec o g i
 let p:=y i; have h': K.ℓ ≤ p:=by omega
 have q':p+(K.ℓ:ℤ)≤ (N.val:ℤ):=by omega
 rw [band_spec]; rw [Int.cast_zero,sub_zero, wrap_here]
 let W:=p.toNat; change K.ℓ ≤ _ ∧ _≤_ -- tune
 have e:W<(More N).val:=by change _< N.val*2; have h:0<N.val:= N.property; unfold W; omega
 rw [show ((y i:ℤ):Per (More N))=(W:Per (More N)) from (by rw [← Int.cast_natCast,Int.toNat_of_nonneg (show 0 ≤ p by omega)]),ZMod.val_natCast_of_lt e]; unfold W; omega
-- time coords ≤d, other coords around node (same mirrored)
lemma chord_city {m:Side}(i j:Axis)(h:0≤nodeC o i)(w:nodeC o i ≤ d):rest K m
 (hyphen i 0 (Lattice.halo t {node (wrap (K.c m) o)})∪(Lattice.halo t {node (wrap (K.c m) o)})) j (2*(d+t)):=by
 let B:ℤ:=d+t; let p:ℤ:=if i=j then -B else nodeC o j-B
 rw [←scarf]; refine ⟨p,fun x a=>?_⟩
 rcases mem_union.mp a with a|a
 · obtain ⟨y,o',rfl⟩:=mem_image.mp a; obtain ⟨z,w',rfl⟩:=mem_image.mp o'
   let v:=(plane i 0).motion z
   refine ⟨v j,?_,?_,?_⟩
   · have b:=bands_spec _ w' j; unfold v; rw [fling_move]; by_cases e:i=j <;> simp only [p, e,if_pos,if_neg, not_false_eq_true] <;> unfold B <;> (try rw [e] at h w) <;> omega -- simp cause false cases?
   · have b:=bands_spec _ w' j; unfold v; rw [fling_move]; by_cases e:i=j <;> simp only [p, e,if_pos,if_neg,not_false_eq_true] <;> unfold B <;> (try rw [e] at h w) <;> omega
   change ((v j:ℤ) : Per _) = ((plane i 0).anon (K.c m) (wrap _ z)) j; rw [Shape.anno]; rfl
 obtain ⟨y,g,rfl⟩:=mem_image.mp a; obtain ⟨a,b⟩:=bands_spec _ g j; refine ⟨y j,?_ , ?_,rfl⟩ <;> unfold p B <;> split_ifs with e <;> (try rw [e] at h w) <;> omega

lemma livery (p1:S.castM i 0=0)(p2:S.place q=Lattice.halo t { Cube.node (wrap (K.c m) o)})
 (p3:K.ℓ+t ≤ nodeC o i)(p4:nodeC o i + t+K.ℓ≤ (K.c m).val)(p5:nodeC o i≤ d):
   let L:=[S.mirror i 0 q,q]; S.race L ∧ (∀ j, rest K m (S.hopit L) j (2*(d+t))) ∧ S.film L= reflMark i 0 (S.pose q)*S.pose q:=by
 intro a; let l:List T:=[q]; have ht:S.hopit l=S.place q:= by unfold l; simp [Sport.hopit]
 have e: Heat.gaugeShift K.B 0=0:=by unfold Heat.gaugeShift; ring
 have dQ:S.hopit l ⊆ band _ i (Heat.gaugeShift K.B (0:ℤ)) K.ℓ:=by rw [ht,p2,e]; exact clean_front _ _ _ p3 p4
 have E:a=(l.map (S.mirror i 0) ++ l):=rfl; rw [E]
 refine ⟨S.duos i 0 l dQ (List.pairwise_singleton ..),fun j=>?_ ,?_⟩
 · rw [Sport.hopit_app,Sport.hops, ht,e,p2]; exact chord_city _ _ _ _ _ (by omega) p5
 rw [S.recount i 0 l dQ,p1,e,show S.film l=S.pose q from (by unfold l; simp [Sport.film])]
#print axioms livery
end Calico
end YM.CF.Buffered.Afterglow.Tower
