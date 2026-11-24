import YM.CF.BProof.Mote.Snow
import YM.CF.Bloom.Flux
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive Tap Haro
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
set_option synthInstance.maxSize 28000
namespace Leg
variable {m n : Type}[LinearOrder m][Fintype m][LinearOrder n][Fintype n]
variable {N P:Side}(G:Ratio N P)(j:ℕ) (Q:SpaceM)(M:Male)
open TripD
open Reed (Fine)
variable (i:Axis)(S : Support (More N)){a:Bool}
local notation "κ"=> winter S false
-- supply function on the Complex submodule. No need to prove linear in its input (pointwise faithful basis witnesses). Continuity for bounded family. Output fine.
structure Rider (E:Support (More N))(K:Support (More P))(i:Axis)(U:Ratio N P)(j:ℕ)(M:Male)(Q:SpaceM) where
 W: ↑(winter E false)→ Pane P → FC (Single P)
 OK: Continuous (Function.uncurry W)
 fee(T):Meet K false T.val U j M Q i (W T)
variable {k:ℕ} (o:Odd G.count.val)(v:SetK j G.count k)
local notation "Wψ"=> reach G S (units G.count k)
lemma Meet.null (i) (X:Support (More P)): Meet X false 0 G j M Q i 0:=by refine ⟨continuous_const,fun _ _ _=>rfl,fun _=>Fine.empty _,fun U t p=>by rw [act_zero,Pi.zero_apply,act_zero,programB,map_zero],?_⟩; rw [theta_zero,mirQ]; intro t s x; simp only [Pi.zero_apply,theta_zero,programB]; rw [act_zero,act_zero,map_zero]
include o v
lemma train : Nonempty (Rider S Wψ i G j M Q):=by
 let K:= Module.finBasis ℂ (κ); choose f h using fun x=> snow_p G j Q M i o v (show Snow S false (K x).val from (K x).property)
 let g(x):Obs P:=f x; let W(z:κ):=∑ i, K.repr z i • g i
 have hp:Continuous (Function.uncurry W):=by change Continuous (fun z: ((κ)×Pane P)=> W z.1 z.2); have he(i):Continuous (fun z:κ=>K.repr z i):=(K.coord i).continuous_of_finiteDimensional; unfold W; simp only [Finset.sum_apply, Pi.smul_apply]; exact continuous_finsetSum _ fun i _=> (he i|>.comp continuous_fst).smul ((h i).cont.comp continuous_snd)
 refine ⟨W,hp, fun T=>?_⟩; let N_:Finset (Fin (Module.finrank ℂ (κ))):=univ
 let A(z):FC (Single N):=(K z).val; have he(F:Finset (Fin (Module.finrank ℂ (κ)))): Meet Wψ false (∑ i∈F,K.repr T i • A i) G j M Q i (∑ i∈F,K.repr T i • g i):=by
    induction F using Finset.induction_on with| empty=> simp only [sum_empty]; apply Meet.null | insert i F p v=> rw [sum_insert p,sum_insert p]; exact (h i |>.smul _).add v
 unfold W; rw [←show ∑ z,K.repr T z • A z=T.val from ?_]; -- basis rewrite motive?
 exact he _
 change ∑ z, K.repr T z • (κ).subtype (K z)= (κ).subtype T; simp_rw [← map_smul, ←map_sum (κ).subtype,K.sum_repr]
end Leg
end YM.CF.BProof.Bide
