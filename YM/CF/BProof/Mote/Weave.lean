import YM.CF.BProof.Mote.Polo
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
abbrev click (Q:SpaceM)(b:Bool)(x:Ket (Single N)): Ket (Single N) := acts (belt N Q b) x
abbrev humP (Q:SpaceM)(b:Bool)(x:Ket (Single N)):=coat (patchQ G) (click Q b x)
/-- The identical stencil T_G (never its inverse) pulled across the normalization step. -/
def songL (Q:SpaceM)(b:Bool)(U:Bkg (More P))(x:Ket (Single N)):Ket (Single P):=trailK (switchG G).symm.toEmbedding (acts (turret G j M U) (humP G Q b x))
lemma hold (b:Bool){x:Ket (Single N)}(p:okSpin b x): eligibleZ (lobe G true) b (humP G Q b x):=by rw [whale_plus]; unfold eligibleZ humP; rw [Fock.origin _ _ (reefS_deck ..)]; have ht:=belt_s Q p; unfold okSpin eligibleZ at ht; rw [show acts _ (click Q b x) = (if b then click Q b x else 0) from ht]; cases b; simp; simp
lemma adjust (E:m≃n)(x:Ket n)(A: Op m): trailK E.toEmbedding (acts (portW E A) x)=acts A (trailK E.toEmbedding x):=by
 nth_rw 1 [←trails_back E x]; rw [←flexL]
 rw [Fock.origin _ _ (shelfG _),trails]
lemma spinG (o:Odd G.count.val)(b:Bool){x:Ket (Single N)}(p:okSpin b x)(U): eligibleZ (tickA P) b (songL G j M Q b U x):=by
 let V:=acts (turret G j M U) (humP G Q b x); let E:= (switchG G).symm; change eligibleZ _ _ (trailK E.toEmbedding V); unfold eligibleZ; rw [←adjust,← show lobe G true=portW E (tickA P) from (lobe_t G).trans (tick_hold ..)]; have he:eligibleZ (lobe G true) b V:=beam b (hold G Q b p) ((canUse j G.count o).orients M G _); unfold eligibleZ at he; rw [he]; cases b <;> simp
theorem union_up (A B:Op n)(g:IsStarProjection A)(u:IsUnit B)(e: Commute A B){x:Ket n}(p:acts A x=x): acts (B⁻¹*A+star B*(1-A)) (acts B x) = x:=by
 let q:=acts B x; have he:=shine p e; have hx: (acts (1-A) q)=0:=by rw [act_sub,show acts A q=_ from he,act_one,sub_self]
 change acts _ q=_; rw [act_add,act_mul,act_mul,show acts A q=q from he,hx,map_zero,add_zero]; change acts B⁻¹ (acts B x)=_; rw [←act_mul,(Fock.live u).2,act_one]
lemma union_down (A B:Op n)(g:IsStarProjection A)(u:IsUnit B)(e:Commute A B){x:Ket n}(p:acts A x=0): acts (star (B⁻¹*A+star B*(1-A))) x=acts B x:=by
 have hf:Commute A B⁻¹:=Dial.poleM u e -- tune
 have he:A*(B⁻¹)=(B⁻¹)*A:=hf.eq; have h':Commute A (star (B⁻¹)):=by have ht:=congrArg star he; simp only [star_mul,g.isSelfAdjoint.star_eq] at ht; exact ht.symm -- tune
 
 rw [star_add,star_mul,star_mul,star_sub,star_one,g.isSelfAdjoint.star_eq,star_star,h'.eq,act_add,act_mul,p,map_zero,zero_add,sub_mul,one_mul,e.eq,act_sub,act_mul,p,map_zero,sub_zero]
abbrev prog (Q:SpaceM)(X:Nom N P)(v:Phys P):Phys N:= scaleZ Q.val (Dial.fire (Thread j) G M (unionP X) (cartsL (switchG G).symm v))
variable (X:Nom N P)
theorem pro_p (Q:SpaceM)(b:Bool){x:Ket (Single N)}(p:okSpin b x)(o:Odd G.count.val)(u:IsUnit (Peaks.cloth j M G (unionP X)))(k:Phys P): acts (port b x) (prog G j M Q X k)=prog G j M Q X (acts (port b (songL G j M Q b X.1 x)) k):=by
 let A:= (patchQ G); let F:=reefS G true; let R:=humP G Q b x; let U:=unionP X; let T:=Peaks.cloth j M G U; let W:= ticketT (Thread j) true M G U; have ht: W=T⁻¹*lobe G true+ star T*(1-lobe G true):=by unfold W ticketT U; rw [revI]
 have hu: T=turret G j M X.1:= turret_eq G j X.1 X.2 M
 have hz: port b R*quant W=quant W*port b (acts T R):=by
    have hq:eligibleZ (lobe G true) b R:= hold G Q b p; let D:=lobe G true; have hc:Commute D T:= (canUse j G.count o).orients M G U
    generalize R=e at *; cases b; change remove e*_= _; rw [quant_ann,ht, union_down D T (lobe_sq ..) u hc hq]; rfl
    change _=quant W*create _; rw [quant_create,ht,union_up D T (lobe_sq ..) u hc hq]; rfl
 let y:= acts T R; let E:=(switchG G).symm; let L:= Dial.fire (Thread j) G M U (cartsL E k)
 unfold prog; rw [belt_acts]; unfold Dial.fire; rw [map_smul]; congr 2 -- tune focus use congrArg
 change acts (port b (click Q b x)) (pailL A F _) = _; rw [← pipe_pail _ _ _ (reefS_deck ..)]; unfold songL; rw [←hu,←about]; unfold effectK; rw [←act_mul,←act_mul, show port b (coat A _) * _= _ from hz] -- tune
end Leg
end YM.CF.BProof.Bide
