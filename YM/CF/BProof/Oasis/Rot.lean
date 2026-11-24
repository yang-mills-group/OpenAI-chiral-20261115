import YM.CF.BProof.Oasis.Test
import YM.CF.Gas.Open
/-! Scaling the ordinary exponent continuously before taking its logarithm
at gauge-rotated arguments. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums Civic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r δ c v η:ℝ}{N:Side}{P:Spin.Ready j a b l r}{F: Core j a b l r N}(H:Honor P F δ)(x:Loft F δ c v η)
abbrev runH (g:Geometry N):= (Tape.kiln H.1 c v η).st.drive g x
def motN (g:Geometry N)(u:Phys N):= acts (quantU (tradew N g)).val u
lemma ownSea(g:Geometry N) : owner (runH H x g)= twist (tradew N g) (owner x):= H.1.rise x.val.1.val.1 g
lemma honorRide (g:Geometry N)(k:Key)(u:ℝ) : view (runH H x g) k u= congrC (tradew N g) (view x k u):= Skein.weekSpin ..
lemma ownTick (g:Geometry N) : coreA (runH H x g)= twist (tradew N g) (coreA x):= (P.mat _ H.1.minN F.M _ H.1.shelter).cov.frame g x.val.1.val.1
lemma owners(g:Geometry N)(u:Phys N)(h:valid x u) : valid (runH H x g) (motN g u):=by
 let W:=runH H x g; let X:=tradew N g; let A:=quantU X; change Task (owner W) (acts A.val u); have he:= (show Ride .. from W.property).bridge.a; refine ⟨he, fun t=> h.nonzero (Eq.trans (by rw [act_unit] : u=acts (star A.val) (acts A.val u)) (by rw [t,map_zero])),?_⟩; rw [show owner W=twist X (owner x) from ownSea H x g,line_twist,←swivel,h.wage] -- tune
lemma honorPress(g:Geometry N): pressK (runH H x g)=motN g (pressK x):=by
 let X:= x.val.1.val.2; let v':= tradew N g; let U:= quantU v'; change acts (visor X) (pairWave (coreB _))=_; rw [show coreB (runH H x g)=congrC v' (coreB x) from honorRide H x g ..,congrC,←pair_cov]; change _=acts U.val (acts (visor X) (pairWave (coreB x))); rw [swivel,cabin_spin (band_separate _) (blockG X g true).symm (blockG X g false).symm]; rfl
include H in
theorem chooseS: ∃ u,valid x u:=by
 have he:IsStarProjection (owner x):=H.1.healthy x.val.1.val.1; obtain ⟨U,v,p⟩:=spot_projection (owner x) he; refine ⟨wedge U.val v, Task.sea he ⟨?_,wedge_norm ..⟩⟩; rw [p,act_twistLine,inner_self_eq_norm_sq_to_K,wedge_norm]; simp
variable {D:GramM N}{m o α C κ:ℝ}(q:Cargo D m o)
include q in
lemma fold_e(w:ℝ)(y:Pane N)(g:Geometry N): foldR D w (Lattice.gauge g y)=paintR false false (tradew N g) (foldR D w y):=by
 have he(y:Pane N): foldR D w y=w • (exponentL D.p D.F y+ exponentL D.p D.slip y):=by -- fold_smr needs x:Orbit, Choose exhibition maybe no Nonempty Ids
   unfold foldR readR; rw [Fintype.sum_prod_type,Fintype.sum_bool]; simp only [ite_true,Bool.false_eq_true, ite_false]; exact congrArg _ (add_comm ..)
 have ha(i):PressB D.p i (D.F i) m (q.vouchR (false,i)):=by simpa only [Bool.false_eq_true,ite_false] using q.press (false,i)
 rw [he,he,map_smul,map_add,Girt.traces D.p D.F (fun i=>⟨m,_,ha i⟩),Girt.traces D.p D.slip (fun i=>⟨m,q.vouchR (true,i), (q.press (true,i))⟩)]
include q in
theorem waveH(w:ℝ)(y:Pane N)(g:Geometry N)(u:Phys N): oracle x u (tank (coreA x) (zoom D w 0 y)) = oracle (runH H x g) (motN g u) (tank (coreA (runH H x g)) (zoom D w 0 (gauge g y))):=by
 let X:=quantU (tradew N g); let Z:= runH H x g; let T:= zoom D w 0 y; have he:(zoom D w 0 (gauge g y))=paintR false false (tradew N g) T:=by
   letI : NormedAlgebra ℚ (Cipher N):=NormedAlgebra.restrictScalars ℚ ℝ (Cipher N); unfold T zoom; rw [evaporate, mul_one,mul_one,fold_e q w,map_exp _ (Girt.spinM (n:=N) _)]
 let k: IsStarProjection (coreA Z):=leanA Z; rw [he]; have ht:tank (coreA Z) (paintR false false (tradew N g) T)= twist X (tank (coreA x) T):=by
    rw [tank_eq (coreA x) _ (leanA x), tank_eq _ _ k,←appleT (leanA x) k false false _ (show Scroll.sings false (tradew N g) _= _ from ?_)]; · rfl
    exact (ownTick H x g).symm
 unfold oracle motN; rw [honorPress, read_normal,read_normal]; change _=_* inner ℂ (acts X.val _) (acts _ (acts X.val _)); rw [ht,←swivel,act_unit_inner,motN,act_unit_inner] -- tune
end YM.CF.BProof.Oasis
