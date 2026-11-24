import YM.CF.Ups.Fawn
import YM.CF.Ups.Siena
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia)
open MeasureTheory Sods Girt Cube Pyx Py Scree Skye Graph
variable {N:Side}
local notation "Qx"=>SpinIdx
private lemma owned (g:Seat N→ SU.E)(a:Wing)(o:Site N)(z:Cover)(v:E)(y:SU.Slot): acts (tradew N g).val (basisKet (hub (skinF a y) o z))=acts (cote (matter (g (node (o+wrap N z))))).val (basisKet (hub (skinF a y) o z)):=by
 let x:=hub (skinF a y) o z; apply PiLp.ext; intro y; rw [basis_act,basis_act]; unfold cote tradew; simp only [jump_apply,Equiv.refl_apply]; split_ifs with h; swap; rfl; rw [h]; rfl
lemma ownH(g: Seat N→ E)(o: Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(h:E): acts (tradew N g).val (hint o z a U h)=acts (cote (N:=N) (matter (g (node (o+wrap N z))))).val (hint o z a U h):=by
 unfold hint; rw [tint,map_smul,map_sum,map_smul (acts _),map_sum]; refine congrArg _ (sum_congr rfl fun i _=>?_ ); simp only [map_smul]; exact congrArg _ (owned g a o z 1 i)
variable(o:Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(h:E)
local notation "c"=> (SU.z^(charge a.x))
lemma mintz(g:Seat N→ E)(hp:g (node (o+wrap N z))=central) : acts (tradew N g).val (hint o z a U h)= (SU.z^(charge a.x)) • hint o z a U h:=by
 rw [ownH,hp]; let v:=stemF o z a U h; let W:= central; let X:= (matter W); let Y:= matter v; let t:= wind o z
 have he:X*Y=Y*X:=by rw [show X*Y=matter (W*v) from (map_mul ..).symm]; apply Eq.trans _ (map_mul ..); apply congrArg; exact (by simpa only [show (↑(1:Sods.Key):ℕ)=1 from rfl,pow_one] using (center_comm 1 v))
 let L:Ket (Single N):= basisKet (hub a o z); have hz:acts (cote X).val L= c • L:=by
    unfold L X W; rw [tint,by_charge]; rw [sum_eq_single a.x]; · rw [Matrix.diagonal_apply_eq]; rfl
    · intro i _ u; rw [Matrix.diagonal_apply_ne _ u, zero_smul]
    simp
 change acts (cote X).val (t • acts (cote Y).val L)= c • t • _; rw [map_smul,←act_mul,←cue,he,cue,act_mul,hz,map_smul, smul_comm]
lemma ownV(g:Seat N→ E)(hp:g (node (o+wrap N z))=1) : acts (tradew N g).val (hint o z a U h)=hint o z a U h:=by
 rw [ownH,hp]; have hx:(cote (N:=N) (matter 1)).val=1:=by rw [map_one]; exact jump_id ..  -- tune
 rw [hx]; exact act_one _
-- invariant functional K(A) cannot be simple tensor with constant fermion marginal and gauge-only weight. Local central gauge element rotates all exposed Wing.dressings incoherently V. applies at all scales.
variable {q:Wave (Single N)}(hq:∀ g:Seat N→ E,effectK (tradew N g).val q=q)
include hq
local notation "fp"=>front
lemma goLam {α:Type*}(Z:α→TagT)(i j:α)(R:ℝ)(hi:signW (Z i).2=true)(hj:signW (Z j).2=false)(t:node (o+wrap N (Z i).1)≠ node (o+wrap N (Z j).1)) : matchF o U h R Z [i,j] q=0:=by
 let Wi(y):=hint o (Z y).1 (Z y).2 U h; let W:=-(gain R • Wi i); let Y:=gain R • Wi j; have hp: zoneA o U h R Z [i,j]=remove W*create Y:=by unfold zoneA Emu.train rollC; simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]; unfold nac; simp only [hi,hj,↓reduceIte, Bool.false_eq_true]; rfl
 let zK(y:α):= node (o+wrap N (Z y).1); let Aℤ:Seat N→ E:= fun x=> if x=zK i then central else 1; let A:=tradew N Aℤ; let u:=SU.z^(SU.charge (Z i).2.x)
 have hv: twist (quantU A) (zoneA o U h R Z [i,j])=(star u) • zoneA o U h R Z [i,j]:=by
    rw [hp,map_mul,twist_remove,twist_create]; have he:acts A.val W=u • W:=by unfold W Wi; rw [map_neg,map_smul]; rw [mintz (o:=o) (U:=U) ..]; module; exact if_pos rfl
    have hz: acts A.val Y=Y:=by unfold Y Wi; rw [map_smul,ownV]; exact if_neg (show zK j≠zK i from Ne.symm t) -- tune hp/g
    rw [he,hz]; rw [remove,map_smul,star_smul,← smul_mul_assoc]
 let X:=quantU A; let p:=mateK N; let Z':=zoneA o U h R Z [i,j]; let x:=matchF o U h R Z [i,j] q; have hz:star u*x=x:=by
    have he:=act_unit_inner X p (acts Z' q); rw [show acts X.val p=p from Girt.mastC Aℤ, Fock.swivel X Z' q,show acts X.val q=q from hq Aℤ,show twist X Z'= _ from hv,act_smul,inner_smul_right] at he; exact he
 have h_:u≠1:=by
    let k: Sods.Key:=1; let Y: Sods.Key:=0; have h: zp (Z i).2.x k≠ zp (Z i).2.x Y:= (zp_j _).ne (by decide +revert); rw [zp,zp,show k.val=1 from rfl,show Y.val=0 from rfl,pow_one,pow_zero] at h; exact h
 by_contra! he; have he': x ≠0:= he; have v:star u=1:=mul_right_cancel₀ he' (hz.trans (one_mul _).symm); apply h_; rw [←star_star u,v,star_one]
end YM.CF.Emu
