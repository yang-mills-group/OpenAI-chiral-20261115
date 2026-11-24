import YM.CF.Buffered.Application
/-!
Each mark in the mirrored string of pairs, explicit in cover coordinates.
On TRUE links (or same law of reconstructed when delegating). Both pairs
use a common axial line. Any reflected copy is a melody: spin labels still
agree (may have swapped within chirality blocks). -/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}
def direction (v:ℤ): Cover:= v • step 3
def sail (f:Bool) (v:ℤ) := if f then -v else v
def axis_val (i:Axis)(v:Bool) := if i=3 then v else !v
def phaseF (b:Bool) : ℝ := if b then -1 else 1
lemma phase_f (i:Axis)(b:Bool) : phaseF (axis_val i b)=(if i=3 then 1 else -1)*phaseF b := by by_cases p:i=3<;> cases b <;> simp [axis_val,p,phaseF]
lemma mirror_direction (i:Axis) (v:ℤ) : (Signed.mirror i).act (direction v)=direction (if i=3 then -v else v):=by
 funext z; by_cases g:i=3; all_goals by_cases p:i=z <;> by_cases e:z=3 <;> simp_all [Signed.act, Signed.mirror, direction]
lemma mirror_travel (a:Shape)(x:Cover)(l:Walk):stop (a.motion x) (l.map (fun t=> t.rotate a.s))=a.motion (stop x l):=by induction l generalizing x with| nil=> rfl| cons i L h=>rw [stop,List.map_cons,stop, Lattice.Step.vec_rotate, ←Shape.motion_v,h]
def gap (B:Side)(R:ℕ) : ℤ := 4*B.val* (↑(R/(2*B.val)):ℤ)+ R+3
structure Lead (R:ℕ) where
 birth : Cover
 death : Cover
 slot : Fin 2
 wave : Bool
 traceV : Walk
 aligns : death = birth+direction (sail wave R)
 moves : stop (nodeC birth) traceV=nodeC death
 costs : traceV.length=2*R
namespace Lead
variable (A:Lead R)
def shuffle (i:Axis)(a:Fin 2):Fin 2:= if i<2 then 1-a else a
local notation "E" => plane
variable (i:Axis)(s:ℤ)
private lemma mirrored : stop (nodeC ((E i s).flee A.birth)) (A.traceV.map (·.rotate (Signed.mirror i)))=nodeC ((E i s).flee A.death):=by
 change stop _ (A.traceV.map (·.rotate (E i s).s))= _
 unfold nodeC; rw [←Shape.mote,← Shape.mote, mirror_travel]; exact congrArg _ A.moves

def mirror : Lead R := ⟨(E i s).flee A.death,(E i s).flee A.birth,shuffle i A.slot,axis_val i A.wave,Lattice.reverse (A.traceV.map (·.rotate (Signed.mirror i))),by
 let x:= (E i s).flee A.birth; rw [A.aligns,Shape.flee_p]
 change x=x+(Signed.mirror i).act (direction (sail A.wave R))+_; rw [mirror_direction]
 by_cases h:i=3<;> cases ht:A.wave <;> simp [axis_val,h,sail,direction],by rw [← mirrored A i s]; apply reverse_stop,by simp [Lattice.reverse,A.costs] ⟩

def laps (V:Pane N) := Lattice.travel (onC N V) (nodeC A.birth) A.traceV
def coil (V:Pane N)(p q: SU.Slot):ℂ:= (matter (A.laps V)).val p q
def upper (N:Side)(p:SU.Slot) := basisC N A.birth (upSpin A.slot) p
def lower (N:Side)(p:SU.Slot):= basisC N A.death (dnSpin A.slot) p
def sing (R:ℕ) (f:Bool) : ℂ := - ((R:ℂ)^3 /5)*(phaseF f:ℂ)
def birthOp (V:Pane N) := sing R A.wave • ∑ p∈ five, ∑ q∈ five, (A.coil V p q) • (Fock.remove (A.lower N q) * create (A.upper N p))
def chant {N:Side}: Mark N := fun V=> A.birthOp V.1
lemma mirror_laps (V:Pane N): (A.mirror i s).laps V=(A.laps (fling i s N V))⁻¹:=by
 unfold mirror laps; dsimp only
 rw [← mirrored A i s,travel_reverse,reflect_onC,moveC,travel_pull]; congr 2; exact ((E i s).mote _).symm
private def scaledn (a:Fin 2):ℂ := pin i (upSpin (shuffle i a)) (dnSpin a)
private def scaleup (a:Fin 2):ℂ := pin i (dnSpin (shuffle i a)) (upSpin a)
@[local simp] private lemma sh00 : shuffle 0 0=1 := by decide
@[local simp] private lemma sh01 : shuffle 0 1=0 := by decide
@[local simp] private lemma sh10 : shuffle 1 0=1 := by decide
@[local simp] private lemma sh11 : shuffle 1 1=0 := by decide
@[local simp] private lemma sh20 : shuffle 2 0=0 := by decide
@[local simp] private lemma sh21 : shuffle 2 1=1 := by decide
@[local simp] private lemma sh30 : shuffle 3 0=0 := by decide
@[local simp] private lemma sh31 : shuffle 3 1=1 := by decide
@[local simp] private lemma upp0 : upSpin 0=0 := by decide
@[local simp] private lemma dwn0 : dnSpin 0=2 := by decide
@[local simp] private lemma upp1 : upSpin 1=1 := by decide
@[local simp] private lemma dwn1 : dnSpin 1=3 := by decide
set_option maxHeartbeats 1200000 in
private lemma pinned (j:SpinIdx)(a:Fin 2) : pin i j (upSpin a)=(if j=dnSpin (shuffle i a) then scaleup i a else 0) ∧ pin i j (dnSpin a)=(if j=upSpin (shuffle i a) then scaledn i a else 0):=by
 fin_cases i <;> fin_cases j <;> fin_cases a <;> norm_num [pin,scaledn,scaleup, show (⟨0,by decide⟩:Axis)=(0:Axis) from rfl,show (⟨1,by decide⟩:Axis)=(1:Axis) from rfl,show (⟨2,by decide⟩:Axis)=(2:Axis) from rfl,show (⟨3,by decide⟩:Axis)=(3:Axis) from rfl, Matrix.cons_val_zero, Axis, Fin.ext_iff, gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
 all_goals norm_num [show Fin.addNat (0:Fin 2) 2 = (2:Fin 4) from rfl,show Fin.addNat (1:Fin 2) 2 = (3:Fin 4) from rfl,show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl]
 all_goals simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl, Matrix.cons_val_succ]; norm_num
 all_goals first | rfl | exact ⟨rfl,rfl⟩ | (simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ]; norm_num)

private lemma paid (a:Fin 2): -(scaledn i a*star (scaleup i a))=(if i=3 then (1:ℂ) else -1):=by
 fin_cases i <;> fin_cases a <;> norm_num [pin,scaledn,scaleup, show (⟨0,by decide⟩:Axis)=(0:Axis) from rfl,show (⟨1,by decide⟩:Axis)=(1:Axis) from rfl,show (⟨2,by decide⟩:Axis)=(2:Axis) from rfl,show (⟨3,by decide⟩:Axis)=(3:Axis) from rfl, Matrix.cons_val_zero, Axis, Fin.ext_iff, gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
 all_goals norm_num [show Fin.addNat (0:Fin 2) 2 = (2:Fin 4) from rfl,show Fin.addNat (1:Fin 2) 2 = (3:Fin 4) from rfl,show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl]
 all_goals simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl, Matrix.cons_val_succ]; norm_num
 all_goals first | rfl | exact ⟨rfl,rfl⟩ | (simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ]; norm_num)

private lemma depict (p q:SU.Slot) : Fock.remove (A.lower N p)*create (A.upper N q)= -(create (A.upper N q)*Fock.remove (A.lower N p)):=by
 unfold lower upper basisC Fock.remove; simp only [map_smul,create_put,star_smul,Matrix.smul_mul,Matrix.mul_smul]
 have he:Lifted.index N A.death (dnSpin A.slot) p≠ Lifted.index N A.birth (upSpin A.slot) q:=fun h=> dn_half A.slot ((show dnSpin A.slot=upSpin A.slot from congrArg (fun t:Single N=> t.1.2) h).symm ▸ up_half A.slot)
 rw [show star (put _)*put _= _ from eq_neg_of_add_eq_zero_left ((mixed _ _).trans (if_neg he)),smul_neg,smul_neg,smul_comm]
private lemma letter_turn (p q:SU.Slot) : theta (carR i s N) (Fock.remove (A.lower N p) * create (A.upper N q))=(if i=3 then (1:ℂ) else -1) • (Fock.remove ((A.mirror i s).lower N q)*create ((A.mirror i s).upper N p)) := by
 let F:= carR i s N; let X:=A.mirror i s; have hl:acts F.val (A.upper N q)=scaleup i A.slot • X.lower N q:=by
    unfold upper F; rw [acted_basisC]; simp_rw [(pinned i _ _).1, ite_smul, zero_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]; rfl
 have hv: acts F.val (A.lower N p)=scaledn i A.slot • X.upper N p:=by
    unfold lower F; rw [acted_basisC]; simp_rw [(pinned i _ _).2, ite_smul, zero_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]; rfl
 rw [theta_mul,theta_upV,theta_downV]; change (Complex.I • create _) * (-Complex.I • Fock.remove _)=_
 rw [show acts _ (A.lower N p)=_ from hv,show acts _ (A.upper N q)=_ from hl,map_smul,show ∀ (v:Ket (Single N))(z:ℂ), Fock.remove (z • v)=star z • Fock.remove v from (by intro v z; simp [Fock.remove]),smul_smul,smul_smul,Matrix.smul_mul, Matrix.mul_smul, ←paid i A.slot,X.depict q p]; rw [smul_smul,neg_smul,smul_neg, neg_neg,show Complex.I * _ * (-Complex.I * _) = scaledn i A.slot*star (scaleup i A.slot) by linear_combination (norm:=ring_nf) -(scaledn i A.slot*star (scaleup i A.slot))*Complex.I_mul_I]

lemma chant_mirror : reflMark (n:=N) i s A.chant =(A.mirror i s).chant := by
 funext V
 let X:= A.mirror i s
 change theta (carR i s N) (A.birthOp (fling i s N V.1))=X.birthOp V.1
 unfold birthOp
 rw [theta_smul,theta_sum]
 simp_rw [smul_sum,theta_sum]; rw [sum_comm]
 apply sum_congr rfl; intro q hp; rw [smul_sum]; apply sum_congr rfl; intro p hq
 rw [theta_smul,letter_turn]
 have he:X.coil V.1 p q=star (A.coil (fling i s N V.1) q p):=by
   unfold coil X; rw [mirror_laps,map_inv]; rfl
 rw [he]
 simp only [smul_smul]
 congr 1
 change star (sing R A.wave)* (star _ *_)=sing R (axis_val i A.wave)*star _
 unfold sing; rw [phase_f]; push_cast; by_cases h:i=3<;> simp [h,Complex.star_def] <;> ring
end Lead
structure Melody (B:Side)(R:ℕ) where
 first: Lead R
 last: Lead R
 slot_s : last.slot=first.slot
 wave_s : last.wave=first.wave
 face : Bool
 aligned : last.birth = first.birth+direction (sail face (gap B R))
namespace Melody
variable (A: Melody B R)
def mirror (i:Axis)(s:ℤ) : Melody B R:= ⟨A.first.mirror i s,A.last.mirror i s,congrArg (Lead.shuffle i) A.slot_s,congrArg (axis_val i) A.wave_s,(if i=3 then !A.face else A.face),by
 change (plane i s).flee A.last.death=(plane i s).flee A.first.death+_
 rw [A.last.aligns,A.wave_s,A.aligned,add_right_comm,Shape.flee_p, ← A.first.aligns,show (plane i s).s=Signed.mirror i from rfl,mirror_direction]; by_cases h:i=3<;> cases p:A.face <;> simp [h,sail] ⟩
def compare (b:Bool): ℂ:= if b then (compared:ℂ) else P20
def goal (b:Bool){N:Side} : Mark N := (if b then A.first.chant*A.last.chant else A.first.chant) - compare b • (1:Mark N)
lemma mirror_goal (b:Bool)(i:Axis)(s:ℤ): reflMark (n:=N) i s (A.goal b)=(A.mirror i s).goal b:=by
 funext V
 let u:=reflFields i s V
 have ht:theta (carR i s N) (A.first.chant u)= (A.mirror i s).first.chant V:=congr_fun (A.first.chant_mirror i s) V
 have he:theta (carR i s N) (A.last.chant u)= (A.mirror i s).last.chant V:=congr_fun (A.last.chant_mirror i s) V
 have hx: star (compare b)=compare b:=by unfold compare; split <;> simp [P20_value]
 unfold goal reflMark; cases b<;> simp only [ite_true,Bool.false_eq_true,ite_false,Pi.sub_apply, Pi.mul_apply,Pi.smul_apply,Pi.one_apply,theta_sub,theta_mul,theta_smul,hx,theta_one]; exact congrArg (·-_) ht; rw [show theta _ _= _ from ht,show theta _ _=_ from he]
end Melody
namespace Original
variable (K:Calibration)
def sun : Lead K.vertex := ⟨creatorSite,removerSite K,0,false,segment K,by rw [sail]; unfold removerSite direction; simp, end_node K,List.length_replicate⟩
lemma chant_sun (m:Side) : (sun K).chant (N:=K.c m)=word K m:=by
 funext v; unfold Lead.chant Lead.birthOp word; simp_rw [Pi.smul_apply,Finset.sum_apply, Pi.mul_apply]; change Lead.sing _ false • _= _
 rw [Lead.sing,phaseF]; simp only [Bool.false_eq_true,ite_false,Complex.ofReal_one,mul_one]; refine congrArg _ (sum_congr rfl ?_)
 intro p _; apply sum_congr rfl; intro q _; symm
 change ((Lead.coil (sun K) v.1 p q) • (1:FC (Single (K.c m)))) *_=_
 rw [Algebra.smul_mul_assoc, one_mul]; rfl

def primary : Melody K.B K.vertex := ⟨sun K, (sun K).mirror 3 K.plane0,rfl,by simp [Lead.mirror,axis_val],true,by
 change (plane 3 K.plane0).flee (removerSite K)=_
 funext i; by_cases h:i=3 <;> simp only [sail,ite_true] <;> simp [sun,removerSite,creatorSite,direction,flee_pos,h, Ne.symm, Calibration.atPlane] -- tune
 unfold gap Calibration.planeR; ring⟩
lemma tune (m:Side) (b:Bool) : (primary K).goal (N:=K.c m) b=(if b then (word K*thetaK K (word K)) m else word K m) - Melody.compare b • (1:Mark _) := by
 unfold primary Melody.goal; dsimp only; rw [← (sun K).chant_mirror,chant_sun]; rfl
end Original
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Original.tune
#print axioms YM.CF.Buffered.Ballad.Melody.mirror_goal
