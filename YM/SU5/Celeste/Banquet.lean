import YM.SU5.Celeste.Pass
import YM.CF.Buffered.Duet
import YM.CF.Buffered.Flute
/-!
Here adapting Ballad proofs from Buffered/Melody, plus Flute,Word, with the **six-family** realization BEFORE pivoting. Focus on explicit testing in Lamour. For this comparison: Each mark in the mirrored string of pairs, explicit in cover coordinates.
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
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare
namespace Lead
abbrev Clan:= Window.Family
def groundWord (A:Lead R)(s:Clan): Weaver:= fun N X=> sing R A.wave • ∑ p∈ colors s, ∑ q∈ colors s,(A.coil X.1 p q) • (Fock.remove (A.lower N q) * Fock.create (A.upper N p))
def patio(A:Lead R):= (visits (nodeC A.birth) A.traceV).toFinset
variable (A:Lead R)
variable (U:Clan)
local notation "Λu"=> cutM (colors U)
def clanMatrix (u : SU.E) : Op SU.Slot := Λu * (matter u).val * Λu
def clanOp {n:Side} (x y : Site n × SpinIdx) (u : SU.E) : Op (Single n) := Matrix.of fun i k=> if i.1=x ∧ k.1=y then clanMatrix U u i.2 k.2 else 0
lemma clan_law {n:Side} (x y : Site n × SpinIdx) (V : SU.E) (g : Seat n → SU.E) :
    twist (tradew n g) (clanOp U x y V) = clanOp U x y (g (node x.1)*V*(g (node y.1))⁻¹) := by
  let H := tradew n g; let W:= g (node x.1)*V*(g (node y.1))⁻¹
  have he(V:SU.E)(a b:Site n × SpinIdx) : tap (clanOp U x y V) a b= if a=x ∧ b=y then clanMatrix U V else 0:= by ext i j; by_cases p:a=x∧ b=y <;> simp [clanOp,tap,p]
  have hp (a b: Site n × SpinIdx) : tap (sings false H (clanOp U x y V)) a b=tap (clanOp U x y W) a b := by
    change tap (sings false (portX (Equiv.refl (Site n × SpinIdx)) (fun i=> matter (g (node i.1)))) _) _ _= _; rw [tap_sg (p:=Equiv.refl (Site n × SpinIdx)) (F:=fun i=> matter (g (node i.1))),he,he]
    by_cases h:a=x ∧ b=y; swap; · simp only [Equiv.refl_apply,if_neg h,win_z,mul_zero,zero_mul]
    obtain ⟨rfl,rfl⟩:= h; simp only [Equiv.refl_apply, true_and, if_true]; unfold W clanMatrix; rw [map_mul,map_inv,map_mul]
    let X:=matter (g (node a.1)); let Y:=matter (g (node b.1))
    change X.val*(Λu*(matter V).val*Λu)*star Y.val=Λu*(X.val*(matter V).val*star Y.val)*Λu
    have ht:X.val*Λu=Λu*X.val:= (matter_block ..).eq; have hu:star Y.val*Λu=Λu*star Y.val:= by
      have he:= (matter_block U (g (node b.1))⁻¹).eq; rw [map_inv] at he; exact he
    simp_rw [mul_assoc] at *; rw [←mul_assoc X.val Λu,ht,mul_assoc]; simp only [mul_assoc,←hu]
  ext ⟨x,a⟩ ⟨y,b⟩; exact congr_fun (congr_fun (hp x y) a) b
private lemma clan_index (V : SU.E) (x y : SU.Slot) : clanMatrix U V x y = if x∈ (colors U) ∧ y∈ (colors U) then (matter V).val x y else 0 := by by_cases h:x∈ (colors U)<;> by_cases k:y∈ (colors U)<;> simp [clanMatrix,cutM,Matrix.mul_diagonal,Matrix.diagonal_mul,h,k]
private lemma clan_dyad (x y : Site N × SpinIdx) (V : SU.E) : dg (clanOp U x y V)=∑ i∈(colors U), ∑ j∈ (colors U),(matter V).val i j • (put (x,i)*takeF (y,j)) := by
 let f(i j:Single N):= (clanOp U x y V) i j • (put i * takeF j)
 change ∑ i,∑ j, f i j=_
 have hp (a : Site N × SpinIdx) (i : SU.Slot) : ∑ t : Single N, f (a,i) t= ∑ j:SU.Slot, f (a,i) (y,j):=by
    rw [show (∑ t : Single N, f (a,i) t)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> f (a,i) k), sum_eq_single y]
    · intro i hi k; apply sum_eq_zero; intro j _; unfold f clanOp; rw [Matrix.of_apply,if_neg (fun z=>k z.2),zero_smul]
    simp
 rw [show (∑ i,∑ j,f i j)=_ from Fintype.sum_prod_type (fun k : (Site N × SpinIdx) × SU.Slot=> ∑ j, f k j)]; simp_rw [hp]
 rw [sum_eq_single x]; swap; · intro a _ t; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; unfold f clanOp; rw [Matrix.of_apply,if_neg (fun z=>t z.1),zero_smul]
 swap; · simp
 symm; let Z:= colors U;
 have hf(i j:Slot) : f (x,i) (y,j)=clanMatrix U V i j • (put (x,i)*takeF (y,j)):=by unfold f clanOp; rw [Matrix.of_apply,if_pos (show x=x∧ y=y from ⟨rfl,rfl⟩)];
 refine Eq.trans ?_ (sum_subset (f:=fun i=> ∑ j, f (x,i) (y,j)) (subset_univ (colors U)) ?_)
 · apply sum_congr rfl; intro i ti; refine Eq.trans ?_ (sum_subset (f:=fun j=> f (x,i) (y,j)) (subset_univ (colors U)) ?_)
   · apply sum_congr rfl; intro j tj; rw [hf,clan_index,if_pos ⟨ti,tj⟩]
   intro j _ t; rw [hf,clan_index,if_neg (fun w=>t w.2),zero_smul] -- indent
 intro i _ t; apply sum_eq_zero; intro j _; rw [hf,clan_index,if_neg (fun w=>t w.1),zero_smul]
lemma dgGround (V:Pane N) : let W:ℂ:= -sing R A.wave*Lifted.winding N A.birth * Lifted.winding N A.death; groundWord A U N (V,1)=W • dg (clanOp U (wrap N A.birth,upSpin A.slot) (wrap N A.death,dnSpin A.slot) (A.laps V)) := by
 intro W; let P:Site N × SpinIdx:=(wrap N A.birth,upSpin A.slot); let Q:Site N×SpinIdx:= (wrap N A.death,dnSpin A.slot)
 rw [clan_dyad,groundWord]; simp_rw [smul_sum]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_
 unfold lower upper basisC Fock.remove; rw [map_smul,map_smul,star_smul, create_put,create_put,Lifted.index, Lifted.index, Matrix.smul_mul, Matrix.mul_smul,show star (Lifted.winding N A.death)=_ from fee_real (Rush.periods N _)] -- tune
 let U₀:=put (P,i); let D:=takeF (Q,j); let c:=A.coil V i j; change _ • (c • (_ • (_ • (D*U₀))))= _ • (c • (U₀*D)); rw [show D*U₀=-(U₀*D) from (eq_neg_of_add_eq_zero_left ((mixed (Q,j) (P,i)).trans (if_neg ?_)))]; swap
 · intro v; exact dn_half A.slot (by rw [show dnSpin A.slot=upSpin A.slot from congrArg (fun t:Single N=> t.1.2) v]; exact up_half _)
 simp only [smul_smul,smul_neg,W,neg_mul,neg_smul]; congr 2; unfold Lifted.winding; ring -- tune
lemma groundWord_cov : covariant (A.groundWord U N) := by
 intro g u; change A.groundWord U N (gauge g u.1,1) = twist _ (A.groundWord U N (u.1,1)); rw [dgGround,dgGround,twist_scalar,dg_cov,clan_law,laps_t,laps_t,travel_gauge,node_of,node_of, ← wrap_stop_cover, A.moves] -- tune .reduce projecting pairs

variable (i:Axis)(s:ℤ)
private def bk_scaledn (a:Fin 2):ℂ := pin i (upSpin (shuffle i a)) (dnSpin a)
private def bk_scaleup (a:Fin 2):ℂ := pin i (dnSpin (shuffle i a)) (upSpin a)
@[local simp] private lemma bk_sh00 : shuffle 0 0=1 := by decide
@[local simp] private lemma bk_sh01 : shuffle 0 1=0 := by decide
@[local simp] private lemma bk_sh10 : shuffle 1 0=1 := by decide
@[local simp] private lemma bk_sh11 : shuffle 1 1=0 := by decide
@[local simp] private lemma bk_sh20 : shuffle 2 0=0 := by decide
@[local simp] private lemma bk_sh21 : shuffle 2 1=1 := by decide
@[local simp] private lemma bk_sh30 : shuffle 3 0=0 := by decide
@[local simp] private lemma bk_sh31 : shuffle 3 1=1 := by decide
@[local simp] private lemma bk_upp0 : upSpin 0=0 := by decide
@[local simp] private lemma bk_dwn0 : dnSpin 0=2 := by decide
@[local simp] private lemma bk_upp1 : upSpin 1=1 := by decide
@[local simp] private lemma bk_dwn1 : dnSpin 1=3 := by decide
set_option maxHeartbeats 1200000 in
private lemma bk_pinned (j:SpinIdx)(a:Fin 2) : pin i j (upSpin a)=(if j=dnSpin (shuffle i a) then bk_scaleup i a else 0) ∧ pin i j (dnSpin a)=(if j=upSpin (shuffle i a) then bk_scaledn i a else 0):=by
 fin_cases i <;> fin_cases j <;> fin_cases a <;> norm_num [pin,bk_scaledn,bk_scaleup, show (⟨0,by decide⟩:Axis)=(0:Axis) from rfl,show (⟨1,by decide⟩:Axis)=(1:Axis) from rfl,show (⟨2,by decide⟩:Axis)=(2:Axis) from rfl,show (⟨3,by decide⟩:Axis)=(3:Axis) from rfl, Matrix.cons_val_zero, Axis, Fin.ext_iff, gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
 all_goals norm_num [show Fin.addNat (0:Fin 2) 2 = (2:Fin 4) from rfl,show Fin.addNat (1:Fin 2) 2 = (3:Fin 4) from rfl,show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl]
 all_goals simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl, Matrix.cons_val_succ]; norm_num
 all_goals first | rfl | exact ⟨rfl,rfl⟩ | (simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ]; norm_num)

private lemma bk_paid (a:Fin 2): -(bk_scaledn i a*star (bk_scaleup i a))=(if i=3 then (1:ℂ) else -1):=by
 fin_cases i <;> fin_cases a <;> norm_num [pin,bk_scaledn,bk_scaleup, show (⟨0,by decide⟩:Axis)=(0:Axis) from rfl,show (⟨1,by decide⟩:Axis)=(1:Axis) from rfl,show (⟨2,by decide⟩:Axis)=(2:Axis) from rfl,show (⟨3,by decide⟩:Axis)=(3:Axis) from rfl, Matrix.cons_val_zero, Axis, Fin.ext_iff, gammaOp,grading,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ]
 all_goals norm_num [show Fin.addNat (0:Fin 2) 2 = (2:Fin 4) from rfl,show Fin.addNat (1:Fin 2) 2 = (3:Fin 4) from rfl,show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl]
 all_goals simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl, Matrix.cons_val_succ]; norm_num
 all_goals first | rfl | exact ⟨rfl,rfl⟩ | (simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ]; norm_num)

private lemma bk_depict (p q:SU.Slot) : Fock.remove (A.lower N p)*create (A.upper N q)= -(create (A.upper N q)*Fock.remove (A.lower N p)):=by
 unfold lower upper basisC Fock.remove; simp only [map_smul,create_put,star_smul,Matrix.smul_mul,Matrix.mul_smul]
 have he:Lifted.index N A.death (dnSpin A.slot) p≠ Lifted.index N A.birth (upSpin A.slot) q:=fun h=> dn_half A.slot ((show dnSpin A.slot=upSpin A.slot from congrArg (fun t:Single N=> t.1.2) h).symm ▸ up_half A.slot)
 rw [show star (put _)*put _= _ from eq_neg_of_add_eq_zero_left ((mixed _ _).trans (if_neg he)),smul_neg,smul_neg,smul_comm]
private lemma bk_letter_turn (p q:SU.Slot) : theta (carR i s N) (Fock.remove (A.lower N p) * create (A.upper N q))=(if i=3 then (1:ℂ) else -1) • (Fock.remove ((A.mirror i s).lower N q)*create ((A.mirror i s).upper N p)) := by
 let F:= carR i s N; let X:=A.mirror i s; have hl:acts F.val (A.upper N q)=bk_scaleup i A.slot • X.lower N q:=by
    unfold upper F; rw [acted_basisC]; simp_rw [(bk_pinned i _ _).1, ite_smul, zero_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]; rfl
 have hv: acts F.val (A.lower N p)=bk_scaledn i A.slot • X.upper N p:=by
    unfold lower F; rw [acted_basisC]; simp_rw [(bk_pinned i _ _).2, ite_smul, zero_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]; rfl
 rw [theta_mul,theta_upV,theta_downV]; change (Complex.I • create _) * (-Complex.I • Fock.remove _)=_
 rw [show acts _ (A.lower N p)=_ from hv,show acts _ (A.upper N q)=_ from hl,map_smul,show ∀ (v:Ket (Single N))(z:ℂ), Fock.remove (z • v)=star z • Fock.remove v from (by intro v z; simp [Fock.remove]),smul_smul,smul_smul,Matrix.smul_mul, Matrix.mul_smul, ←bk_paid i A.slot,X.bk_depict q p]; rw [smul_smul,neg_smul,smul_neg, neg_neg,show Complex.I * _ * (-Complex.I * _) = bk_scaledn i A.slot*star (bk_scaleup i A.slot) by linear_combination (norm:=ring_nf) -(bk_scaledn i A.slot*star (bk_scaleup i A.slot))*Complex.I_mul_I]

lemma bk_chant_mirror : reflMark (n:=N) i s (A.groundWord U N)=(A.mirror i s).groundWord U N := by
 funext V
 let X:= A.mirror i s
 change theta (carR i s N) (A.groundWord U N (fling i s N V.1,1))=X.groundWord U N (V.1,1)
 unfold groundWord
 rw [theta_smul,theta_sum]
 simp_rw [smul_sum,theta_sum]; rw [sum_comm]
 apply sum_congr rfl; intro q hp; rw [smul_sum]; apply sum_congr rfl; intro p hq
 rw [theta_smul,bk_letter_turn]
 have he:X.coil V.1 p q=star (A.coil (fling i s N V.1) q p):=by
   unfold coil X; rw [mirror_laps,map_inv]; rfl
 rw [he]
 simp only [smul_smul]
 congr 1
 change star (sing R A.wave)* (star _ *_)=sing R (axis_val i A.wave)*star _
 unfold sing; rw [phase_f]; push_cast; by_cases h:i=3<;> simp [h,Complex.star_def] <;> ring

end Lead
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Lead.groundWord_cov
#print axioms YM.CF.Buffered.Ballad.Lead.bk_chant_mirror
