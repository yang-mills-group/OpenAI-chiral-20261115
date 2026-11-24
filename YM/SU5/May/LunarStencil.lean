import YM.SU5.May.LunarHalf
import YM.SU5.May.TorqueBeam
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Lat Onyx Flare Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
open SU Tulip Hygrometry Personality Rush Dial Cube Kea Emu Tilted May.Floe
attribute [local instance] opCStarAlgebra
variable (N:Side)(P:Ramp)(p q:E4)(i:Title P)(x y:Cover)(b:ℝ) (v w:Ket SpinIdx) (T:Jill.Male)
local notation "𝕀" => Complex.I
local notation "θ"=> P.plan.flee
-- II. odd $Δ$ limit
private def bothF : Cover≃ Cover:= {toFun r:= -r-1,invFun r:= -r-1,left_inv r:=by dsimp; abel,right_inv r:=by dsimp; abel}
lemma underage : apAt N (bothF x)= -apAt N x:=by apply PiLp.ext; intro i; rw [PiLp.neg_apply,ap_fee,ap_fee]; change tune N*(↑(-x i-1:ℤ)+_)=_; push_cast; ring
lemma spect_opp : spectral (-p) (-q)= -spectral p q:=by
 have he:brushQ (-p)= -brushQ p:=by ext1 i; simp [brushQ,Fir.tmap]
 unfold spectral; rw [inner_neg_left,inner_neg_right,neg_neg]; ext1 i; simp only [Pi.smul_apply,Pi.neg_apply,smul_eq_mul]; simp only [ironQ,amiX,spendQ,norm_neg]; simp only [he,leer_under,Pi.neg_apply,mul_neg, neg_div]
lemma pollen : poll N (-x)= -poll N x:=by unfold poll; simp_rw [emit_neg]; rw [← bothF.tsum_eq]; simp_rw [underage,spect_opp]; exact tsum_neg ..
-- WickRay b plus/down. z label inside T. Common chargeAxis orientation.
def amount (N:Side)(P:Ramp)(T:Jill.Male)(B:Bool) (v w:Ket (Single N)):ℂ:= if B then TorqueBeam.wickRay (P.vehicle N) (ledger N 4 T) true 0 w v else TorqueBeam.wickRay (P.vehicle N) (ledger N 4 T) false 0 v w
def headS (N:Side)(v:Cover):Peb:= Floe.coins N 1 • lash (poll N v)
def gapC (P:Ramp)(B:Bool)(x y:Cover):Cover:= if B then P.plan.flee y-x else P.plan.flee x-y
variable {ι:Type*} {l:Filter ι} (F:ι→Jill.Male)(H:Tendsto (fun i=>(F i).val) l atTop)(g:Even N.val)
-- strip density
lemma pivot (a:SU.Slot): pitch N x 1 a v=cantor N x a v:=by simp [pitch, gain] -- tune `gain` ambiguous
-- sector parity assignment +basis pure
lemma swing (a:SU.Slot)(e:SpinIdx): cantor N (P.plan.flee x) a (acts P.imageP (basisKet e))= acts (P.vehicle N).val (basisC N x e a) :=by unfold cantor; simp_rw [basis_act,P.acted_basisC]
local notation "A"=>P.imageP
lemma swings_total (a:SU.Slot) : cantor N (P.plan.flee x) a (acts P.imageP v)= acts (P.vehicle N).val (cantor N x a v):=by
 nth_rw 1 [← basis_expand v]; rw [map_sum]; simp_rw [map_smul]; unfold cantor; rw [map_sum]; simp_rw [map_smul,P.acted_basisC,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,basis_act, Finset.sum_smul,Finset.smul_sum]; rw [Finset.sum_comm]; simp [smul_smul,smul_eq_mul]
variable (t z:SU.Slot)
def booth (B:Peb):ℂ:= if t=z then inner ℂ v (acts B w) else 0
include F H g
private lemma lamp (u:remains true v)(e:remains false w): Tendsto (fun i=> inner ℂ (cantor N x t v) (acts (ledger N 4 (F i)) (cantor N y z w))) l (𝓝 (booth v w t z (headS N (x-y)))):=by
 let V: Personality:= ⟨true,t,v,u⟩; let W:Personality:=⟨false,z,w,e⟩
 let f:= fun i:ι=> ice 4 N (F i) 1 x y V W; have he(i): inner ℂ (cantor N x t v) (acts (ledger N 4 (F i)) (cantor N y z w))= f i:=by rw [←pivot,←pivot]; exact (downPrice (j:=4) (F i) 1 x y V W rfl rfl).symm
 simp_rw [he,f, personPrice (by decide : 1≤4) g _ 1 (by norm_num) x y V W rfl rfl]; by_cases s:t=z; swap; · have ht:V.color ≠ W.color:= s; simpa [ht,booth, s] using (show Tendsto (fun _:ι=>(0:ℂ)) l (𝓝 (0:ℂ)) from tendsto_const_nhds)
 subst z; have ht:V.color=W.color:=rfl; let B:= headS N (x-y); rw [booth,if_pos rfl]; simp_rw [if_pos ht]; change Tendsto _ _ (𝓝 (inner ℂ V.voice (acts B W.voice)))
 nth_rw 2 [←V.hymn]; rw [sum_inner]; apply tendsto_finsetSum _; intro i _; nth_rw 2 [←W.hymn]; rw [map_sum,inner_sum]; apply tendsto_finsetSum _; intro j _; rw [map_smul,inner_smul_left,inner_smul_right,basis_inner,basis_act, ← Complex.star_def, ←mul_assoc, show B i j = coins N 1*(lash (poll N (x-y)) i j) from rfl]; exact (apLimits N (x-y) H i j).const_mul _ -- warning nth rw ←V hymn changes occurrences λ
omit F H g in
lemma shiftTarget{f:ι→ℂ}{φ ψ:ℂ}(u:Tendsto f l (𝓝 φ))(v:φ=ψ): Tendsto f l (𝓝 ψ):= v ▸ u -- dangling F! omit
-- kernel universal
lemma spot (B:Bool)(u: remains B v)(e:remains B w): Tendsto (fun i=> amount N P (F i) B (cantor N x t v) (cantor N y z w)) l (𝓝 (booth v w t z (chargeAxis P B (headS N (gapC P B x y))))) := by
 cases B
 · have hx: remains true (acts P.imageP v):= (by rw [reel_eq,act_mul,rising v u]; exact purse_u _ v u)
   simp only [amount,TorqueBeam.wickRay, ite_false, Bool.false_eq_true,ofReal_zero,zero_mul,add_zero]; have ha:= (lamp N (P.plan.flee x) y (acts (A) v) w F H g t z hx e).neg; rw [swings_total N P x v t] at ha; refine shiftTarget ha ?_
   unfold booth; split_ifs <;> try simp only [neg_zero]
   rw [chargeAxis, if_neg (by decide),act_neg,inner_neg_right]; apply congrArg Neg.neg; change inner ℂ (acts (A) v) (acts _ w)=_; nth_rw 1 [← star_star (A)]; rw [act_inner,←act_mul]; rfl -- goals?
 have hx: remains false (acts P.imageP w):=by rw [reel_eq,act_mul,sinking w e]; unfold remains; rw [map_neg,map_neg, show acts Aop (acts (cliff _) w) = _ from purse_d (tilted P) w e]; simp
 simp only [amount, TorqueBeam.wickRay, ite_true,ofReal_zero,zero_mul,add_zero]; have he:= (lamp N x (P.plan.flee y) v (acts (A) w) F H g t z u hx).neg; rw [swings_total N P y w z] at he; refine shiftTarget he ?_; unfold booth; split_ifs; swap; · simp
 rw [chargeAxis,if_pos rfl, gapC, if_pos rfl, show x- P.plan.flee y= -(P.plan.flee y-x) from (by abel)]; unfold headS; rw [pollen,show lash (-poll N _)=_ from map_neg lashCL _,smul_neg,act_neg,inner_neg_right,neg_neg,act_mul]
 rfl
#print axioms spot
#print axioms pollen
end YM.CF.May.Lunar
