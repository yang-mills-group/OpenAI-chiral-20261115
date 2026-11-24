import Bay.Season
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation

open Lor Py.Rate.BScale Push.Uniform
open Pressure SectorNext.Remainder Nor
open Push.AbsoluteSums Trees Roots
open BPress (NPL PL lscale lscale_late lscale_one)
local notation "VΔ" => Buffered.Afterglow.Tower.VacuumSelection.Spine
open Salt SU Swell QuadClock Mew Vow.TreasuryFog

open Till
variable {f g:ℝ→ℝ}
lemma borePL (e:BoreP f):PL f:=by
 obtain ⟨c,n,t,h⟩:=e.pace
 refine ⟨n+1,?_⟩
 filter_upwards [h,lscale_late.eventually_ge_atTop c] with x p r
 have ha:=lscale_one x
 have hb:0≤lscale x:= zero_le_one.trans ha
 rw [pow_succ,mul_comm]
 apply le_trans p
 exact mul_le_mul_of_nonneg_right r (pow_nonneg hb _)

lemma Cabs (e:Chill_v f):Chill_v fun x=> |f x| := e.trend (Eventually.of_forall fun i=>by rw [abs_abs])
variable (L: Patch)
lemma spentW (M:ℕ)(p:PL f): Chill_v (spent M (fun x=> f x*qL L x)):=by
 have h:= p.times (chill_iff.mp (cool_q L))
 exact spentC h M
lemma barrierW (F H:ℝ→ℝ)(p:Quench L F)(k:Chill_v H):Chill_v (barrier L F H):=
 ((Cabs p.illum_Q |>.noteR ((Cabs k).leanB BoreP.radius_c)).noteR
 (alloy L (chill_iff.mp (cool_q L))).illum_Q).cheap _

variable (g)

lemma coolGinv (p:Chill_v g):
 Tendsto (fun i=> (1-degreePrice (radiusB i) (g i) (runway i))⁻¹) atTop (𝓝 1) :=by
 simpa only [sub_zero,inv_one] using 
  ((tendsto_const_nhds (x:=(1:ℝ))).sub (deg_chill _ p).spine_a 
    |>.inv₀ (show (1:ℝ)-0≠0 by norm_num))
lemma coolG (p:Chill_v g): Tendsto (fun i=>θG (radiusB i) (runway i) (g i)) atTop (𝓝 0) := by
 simpa only [zero_mul] using p.spine_a.mul (coolGinv _ p)

variable {g}
lemma skyEyes (g:ℝ→ℝ)(p:Chill_v g):
 ∀ᶠ x in atTop,
 let b:=weeB x; let a:=runway x
 (0 < g x)→ degreePrice b (100*g x) a≤1/2 ∧ degreePrice b (g x) a < 1 ∧ θG b a (g x) ≤1 ∧ g x+Real.exp 1*θG b a (g x) ≤100*g x:=by
 have yu :=  coolG g p
 let a(i:ℝ):=runway i; let b(i:ℝ):=weeB i
 filter_upwards [(deg_chill _ p).spine_a.eventually (ge_mem_nhds
     (show (0:ℝ)<1/2 from by norm_num)),
   (deg_chill _ (p.cheap 100)).spine_a.eventually
     (ge_mem_nhds (show (0:ℝ)<1/2 from by norm_num)),
   yu.eventually (ge_mem_nhds zero_lt_one)] with x hp hf hu

 have e:=(show degreePrice (b x) (g x) (a x) ≤ 1/2 from hp)
 dsimp only
 intro w
 refine ⟨hf,lt_of_le_of_lt e (by norm_num),?_ ,?_⟩
 · exact hu
 have r: (1-degreePrice (weeB x) (g x) (runway x))⁻¹ ≤ 2:=(inv_le_comm₀ (by
    change 0 < 1-degreePrice (b x) (g x) (a x);linarith only [e]) (by norm_num)).mpr (by
    change (2:ℝ)⁻¹ ≤ 1-degreePrice (b x) (g x) (a x); linarith only [e])
 have z:=mul_le_mul_of_nonneg_left r w.le
 have v:=mul_le_mul (Real.exp_one_lt_d9.le) z
     (mul_nonneg w.le (inv_nonneg.mpr (show 0 ≤ 1-degreePrice (b x) (g x) (a x) from by linarith only [e]))) (by norm_num)
 unfold θG
 change Real.exp 1*(g x*(1-degreePrice (weeB x) (g x) (runway x))⁻¹)≤ _*_ at v
 linarith only [w,v]


lemma snow
 (F U H:ℝ→ℝ)(t:Quench L F)(r:Chill_v H)(h:Chill_v U):
 ∀ᶠ x in atTop, 0<runway x ∧
 (0≤U x→ Glacier (weeB x) (runway x) (F x) (U x) (H x) (barrier L F H x)):=by
 let G:=barrier L F H
 have ht:Chill_v G:=barrierW _ _ _ t r
 filter_upwards [warm_gt L,Work.E01.radiusB_tendsto.eventually_ge_atTop 5,
    skyEyes _ ht,churn G ht,churn U h] with x y yp yu i k
 let b:=weeB x;let a:=runway x
 have hv: (5:ℝ) ≤ b:=Nat.cast_le.mpr yp -- tune
 have hw:0<radD x:=show 0 < (b:ℝ) from by linarith only [hv]
 have hp:0<a:=inv_pos.mpr hw
 have ha: 5*a ≤ 1:=show 5 * (radD x)⁻¹ ≤ 1 from by rw [←div_eq_mul_inv, div_le_one hw]; exact hv -- tune
 obtain ⟨w,e,s⟩:=leftBarrier L F H x y hw
 obtain ⟨m,n,o,p⟩:=yu w
 obtain ⟨f,j⟩:=k
 refine ⟨hp, fun q=> ⟨hp,ha,w,q,e,?_,?_,?_,m,n,o,p⟩⟩
 · rw [mul_comm]
   exact i.1.trans (div_le_self hp.le (by norm_num))
 · exact f.trans (div_le_self hp.le (by norm_num))

 · nlinarith only [s,mul_le_mul_of_nonneg_right j w.le,mul_le_mul_of_nonneg_right f w.le,
     mul_pos (show 0<runway x from hp) w]




lemma warmning (M:ℕ)(F C D:ℝ→ℝ)(p:Quench L F)(q:NPL C)(h:PL D):
 Chill_v (spent M C)∧Chill_v (spells L M F D)∧
 ∀ᶠ x in atTop,
 Glacier (weeB x) (runway x) (F x) (spent M C x)
    (spent M (fun x=>D x*qL L x) x) (spells L M F D x):=by
 have a:=spentW L M h
 refine ⟨spentC q M,barrierW _ _ _ p a, ?_⟩
 filter_upwards [snow L _ _ _ p a (spentC q M)] with x u
 exact u.2 (spentPos C M x u.1)

abbrev WaitZ (L:Patch)(W f:ℝ→ℝ):Prop:=
   Tendsto (fun x=> W x * f x/qL L x) atTop (𝓝 0)
variable {L}
namespace WaitZ
variable {W V:ℝ→ℝ}
lemma commission (W:ℝ→ℝ)(p:Quench L f)(q:PL W): WaitZ L W f:=by
 have h:=q.times (forgeQ _ p)
 unfold WaitZ; simp_rw [mul_div_assoc]; exact h.drop
lemma rel (p:WaitZ L W f)(q:∀ᶠ x in atTop, W x*f x=V x*g x):WaitZ L V g:=by
   apply Tendsto.congr' _ p
   filter_upwards[q] with x t; rw[t]
lemma ab (p:WaitZ L W f): WaitZ L W (fun x=>|f x|) := by
 rw [WaitZ,tendsto_zero_iff_abs_tendsto_zero] at p ⊢
 change Tendsto (fun x=>|W x * f x / qL L x|) atTop (𝓝 0) at p
 change Tendsto (fun x=>|W x * |f x| / qL L x|) atTop (𝓝 0)
 simp_rw [abs_div,abs_mul] at p
 simp_rw [abs_div,abs_mul,abs_abs]; exact p

lemma together (p:WaitZ L W f)(q:WaitZ L W g): WaitZ L W (fun x=> f x+g x):=by
 unfold WaitZ; simp_rw [mul_add,add_div]; exact zero_add (0:ℝ) ▸ Tendsto.add p q
lemma coves {v:ℝ} (p:WaitZ L W f)(q:Tendsto g atTop (𝓝 v)):
 WaitZ L W (fun x=>g x*f x):=by
 have h: WaitZ L (fun x=>g x*W x) f:=by
   unfold WaitZ;simp_rw[mul_assoc,mul_div_assoc (g _)]
   exact mul_zero v ▸ q.mul p
 exact rel h (Eventually.of_forall fun _=> by ring)
lemma fixed (p:WaitZ L W f)(d:ℝ): WaitZ L W (fun x=>d*f x):= coves p tendsto_const_nhds
lemma readB (p:WaitZ L (fun x=>W x * V x) f): WaitZ L W (fun x=>V x * f x):= rel p (Eventually.of_forall fun _=>mul_assoc _ _ _)
end WaitZ
abbrev liftU (x:ℝ):=reserveT 2 6 (weeB x) (runway x)
abbrev cnt (x:ℝ):=countCost (incE (runway x) (weeB x))
abbrev powZ(n:ℕ)(x:ℝ):=(lscale x)^n
abbrev heelW(n:ℕ)(x:ℝ):=powZ n x*(powZ 100 x*liftU x)
abbrev roar(n:ℕ)(x:ℝ):=powZ n x*liftU x
abbrev shellW(n:ℕ)(x:ℝ):=(roar n x*radD x) * cnt x


lemma tariffsZ (n:ℕ) : PL (roar n)∧ PL (heelW n)∧ PL (shellW n):=by
 have c: PL cnt:= (borePL (purchaseInc 1)).mono (Eventually.of_forall fun _=> by rw [Nat.cast_one,one_mul])
 have r:=borePL (reserve_bond 2 6)
 have t:= (PL.scale.pow n)
 have s:= t.mul r
 exact ⟨s,t.mul ((PL.scale.pow _).mul r),(s.mul (borePL BoreP.radius_c)).mul c⟩

abbrev snowF (L:Patch)(D:ℝ→ℝ)(x:ℝ):= D x * qL L x

-- birth costs D quotes in w.Q units
structure HopsRate (L:Patch)(D:ℝ→ℝ)(n:ℕ):Prop where
 cheap:PL D
 head:WaitZ L (heelW n) (snowF L D)
 wide:WaitZ L (shellW n) (snowF L D)

lemma lakeRank {P:VΔ}(M L:ℕ)(F C D:ℝ→ℝ)(n:ℕ)
 (p:Quench P.par.R F)(q:NPL C)(r:HopsRate P.par.R D n):
 WaitZ P.par.R (powZ n) (icedCost P M L F D) :=by
 let R:= P.par.R
 let U:= recoat L C
 let V:= recoat L D
 have u:=recoatRate L q
 have v:= (PL.const (padFee L)).mul r.cheap
 let γ:= TopBill P M F V
 obtain ⟨_,cool,_⟩:=warmning _ M F U V p u v
 have h:WaitZ R (heelW n) (snowF R V):=
     (r.head.fixed (padFee L)).rel (Eventually.of_forall fun _=> by rw[←mul_assoc (padFee _)])
 have d:WaitZ R (shellW n) (snowF R V):=
     (r.wide.fixed (padFee L)).rel (Eventually.of_forall fun _=> by rw[←mul_assoc (padFee _)])

 have z1:WaitZ R (powZ n) (xHead P V):= h.rel (Eventually.of_forall fun _=>by
   unfold heelW xHead powZ BPress.lscale liftU snowF; ring)
 let H:=spent M (snowF R V)
 have ht:WaitZ R (fun i=>roar n i * radD i) H:=by

   apply (d.ab.fixed (M:ℝ)).rel
   filter_upwards with i
   unfold H shellW spent incT cnt; ring
 let T:=fun i=> qL R i*qL R i
 have t: Quench R T:= alloy R (chill_iff.mp (cool_q R))
 have a: WaitZ R (roar n) γ :=
    (((WaitZ.commission (roar n) p.normF (tariffsZ _).1).together ht.ab.readB).together
       (WaitZ.commission (roar n) t (tariffsZ _).1)).fixed 8

 have e: WaitZ R (powZ n) (markEG γ):=by
    apply (a.coves (coolGinv _ cool)).rel
    filter_upwards with x
    change (powZ n x * liftU x)*((1-degreePrice (weeB x) (γ x) (runway x))⁻¹*γ x)= _
    rw [mul_comm _ (γ x), mul_assoc]
 have t: WaitZ R (roar n) (fun i=>γ i*200):=
   (a.fixed 200).rel (Eventually.of_forall fun _=>by ring)
 have v:WaitZ R (powZ n) (markFG γ):=t.readB
 exact ((z1.ab.fixed _).together e.ab).together (v.ab.fixed _)

structure Levee (P:VΔ)(M L:ℕ)(F C D:ℝ→ℝ)(n:ℕ): Prop where
 rate:WaitZ P.par.R (powZ n) (icedCost P M L F D)
 ready: Dry P (fun w=> w.Rails → ∃ r,w.Thermal M L F C D r)
lemma runoff {P:VΔ}{F C D:ℝ→ℝ}
 (M L n:ℕ)(e:Ice P F)(p:NPL C)(r:HopsRate P.par.R D n):
 Levee P M L F C D n:=by
 let U:=recoat L C;let V:=recoat L D
 have h:Quench P.par.R F:=chill_iff.mpr e.rate
 obtain ⟨_,_,k⟩:= warmning P.par.R M F U V h (recoatRate L p) ((PL.const _).mul r.cheap)
 refine ⟨lakeRank _ _ _ _ _ _ h p r, ?_⟩
 filter_upwards [e.frost,(turnover P.par).eventually k,(Work.E01.radiusB_tendsto.comp 
    (turnover P.par)).eventually_ge_atTop (36*M+5)] with s f v b
 filter_upwards [f,(ageFar P s).eventually_gt_atTop
  (plankN L * weeB (Vale.hat P.par.R.L P.par.x s))] with i q S
 intro j p h
 let w:=takeUp P s i j
 have w5:5≤w.p.B:=h.size.symm ▸ (Nat.le_add_left 5 (36*M)).trans b
 have u:w.Chilled M F U V:=⟨q j p,h, by unfold Berth.gl; rw[h.size];exact v,w5⟩
 obtain ⟨r,H⟩:=Berth.readyFirm u

 refine ⟨r,H, ?_,?_⟩
 · constructor
   · rw [h.size]
     exact S
   exact (by decide:0<(5:ℕ)).trans_le w5
 unfold Berth.SlipCount
 rw[h.size]
 exact (le_add_of_nonneg_right (Nat.zero_le 5)).trans b

abbrev meltZ(t:ℕ)(x:ℝ):= (lscale x ^ t)⁻¹
lemma meltPos (t:ℕ)(x:ℝ):0 < meltZ t x :=
 inv_pos.mpr (pow_pos (zero_lt_one.trans_le (lscale_one _)) _)
lemma meltPL (t:ℕ):PL (meltZ t):=(PL.const 1).mono (Eventually.of_forall fun x=>by
 rw[abs_of_pos (meltPos ..),abs_one]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (lscale_one x)))

lemma expires (p:PL f):∀ᶠ t:ℕ in atTop,Tendsto (fun x=>meltZ t x*f x) atTop (𝓝 0):=by
 obtain ⟨n,h⟩:=p.bound
 filter_upwards [eventually_ge_atTop (n+1)] with t a
 rw [tendsto_zero_iff_norm_tendsto_zero]
 apply squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) _ lscale_late.inv_tendsto_atTop
 filter_upwards [h] with x k
 rw [Real.norm_eq_abs,abs_mul,abs_of_pos (meltPos ..),mul_comm]
 show |f x| * (lscale x ^ t)⁻¹ ≤ (lscale x)⁻¹
 rw [←div_eq_mul_inv]
 have hx:0<lscale x:=zero_lt_one.trans_le (lscale_one _)
 rw [div_le_iff₀ (pow_pos hx _),←mul_one |f x|]
 rw[show (lscale x)⁻¹=(lscale x)⁻¹*1 from (mul_one _).symm] -- remove
 rw [mul_one,mul_one,le_inv_mul_iff₀ hx]
 exact ((mul_le_mul_of_nonneg_left k hx.le).trans_eq ((mul_comm ..).trans (pow_succ ..).symm)).trans
    (pow_le_pow_right₀ (lscale_one x) a)

lemma bounce (R:Patch){Y D U:ℝ→ℝ}(p:NPL Y)(r:PL D)(k:PL U):
 ∀ᶠ t:ℕ in atTop, WaitZ R U (snowF R (fun x=>Y x+meltZ t x*D x)):=by
 filter_upwards [expires (k.mul r)] with t a

 have h:=(k.times p).drop.add a
 rw[zero_add] at h
 refine h.congr' ?_
 filter_upwards[warm_gt R] with x y
 change U x * Y x + _= U x *((_ + _) * qL R x) / qL R x
 rw [mul_div_assoc,mul_div_cancel_right₀ _ y.ne']
 ring
lemma slope (R:Patch)(n:ℕ){Y D:ℝ→ℝ}(p:NPL Y)(r:PL D):
 ∀ᶠ t:ℕ in atTop,HopsRate R (fun x=>Y x+meltZ t x*D x) n:=by
 obtain ⟨_,a,b⟩:=tariffsZ n
 filter_upwards [bounce R p r a,bounce R p r b] with t h g
 exact ⟨p.pl.add ((meltPL t).mul r),h,g⟩
