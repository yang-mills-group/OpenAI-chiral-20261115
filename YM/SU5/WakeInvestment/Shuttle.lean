import YM.SU5.WakeInvestment.Vary
import YM.SU5.WakeInvestment.Demarcate
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Shuttle
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexOrder
open Fock Cube Lat Tenant Tulip Scree Skye
open Buffered Afterglow Journey Buffered.Afterglow.Tower Ballad SitSpin SpinReceipt Tapestry
open Lifted Onyx
open YM.Stationary (Gaia)
open Py Preparation YM.Pressure
open Phase Rush Scroll Peaks Spire
open Lamour Lamour.Bridge Lamour.Bridge.Celeste Morn
attribute [local instance] opCStarAlgebra
variable {P:Preparation} {A:ℝ} (B:Side) (n s:ℕ) 
local notation "VR" s:max => zoomR P A s
abbrev kroll (P:Preparation) (A:ℝ)(n s:ℕ):ℕ:= n*zoomR P A s
-- coverage extends in positive 3-gauge
abbrev march (x:Cover) (n:ℕ) (B:Side): Cover:= x+ Heat.gaugeShift B n • step 3
abbrev xplus (P:Preparation)(A:ℝ)(x:Cover)(n s:ℕ):Cover:= march x (kroll P A n s) P.block
abbrev flip (x:Cover):Cover:= (plane 3 0).flee x
lemma commute_f (x:Cover)(p:ℕ)(B:Side): (plane 3 (Heat.gaugeShift B p)).flee (flip x)=march x p B:=by
 ext i; by_cases h:(3:Axis)=i; · subst i; unfold flip march; simp [flee_pos]; try ring
 unfold flip march; simp [flee_pos,h,Ne.symm h]
lemma alignL (x:Cover)(n): nodeC (march x n B) = nodeC x + (2*Heat.gaugeShift B n) • step 3:=by unfold nodeC march; ext i; simp [two_smul]; split_ifs <;> ring -- nat factor
private abbrev proj : Gaia:=EuclideanSpace.single (3:Axis) (1:ℝ)
-- mirror in scaled Gaia
abbrev opposite (x:Gaia): Gaia:= WithLp.toLp 2 (fun i=> if i=3 then - x i else x i)
abbrev runway (B:Side)(n:ℕ):ℝ:=4*(B.val:ℝ)* n
abbrev gait (P:Preparation)(x:Gaia)(n:ℕ): Gaia:= x+runway P.block n • proj
lemma forecast (x:Cover)(j:Axis) : march x n B j= if j=3 then x 3+Heat.gaugeShift B n else x j:=by by_cases p:j=3; · subst j; simp [march,step]
                                                                                                   simp [march,p]
lemma xP (x:Gaia) (i:Axis) (B:Preparation) : gait B x n i= x i + if i=3 then runway B.block n else 0:=by by_cases p:i=3 <;> simp [gait,proj,p]
@[simp] lemma plus_time (x:Gaia) (P:Preparation) : gait P x n 3=x 3 + runway P.block n:=by rw [xP]; simp
lemma opp_tim (x:Gaia): opposite x 3 = -x 3:=by simp
private lemma reach_of (x:ℕ→ Gaia) (y:Gaia)(p:∀ j:Axis,Tendsto (fun s=>x s j) atTop (𝓝 (y j))): Tendsto x atTop (𝓝 y):=(PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr p)

variable {n s}
lemma xplus_a {x:ℕ→ Cover}{y:Gaia}(u:0<A)(h:Appoint P A x y)(n:ℕ): Appoint P A (fun s=> xplus P A (x s) n s) (gait P y n):=by
 rw [appoint_as P u] at *; let X s:= xplus P A (x s) n s; let t:=runway P.block n; apply reach_of; intro j; rw [xP]; have ht:Tendsto (fun s=> riseX (VR s) (x s) j) atTop (𝓝 (y j)):= (PiLp.continuous_apply 2 _ j).continuousAt.tendsto.comp h
 apply (ht.add_const (if j=3 then t else 0)).congr'; filter_upwards [(zoom_grows P u).eventually_gt_atTop 0] with r a; let R':ℝ:= (zoomR P A r); have he:0<R':=Nat.cast_pos.mpr a; change (x r j:ℝ)/R'+_= (X r j:ℝ)/R'; unfold X xplus kroll; rw [forecast]; split_ifs with h; · subst j; push_cast; unfold Heat.gaugeShift t runway; push_cast; change _=( _ + 4*_*( _* R'))/_; field_simp
 rw [add_zero]
lemma xrev_s (P:Preparation)(A:ℝ)(s:ℕ)(x:Cover): gaugeRise P s A (flip x)=opposite (gaugeRise P s A x):=by
 ext i; let v:= sPow P s A; change ↑(nodeC (flip x) i)/ v=if i=3 then - (↑(nodeC x i)/v) else ↑(nodeC x i)/ v; split_ifs with h; · subst i; simp [nodeC, flip,flee_pos]; ring
 simp [nodeC, flip, flee_pos,Ne.symm h]
lemma xflip_a {x:ℕ→ Cover}{y:Gaia}(h:Appoint P A x y): Appoint P A (fun s=> flip (x s)) (opposite y):=by
 apply reach_of; intro j; have he:Tendsto (fun s=> gaugeRise P s A (x s) j) atTop (𝓝 (y j)):= (PiLp.continuous_apply 2 _ j).continuousAt.tendsto.comp h
 simp_rw [xrev_s]; by_cases p:j=(3:Axis)
 · subst j; exact he.neg
 change Tendsto (fun s=> opposite _ j) _ _; simpa only [opposite, if_neg p, WithLp.ofLp_toLp] using he
lemma xfront {x:ℕ→ Cover}{y:Gaia}(u:0<A)(h:Appoint P A x y)(p:0< y 3)(ℓ:ℕ) : ∀ᶠ s:ℕ in atTop, (ℓ:ℤ) ≤ nodeC (x s) 3:=by
 have e:= (PiLp.continuous_apply 2 (fun _:Axis=>ℝ) 3).continuousAt.tendsto.comp h; let r:= y 3/2; have hr:0<r:=half_pos p
 filter_upwards [(sPower_pay P u).eventually_ge_atTop ((ℓ:ℝ)/r), e.eventually (le_mem_nhds (show r< y 3 from (half_lt_self p)))] with s E t
 let R':=sPow P s A; have h: r≤ ↑(nodeC (x s) 3)/R':= t; apply Int.cast_le (R:=ℝ) |>.mp; push_cast; nlinarith only [(le_div_iff₀ (show 0<R' from BProof.coin_pos ..)).mp h, (div_le_iff₀ hr).mp E]
lemma flip_inj : Injective opposite := by
 intro x y e; ext i; have hx:=congrArg (fun t:Gaia=> t i) e; unfold opposite at hx; by_cases h:i=3<;>simpa [h] using hx
lemma flip_d (x y:Gaia): opposite x - opposite y = opposite (x-y):=by ext i; by_cases p:i=3 <;> simp [opposite,p]; try ring
lemma gait_d (P:Preparation)(n:ℕ)(x y:Gaia): gait P x n - gait P y n=x-y:=add_sub_add_right_eq_sub ..
lemma gait_up (P:Preparation)(x:Gaia): Tendsto (fun n:ℕ=> gait P x n 3) atTop atTop:=by
 simp_rw [plus_time]; let X:ℝ:=4* P.block.val; have he:0<X:= by unfold X; positivity
 exact tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop he tendsto_natCast_atTop_atTop)
lemma foreign (P:Preparation)(x y:Gaia): Tendsto (fun n=>dist (opposite (gait P x n)) (gait P y n)) atTop atTop:=by
 have he:= (gait_up P x).atTop_add_atTop (gait_up P y); apply tendsto_atTop_mono _ he; intro i; rw [dist_comm,dist_eq_norm]; have ht:= PiLp.norm_apply_le (gait P y i-opposite (gait P x i)) (3:Axis); rw [PiLp.sub_apply,opp_tim] at ht; refine le_trans ?_ ht; rw [sub_neg_eq_add]; exact (add_comm _ _).le.trans (le_abs_self _)

-- layout flight on union together. transport proofs, t0 positives. call Appoint not Stamp.
variable {I:Type*}[Fintype I] {z:ℕ→ I→ Cover}{y:I→Gaia}
-- all-lifting along height (no time offsets lost under P kernel). 
abbrev forward (z:I→ Cover)(P:Preparation)(A:ℝ)(n s:ℕ):=fun i=>xplus P A (z i) n s
abbrev troupe (z:I→ Cover)(P:Preparation)(A:ℝ)(n s:ℕ):=Sum.elim (flip ∘ (forward z P A n s)) (forward z P A n s)
abbrev dualC (v:I→Gaia) := Sum.elim (opposite∘v) v
omit [Fintype I] in
lemma onFlight_exact (B:Side)(L:List I)(x:I→ Cover)(n:ℕ):
    onFlight B (lay x L) 3 n=lay (fun i=> march (x i) n B) L:=by
 induction L with
 | nil=> simp [onFlight,lay,Tower.address]
 | cons i L ih=> unfold lay onFlight Tower.address at *; simp_rw [alignL] at *; simp only [List.map_cons,List.toFinset_cons, Finset.image_insert]; rw [ih]
lemma to_zone (u:0<A)(h:∀ i,Appoint P A (fun s=>z s i) (y i))(p:∀ i,(0:ℝ)< gait P (y i) n 3)(L:List I)(ℓ:ℕ): ∀ᶠ s:ℕ in atTop, Tower.region 3 0 ℓ (onFlight P.block (lay (z s) L) 3 (kroll P A n s)):=by
 have he(i:I):∀ᶠ s:ℕ in atTop,(ℓ:ℤ) ≤ nodeC (forward (z s) P A n s i) 3:= xfront u (xplus_a u (h i) n) (p i) ℓ
 filter_upwards [Filter.eventually_all.mpr he] with s t; rw [onFlight_exact]; intro x hx; obtain ⟨i,h,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp hx); rw [zero_add]; exact t i

omit [Fintype I] in
lemma troupe_loan (u:0<A)(h:∀ i,Appoint P A (fun s=>z s i) (y i))(f:∀ i j,y i=y j→∀ᶠ s:ℕ in atTop, z s i=z s j)(n:ℕ)(p:∀ i,(0:ℝ)< gait P (y i) n 3):
    let X:=fun n' s=>troupe (z s) P A n' s; let Y:=fun i=> gait P (y i) n; let Z:=dualC Y
    (∀ i,Appoint P A (fun s=> X n s i) (Z i)) ∧ (∀ i j, Z i=Z j→∀ᶠ s:ℕ in atTop, X n s i=X n s j):=by
 intro X Y Z; have hv(i j:I)(e:Y i=Y j):∀ᶠ s:ℕ in atTop,forward (z s) P A n s i=forward (z s) P A n s j:= (f i j (add_right_cancel e)).mono fun _ e=> congrArg (fun t=> xplus P A t n _) e
 have hp(i j:I): Z (Sum.inl i) ≠ Z (Sum.inr j):=by intro e; have hx:= congrArg (fun t:Gaia=>t 3) e; change opposite (Y i) 3= Y j 3 at hx; rw [opp_tim] at hx; exact absurd hx (LT.lt.ne (lt_trans (neg_lt_zero.mpr (p i)) (p j)))
 constructor; · rintro (i|i); exact xflip_a (xplus_a u (h i) n); exact xplus_a u (h i) n
 rintro (i|i) (j|j) e; exact (hv _ _ (flip_inj e)).mono fun _ e=> congrArg flip e; exact (hp i j e).elim; exact (hp j i e.symm).elim; exact hv i j e
end YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Shuttle
