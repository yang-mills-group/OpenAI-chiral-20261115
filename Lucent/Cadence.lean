import Lucent.Mantle
import Lucent.Sub
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment


open Peaks Scree
open RG Buffered.Afterglow
open Lamour Lamour.Bridge
open Morn Journey
variable {P:Preparation}{I J:Type}

/-- Width, room and geometry expenses. Repeated polling amplifies costs
inside finite s, will be paid even for every extra fixed step. -/
structure Squad(B:ℝ)(W:I→Staff)(b w:ℕ):Prop where
 day: dayStars W
 width: (w:ℝ)≤B
 room: (b:ℝ)≤B
 paid: ∀ i,(W i).Pays b w
 nearby: ∀ i j,|↑((W i).hub j)| ≤ B

variable {B A:ℝ} {W:I→Staff} {b w:ℕ} 
open Pannier.Chancel
lemma Squad.mono (h:Squad B W b w) (p:B ≤ A): Squad A W b w:= ⟨h.day,h.width.trans p,h.room.trans p,h.paid,fun i j=>(h.nearby i j).trans p⟩
lemma Squad.rods (s:ℤ)(h:Squad B W b w):Squad (B+2*|↑s|) (Lucent.rods s W) b w:=by
 have u:B≤B+2*|↑s|:=le_add_of_nonneg_right (by positivity)
 refine ⟨h.day,h.width.trans u,h.room.trans u,fun i=>sash_pay s (W i) (h.paid i) (h.day i),?_⟩
 intro i j; change |(↑((plane 3 s).motion (W i).hub j):ℝ)|≤ _
 rw [fling_move]; have n:= h.nearby i j
 split_ifs
 · push_cast; exact (abs_add_le ..).trans (by rw [abs_neg,abs_mul,abs_of_pos (by norm_num: (0:ℝ)<2)]; gcongr)
 exact n.trans u

lemma Squad.union {V:J→Staff}(h:Squad B W b w)(t:Squad B V b w): Squad B (Sum.elim W V) b w:=by
 refine ⟨?_,h.width,h.room,?_,?_⟩
 · rintro (i|i); exact h.day i; exact t.day i
 · rintro (i|i); exact h.paid i; exact t.paid i
 rintro (i|i); exact h.nearby i; exact t.nearby i
open Precision Pressure Rous Corona

lemma Squad.bounds {r v:ℕ}(h:Squad B W b w)(z:B+(r:ℝ)≤(v:ℝ)) (i:I):
  skyDeck (W i).hub r ⊆ Lattice.box v:=by
 intro x e; obtain ⟨y,g,rfl⟩:=mem_image.mp e
 obtain ⟨u,t⟩:=box_test.mp g
 suffices S:∀ j, |(↑(y j + (W i).hub j):ℝ)| ≤ v from box_test.mpr ⟨fun j=> by exact_mod_cast (abs_le.mp (S j)).1,fun j=> by exact_mod_cast (abs_le.mp (S j)).2⟩
 intro j; push_cast; rw [add_comm]; exact (abs_add_le ..).trans ((add_le_add (h.nearby i j) (abs_le.mpr ⟨by exact_mod_cast u j,by exact_mod_cast t j⟩)).trans z)

lemma Squad.rail {e:ℕ}(h:Squad B W b w)
    (z:B+↑(b+Staff.clearance+8) ≤ (e:ℝ)) (n:Side):
    Lucent.rail W b w n 0 e:= by
 intro i; refine ⟨h.paid i,?_⟩; unfold Staff.tenancy Staff.gateS
 rw [←wrap_pav]; intro t v; obtain ⟨y,u,rfl⟩:= mem_image.mp v
 have e:=Work.E08.separation_box_add (0:Site (More n)) (h.bounds z i u)
 apply blocks_test.mpr; simpa using e

/-- Squad prices on whole height. `l` separates arms and length expenses. -/
def DanceCost(B:ℝ)(R:ℕ→ℝ)(W:ℕ→I→Staff)(b l:ℕ→ℕ):Prop:=
   ∀ᶠ s in atTop, Squad (B*R s) (W s) (b s) (l s)

variable {R:ℕ→ℝ}{r b l:ℕ→ℕ}{W:ℕ→ I→Staff}(T:Velocity P R r)

lemma Velocity.bill (T:Velocity P R r)(E H:ℝ) :
   ∃ A,0<A ∧ ∀ᶠ s in atTop,E*R s+H ≤ sPow P s A:=by
 obtain ⟨A,u,p⟩:=T.book
 refine ⟨A+A,by linarith,?_⟩
 filter_upwards [p,(sPower_pay P u).eventually_ge_atTop (|H| + |E|+1)] with s p e
 let F:=sPow P s A
 rw [sPow,show BProof.coin (Vale.hat P.R.L P.x s) _ _ _= _ from (by simpa using (BProof.coin_mul (Vale.hat P.R.L P.x s) 0 A 0 0 A 0).symm : BProof.coin _ 0 (A+A) 0 = F*F)]
 change E*R s+H ≤ F*F
 calc
   _≤ |E| *F+|H| *F:=add_le_add (mul_le_mul (le_abs_self _) p (T.p s).le (abs_nonneg _)) ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) (by change (1:ℝ)≤ sPow P s A; linarith [abs_nonneg H,abs_nonneg E])))
   _≤ F*F:= by rw [←add_mul]; exact mul_le_mul_of_nonneg_right (by linarith) ((T.p s).le.trans p)
#print sPow
#check @BProof.coin_mul

include T
lemma DanceCost.collect [Fintype I] {S:Stencil I}(h:DanceCost B R W b l)(g:∀ᶠ s in atTop,Singing (W s) S) :
    ∃ A,0<A ∧ ∀ᶠ s in atTop,Expense P s A S (W s) (b s):=by
 obtain ⟨A,u,G⟩:=T.bill (B+B) (↑Staff.clearance+8+1)
 refine ⟨_,u,?_⟩
 filter_upwards [h,g,G] with s t z p
 let m:=B*R s+↑(b s+Staff.clearance+8)
 let a:=t.room; have q:B*R s ≤ m:=le_add_of_nonneg_right (Nat.cast_nonneg _)
 have d:((⌈m⌉₊:ℕ):ℝ)≤ sPow P s A:= ((Nat.ceil_lt_add_one ((Nat.cast_nonneg _|>.trans a).trans q)).le).trans (le_trans (by unfold m; push_cast; linarith only [a]) p)
 exact ⟨z,_,_,fun i=>⟨_,t.rail (Nat.le_ceil m) i⟩,t.width.trans (q.trans ((Nat.le_ceil m).trans d)),d⟩

omit T
/-- `disturb` units of P ray pixels : 8 P.block in gauge (4 B in matter). -/
abbrev disturb (r:ℕ→ℕ)(n s:ℕ):ℕ:=n*r s
abbrev liftum (P:Preparation)(r:ℕ→ℕ)(n s:ℕ):ℤ:= Heat.gaugeShift P.block (disturb r n s)
abbrev trackB (P:Preparation)(n:ℕ):ℝ:=4*P.block.val*n

lemma Velocity.sky (T:Velocity P R r):∀ᶠ s in atTop,(r s:ℝ)≤R s ∧ R s≤3*r s:=by
 filter_upwards [T.coupled.eventually (ge_mem_nhds (show (2:ℝ)<3 by norm_num)),T.coupled.eventually (le_mem_nhds (show (1:ℝ)<2 by norm_num))] with s u t; rw [le_div_iff₀ (T.t _),one_mul] at t; exact ⟨t, (div_le_iff₀ (T.t _)).mp u⟩
lemma Velocity.tracks (T:Velocity P R r)(n:ℕ):∀ᶠ s in atTop,2*|(↑(liftum P r n s):ℝ)|≤ 2*trackB P n * R s:=by
 filter_upwards [T.sky] with s u; unfold liftum Heat.gaugeShift disturb; unfold trackB; generalize P.block=h; push_cast; rw [abs_of_nonneg (by positivity)]; nlinarith only [mul_le_mul_of_nonneg_left u.1 (show 0≤ 8 * (h.val:ℝ)*n from by positivity)]

lemma trFar(P:Preparation): Tendsto (trackB P) atTop atTop:=tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)

lemma Squad.bandzero [Fintype I] {W:I→Staff}{b:ℕ}{x:ℕ} {t:ℤ}(h:Squad B W b w)(e:(x:ℝ)+(B+(B+8)) ≤2*t): Tower.region 3 0 x (Tower.address 3 t (band W b)) := by
 intro i v; obtain ⟨j,g,rfl⟩:= mem_image.mp v
 obtain ⟨k,q,f⟩:=mem_biUnion.mp g; obtain ⟨y,u,rfl⟩:=mem_image.mp f
 let a:Axis:=3
 have hg: -(↑(b+8:ℕ):ℝ) ≤ (y a:ℝ):=by exact_mod_cast (box_test.mp u).1 a
 push_cast at hg
 let ht:= -|(↑((W k).hub a):ℝ)|
 have hk:= (le_trans (neg_le_neg (h.nearby k a)) (neg_abs_le _))
 have hz:= h.room
 have l:(x:ℝ)≤(y a:ℝ)+ (↑((W k).hub a):ℝ)+2*t:= by linarith
 rw [zero_add]; simp; exact_mod_cast l

include T
lemma DanceCost.launch [Fintype I] (h:DanceCost B R W b l) (x:ℕ):
   ∀ᶠ n in atTop,∀ᶠ s in atTop,Tower.region 3 0 x (onFlight P.block (band (W s) (b s)) 3 (disturb r n s)):=by
 filter_upwards [(trFar P).eventually_ge_atTop (1+6*|B|)] with n t
 filter_upwards [T.sky,h,T.matter.eventually_ge_atTop (↑x+8)] with s p g v
 refine g.bandzero ?_
 have u:B * R s ≤ 3*|B| * (r s:ℝ):=by rw [mul_comm 3, mul_assoc]; exact mul_le_mul (le_abs_self _) p.2 (T.p _).le (abs_nonneg _)
 have ht:=(mul_le_mul_of_nonneg_right t (T.t s).le); unfold Heat.gaugeShift disturb; unfold trackB at ht; push_cast at *; nlinarith only [u,ht,v,mul_nonneg (abs_nonneg B) (T.t s).le]
