import YM.SU5.May.LunarUniform
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Lat Onyx Flare Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
open SU Tulip Hygrometry Personality Rush Dial Cube Kea Emu Tilted May.Floe
attribute [local instance] opCStarAlgebra
open Rink Trail
variable (N:Side)(P:Ramp)(b:Bool)(v:Ket (Single N))
variable {D:ℕ} {X:Type*} [Fintype X]
local notation "T"=>rimB N
open Spire Buffered Window Buffered.Afterglow.Satin
namespace Trail
variable {N P b}
variable (F:Trail N P b X)
def instant (i:X):= cantor N (F.atSlot i) (F.appointment i) (F.vr i)
noncomputable def brief(i k:X)(J:Jill.Male):ℂ:= amount N P J b (F.instant i) (F.instant k)
local notation "A"=>amount N
private lemma amount_s (N:Side)(P:Ramp)(J:Jill.Male)(b:Bool)(i:X→Ket (Single N))(w:X→ℂ): amount N P J b (∑ j:X,w j • i j) (∑ j:X,w j • i j)= ∑ j:X,∑ l:X, star (w j)*w l* amount N P J b (i j) (i l):=by
 cases b <;> simp only [amount,TorqueBeam.wickRay,Bool.false_eq_true, ite_false,ite_true,map_sum, map_smul, sum_inner, inner_sum,inner_smul_left,inner_smul_right,← Complex.star_def,Complex.ofReal_zero,zero_mul,add_zero,Finset.mul_sum,←Finset.sum_neg_distrib,Finset.sum_const_zero] <;> rw [sum_comm] <;> (refine sum_congr rfl fun _ _=> sum_congr rfl fun _ _=>?_; ring)
-- holds t eventually for all width.& β ON Sold.
variable {α:Type*}{K:Filter α}{M:α→Jill.Male}(x:Tendsto (fun i=>(M i).val) K atTop) (e:Even N.val)
include e x
lemma pillow (δ:ℝ)(g:0<δ): ∀ᶠ i in K,∀ w:X→ℂ,‖amount N P (M i) b (F.lives w) (F.lives w)-F.yield w‖≤ δ*(∑ i:X,‖w i‖)^2 := by
 have ht(j k:X): ∀ᶠ i in K,‖F.brief j k (M i)-F.stored j k‖ ≤ δ :=by
    let b:= F.stored j k; have he: Tendsto (fun i=> F.brief j k (M i)) K (𝓝 b):= spot _ _ _ _ _ _ M x e _ _ _ (F.noted j) (F.noted k); exact (Metric.tendsto_nhds.mp he _ g).mono (fun i h=>le_of_lt (by rw [← dist_eq_norm]; exact h))
 filter_upwards [(eventually_all.mpr (fun x=>eventually_all.mpr (ht x)))] with i u w; change ‖amount _ _ _ _ (∑ j:X,w j • F.instant j) (∑ j:X,w j • F.instant j)-_‖≤_; rw [amount_s, Trail.yield]; simp_rw [← Finset.sum_sub_distrib]; set s:ℝ:=∑ i:X,‖w i‖; rw [show δ*s^2=s*(δ*s) from (by ring)]; unfold s; simp_rw [Finset.sum_mul,Finset.mul_sum]; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>(norm_sum_le ..).trans (sum_le_sum fun l _=>?_); rw [←mul_sub,norm_mul,norm_mul, norm_star]; exact (mul_le_mul_of_nonneg_left (u j l) (by positivity)).trans_eq (by ring) -- tune defeq amount
end Trail
noncomputable def apron(P:Ramp):ℝ:= Trail.remainder P
lemma apron_p : 0 ≤ apron P:= by unfold apron Trail.remainder; have hp:= cess_p P; have he:= loan_p; have ht:=broker_p; positivity
noncomputable def tuition(P:Ramp)(D:ℕ):ℝ:=volE*(apron P+1)*tollV D
lemma volP : 0≤ volE:= by unfold volE; positivity
lemma tuition_p :0≤tuition P D:=by have h:=tollVal D; have h':= apron_p P; have t:=volP; unfold tuition; positivity
open TorqueBeam
lemma Cate (P:Ramp): ∀ᶠ D:ℕ in atTop,cessR P*loanP*(32/meal)≤(D:ℝ)∧∀ N:Side,80≤rimB N→ (D:ℝ)^10≤rimB N→ CapeF P N D:=by
 filter_upwards [eventually_ge_atTop (6:ℕ),(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (cessR P*loanP*(32/meal)), hot_ticket (P:=P) ] with D k a v; exact ⟨a,fun N t h=>⟨sub_le_self _ (Real.exp_nonneg _),t,v N h,k⟩⟩ -- tune explicit args
variable {α:Type*}{K:Filter α}{M:α→Jill.Male}(x:Tendsto (fun i=>(M i).val) K atTop)
lemma rebased : ∀ᶠ D:ℕ in atTop,∀ (N:Side)(W: Finset Cover), (D:ℝ)^10 ≤ rimB N →80 ≤ rimB N→Even N.val →(∀ y : Cover,nodeC y∈ W→Legible P N y∧‖age y‖≤hazySize D N)→∀ (M:α→Jill.Male), Tendsto (fun i=>(M i).val) K atTop→ ∀ᶠ i in K,∀ (b:Bool)(v:Ket (Single N)),withinM (treX N b) v→withinM (offerK N W) v→ -(tuition P D * (N.val:ℝ)*‖v‖^2) ≤ (promoted (P.vehicle N) (ledger N 4 (M i)) 0 (b,v) (b,v)).re := by
 filter_upwards [Cate P] with D p N W u t h w M x; let z:= fun y v=>(w y v).1; let n:ℝ:=N.val; let R':=(N.val:ℝ)^3; let Z:=tollV D; let zetaB:ℝ:= Z/R'; have hR:0<R':= by unfold R'; positivity
 let F (b:Bool):=loan N P b W z; filter_upwards [(eventually_all.mpr (fun b: Bool => (F b).pillow x h zetaB (div_pos (tollVal _) hR)))] with i v a y hy h'y
 let f:= readDust N a y W; let U:= F a; have yU:U.lives f=y:= earningK N P a y W z hy h'y; let m:= M i; let θ:= amount N P m a y y; let B:ℝ:=∑ i,‖f i‖; let L':=U.yield f; have hf: ‖θ-L'‖ ≤ zetaB*B^2:= by unfold θ; rw [← yU]; exact v a f
 have he: -(Trail.remainder P*Z*B^2) ≤ R'*L'.re:= U.fond f (p.2 N t u) (fun i=>(w ((U).atSlot i) (crystal N a W i).1).2) p.1
 rw [show promoted _ _ _ (a,y) (a,y)= θ from (by unfold θ amount promoted TorqueBeam.wickRay; cases a <;> rfl)]; apply le_of_mul_le_mul_left _ hR; -- goals
 let A:= R'*zetaB; have hs:R'*zetaB=Z:=by unfold zetaB; field_simp
 have hg:L'.re-θ.re ≤ zetaB*B^2:= (le_of_eq (Complex.sub_re ..).symm).trans ((Complex.re_le_norm (L'-θ)).trans (by rw [norm_sub_rev]; exact hf)); have he2 : -((apron P+1)*Z* B^2) ≤ R'*θ.re:= by nlinarith only [show -(apron P*Z*B^2)≤ R'*L'.re from he,mul_le_mul_of_nonneg_left hg hR.le,show R'*zetaB*B^2=Z*B^2 from (by rw [hs])]
 apply le_trans _ he2; rw [mul_neg]; apply neg_le_neg; refine (mul_le_mul_of_nonneg_left (show B^2≤_ from readSize N a y W) (mul_nonneg (add_nonneg (apron_p P) zero_le_one) (tollVal _).le)).trans_eq ?_; unfold tuition R'; ring
#print axioms rebased
end YM.CF.May.Lunar
