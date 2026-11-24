import YM.CF.BProof.Prox.Recruit

/- Transfer PL spectral estimates to Show using chunks as in B-poly/B-matrix. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prox.Show
open Function Filter Finset MeasureTheory Matrix
open scoped Topology BigOperators Classical
variable {A X E I J K L: Type*}[Fintype A][Fintype I][Fintype J][Fintype K][MeasurableSpace X]
variable {B:Base A}{O: Atmos A X}{F:B.Index I}{G:B.Index J}{H:B.Index K}{a p q:ℝ}
variable [NormedAddCommGroup E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

section Balls
variable {Y: Board X I J E}
private lemma singleton (g:I→ J→Finset A)(u:I→J→ℝ)(v:∀ i j,Rent O (g i j) (fun x=> Y x i j) (u i j))
    (h:∀ i j,u i j≠0→ B.C (g i j)∧F.port i∈g i j∧G.port j∈ g i j)
    (k:∀ i,∑ j,Real.exp (a*(g i j).card)*u i j ≤p)(k':∀ j,∑ i,Real.exp (a*(g i j).card)*u i j≤p): Show O F G Y a p := by
 refine recruit (L:=Unit) (fun i j _=>g i j) (fun i j _=>u i j) (fun i j _ x=> Y x i j) _ (fun i j _=>v i j) (fun i j _=>h i j) (fun i j=>by simp) (by simpa only [Fintype.sum_unique] using k) (by simpa only [Fintype.sum_unique] using k')

def radiusBill (B:Base A) (a:ℝ)(k r:ℕ):ℝ:= (((2*k+1)^B.dim :ℕ):ℝ)*r*Real.exp (a*((2*k+1)^B.dim:ℕ))
lemma balls {k:ℕ}(u:∀ i j,¬ B.N (F.port i) (G.port j) k→ ∀ x,Y x i j=0)(hp:0≤p)(ha:0≤a)
    (v:∀ i j,Rent O (B.ball (F.port i) k) (fun x=> Y x i j) p): Show O F G Y a (radiusBill B a k (max F.roof G.roof)*p) := by
 let l(i:I):=B.ball (F.port i) k; let R(i:I)(j:J):=G.port j∈l i
 let W (i j) := if R i j then p else 0
 let D:= (2*k+1)^B.dim
 let H:=Real.exp (a*D)*p; let r:=Max.max F.roof G.roof; let Q:=radiusBill B a k r*p
 have he(i): Real.exp (a*(l i).card)*p ≤ H:=mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (B.size _ _)) ha)) hp
 have hv(d:ℕ)(v:d≤D*r) : (d:ℝ)*H≤Q:= by
    apply le_trans (b:=((D*r:ℕ):ℝ)*H) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr v) (by unfold H; positivity)); apply le_of_eq; unfold Q radiusBill H D; push_cast; ring
 apply singleton (g:=fun i _=>l i) W
 · intro i j; unfold W; split; exact v _ _; next h=> rw [show (fun x=> Y x i j)=(0:X→E) from funext (fun x=>u _ _ (fun k=>h ((B.ball_m ..).2 k)) x)]; exact Rent.zero
 · intro i j h; exact ⟨B.solid _ _,B.resides _ _,not_not.mp (fun k'=>h (if_neg (c:=R i j) k'))⟩
 · intro i; apply le_trans (b:= ∑ j:J with R i j,H); rw [sum_filter]; refine sum_le_sum (fun j _=>?_); unfold W; split; exact he _; rw [mul_zero]; rw [sum_const,nsmul_eq_mul]; exact hv _ ((G.vent_ball _ _).trans (Nat.mul_le_mul_left _ (le_max_right ..)))
 intro j; apply le_trans (b:=∑ i:I with F.port i∈ B.ball (G.port j) k,H); rw [sum_filter]; refine sum_le_sum fun i _=>?_ ; simp only [show F.port i∈ B.ball (G.port j) k ↔ R i j from ⟨fun h=>(B.ball_m ..).2 (B.symm ((B.ball_m ..).1 h)),fun h=>(B.ball_m ..).2 (B.symm ((B.ball_m ..).1 h))⟩]; unfold W; split; exact he _; rw [mul_zero]; rw [sum_const,nsmul_eq_mul]; exact hv _ ((F.vent_ball _ _).trans (Nat.mul_le_mul_left _ (le_max_left ..))) -- tune rewrite iff
lemma office [Countable X][MeasurableSingletonClass X] (Y:Pup X I E)(S: Scope X A)(k:ℕ)(v: Via F S Y k)(h:0≤p)(u:∀ x i j,‖Y x i j‖ ≤ p)(he:0 ≤ a) : Show (Atmos.discrete A X S) F F Y a (radiusBill B a k F.roof*(3*p)):= by
 rw [← max_self F.roof] -- tune nth
 apply balls (fun i j h x=> v.door i j x h) (by positivity : 0≤ 3*p) he (fun i j=>?_)
 refine ⟨measurable_of_countable _,p,2*p,h,by positivity,by linarith,(u · i j),fun x y e=>?_⟩; dsimp only [Atmos.discrete]; split
 next h=> rw [v.lock _ _ _ h,sub_self,norm_zero,mul_zero]
 next h=> exact (norm_sub_le ..).trans ((add_le_add (u ..) (u ..)).trans_eq (by ring))
end Balls

variable {Y:ℕ→ Board X I J E}{W:Board X I J E}
lemma finance [CompleteSpace E] {p:ℕ→ℝ} (h:Summable p)(ha:0≤a)(u:∀ i,Show O F G (Y i) a (p i))(hp:∀ i,0≤p i)(eq: ∀ x i j, W x i j=∑' n,Y n x i j): Show O F G W a (∑' i,p i) := by
 choose U V hv h1 h2 h3 h4 using fun i=>(u i).presents
 let z(T:Finset A):= Real.exp (a*T.card); have hz(T):1 ≤ z T:= Real.one_le_exp (by positivity); have hp (n T i j):0≤U n T i j:= (hv n T i j).price
 have ht(n T i j):z T*U n T i j≤p n:=by
    have he(T:Finset A)(j:J):0≤z T*U n T i j:= mul_nonneg (zero_le_one.trans (hz T)) (hp ..)
    exact ((single_le_sum (f:=fun T=> z T*U n T i j) (fun i _=>he i j) (mem_univ T)).trans (single_le_sum (f:=fun j=> ∑ T,z T*U n T i j) (fun i _=> sum_nonneg (fun j _=> he j i)) (mem_univ j))).trans (h3 n i)
 have hs(T i j):Summable (fun n=> U n T i j):= h.of_nonneg_of_le (fun n=>hp ..) (fun n=> le_trans (le_mul_of_one_le_left (hp ..) (hz T)) (ht n T i j))
 let f(T:Finset A):= of fun (i:I) (j:J)=>∑' n,U n T i j; constructor; refine ⟨f,fun T=> of (fun i j x=>∑' n,V n T i j x),fun _ _ _=> Rent.series (fun _=> hv ..) (hs ..),fun T i j H=>?_,fun i j=>?_,fun i=>?_,fun i=>?_⟩
 · by_contra H'; apply H; have h(n):U n T i j=0:=by contrapose H'; exact h1 n T i j H'
   simp only [f,of_apply,h,tsum_zero] -- tune
 · ext1 x; have he(n): Y n x i j=∑ T,V n T i j x:=by simpa using congrFun (h2 n i j) x
   simp only [Finset.sum_apply,Matrix.of_apply]; rw [eq]; simp_rw [he]; exact Summable.tsum_finsetSum fun T _=> Summable.of_norm_bounded (hs T i j) (fun n=> (hv n T i j).exact_bound x)
 all_goals
  unfold f; simp only [Matrix.of_apply]; simp_rw [←tsum_mul_left]
 · let Z(n)(j):=∑ T:Finset A,z T * U n T i j; have he(j):HasSum (fun n=>Z n j) _:=hasSum_sum (s:=Finset.univ) (a:=fun T=> ∑' n,z T *U n T i j) (fun T _=> ((hs T i j).mul_left (z T)).hasSum); exact hasSum_le (h3 · i) (hasSum_sum (fun j _=>he j)) h.hasSum -- tune
 let Z(n)(j):=∑ T:Finset A,z T * U n T j i; have he(j):HasSum (fun n=>Z n j) _:=hasSum_sum (s:=Finset.univ) (a:=fun T=> ∑' n,z T *U n T j i) (fun T _=> ((hs T j i).mul_left (z T)).hasSum); exact hasSum_le (h4 · i) (hasSum_sum (fun j _=>he j)) h.hasSum
end YM.CF.BProof.Prox.Show
