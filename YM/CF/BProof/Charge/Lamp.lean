import YM.CF.BProof.Charge.Pair
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.FiniteStack

/-! Heavy scalar primitives. Kept terms indexed by physical center and the other two
indices, not the natural channel base. `shorten_data` gives a finite formula even for
row requiring analytic path.Bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Push.AbsoluteSums Work Micro Moment MeasureTheory ConnectedActivityE6.Raw Pressure Next.SectorChange AnalyticBridge.SectorAffine -- Bill names ambiguous
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side} {G:Gauge} (c:Clip)(p:BudgetPoint)(T:PathData G)(M:ℕ)(σ: Signed)(β:ℝ)(U : Config G s){t W C Λ:ℝ}

abbrev Lam (s:Side) := Signed × PlaqAxes × Site s
-- µ=(σ,i,o) with o in physical lattice coords
abbrev Lam.center (a:Lam s):= a.2.2
def ref (a:Lam s) : Cell s:= ((Micro.equiv a.1).symm a.center,a.2.1)
def lRead := pull σ 0 U
def share : ℝ := (Fintype.card Signed :ℝ)⁻¹
lemma share_pos : 0<share:=by unfold share; positivity
lemma share_le : share≤1:=inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos (α:=Signed))

def directQ (x:Cell s) := β*PathData.clipped c p.threshold (G.chord (faceValue U x))
def higher (a:Lam s) := β*share * trunk T c M 1 p.threshold (lRead a.1 U) (ref a)
variable (h:T.Bounds c W C Λ)
include h
lemma shorten_data (x:Cell s) : shorten T M 1 U x = ∑ i∈ Stack.allShort M, Stack.grouped T x.2 i • i.atSite U x.1:=by
 rw [←barrel_term,Stack.finite_price x M _ _ h]; simp_rw [Work.F03.atSite_path]
lemma grouped_cost (a:PlaqAxes): ∑ i∈Stack.allShort M,|Stack.grouped T a i| ≤ C:=by
 apply le_trans _ (Stack.grouped_le (Stack.allShort M) h a); refine sum_le_sum (fun i _=> le_mul_of_one_le_right (abs_nonneg _) ?_); exact Real.one_le_exp (mul_nonneg h.width.le (by positivity))
lemma shorten_local (x:Cell s): LocalOn (↑(halo M {x.1})) (fun U=>shorten T M 1 U x):=by
 intro U V hx; dsimp only; rw [shorten_data c T M U h,shorten_data c T M V h]; refine sum_congr rfl fun i hi=>?_; congr 1; exact slot_local i x.1 U V (agrees_mono hx (Finset.coe_subset.mpr (lives_sub _ _ ((Stack.short_iff ..).mp hi)))) -- tune
lemma shorten_price (x:Cell s) : ‖shorten T M 1 U x‖≤C*2:=by rw [shorten_data c T M U h]; apply (norm_sum_le ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right (grouped_cost c T M h x.2) (by norm_num : 0≤(2:ℝ))); rw [sum_mul]; exact sum_le_sum fun i _=> (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (Slot.eval_norm i _) (abs_nonneg _))

lemma shorten_gauge (x:Cell s)(g:Site s→G.El): shorten T M 1 (Lattice.gauge g U) x= G.adjoint (g x.1) (shorten T M 1 U x):=by rw [shorten_data c T M _ h, shorten_data c T M _ h]; simp only [map_sum,map_smul,F05.slot_gauge]
lemma shorten_c (x:Cell s): Continuous (fun U:Config G s=> shorten T M 1 U x):=by simp_rw [shorten_data c T M _ h]; unfold Slot.atSite expandAt; fun_prop

variable (k:ValidR c p M)
lemma higher_local (a:Lam s)(k:ValidR c p M): LocalOn (halo (M+2) {a.center}) (fun U=> higher c p T M β U a):=by
 let q:=ref a; have eq: a.1.act q.1=a.center:= (Micro.equiv (s:=s) a.1).apply_symm_apply _
 intro U V hv; let R:=halo (M+2) {q.1}; have hg:Agrees R (lRead a.1 U) (lRead a.1 V):= Micro.agrees_turn a.1 R U V (show Agrees (↑(move a.1 R)) U V from by unfold R; rw [Micro.move_halo,Micro.spin,eq]; exact hv)
 let x:=p.threshold; have h':= kept_agrees c p.threshold (M+2) q.1 _ _ k hg; dsimp only; unfold higher trunk; rw [h']; split; rw [show shorten T M 1 (lRead a.1 U) (ref a)=shorten T M 1 (lRead a.1 V) (ref a) from shorten_local c T M h q _ _ (agrees_mono hg (Finset.coe_subset.mpr (Corona.halo_mono (by omega) (Finset.Subset.refl _))))]; rfl -- tune
lemma higher_c (a:Lam s): Measurable (fun U=>higher c p T M β U a):=by
 let P (X: Cell s):= fun U:Config G s=> trunk T c M 1 p.threshold U X
 have ht(i):Measurable (P i):= ( (((shorten_c c T M h i).norm.pow 2).div_const 2).measurable).ite (PathData.kept_closed .. |>.measurableSet) measurable_const
 exact measurable_const.mul ((ht (ref a)).comp (continuous_pull ..).measurable)
lemma higher_g (a:Lam s) (g:Site s→ G.El): higher c p T M β (Lattice.gauge g U) a=higher c p T M β U a:=by
 let v := fun x=>g (affine a.1 0 x); let x:=ref a; unfold higher lRead; rw [F05.pull_gauge_zero]; have hh:PathData.kept c p.threshold x.1 (Lattice.gauge v (pull a.1 0 U))=PathData.kept c p.threshold x.1 (pull a.1 0 U):=by unfold PathData.kept; simp only [face_gauge,G.chord_conj]
 unfold trunk; rw [hh]; split; rw [shorten_gauge c T M _ h,G.norm_adjoint]; rfl -- semis

lemma higher_cost (a:Lam s)(v:0≤β): higher c p T M β U a≤ β*share*((C*2)^2/2):=by unfold higher trunk; have ht:=share_pos; split; gcongr; apply shorten_price c T M _ h; rw [mul_zero]; positivity
omit h
lemma higher_pos (a:Lam s)(v:0≤β) : 0≤higher c p T M β U a:=by unfold higher trunk; split<;>have :=share_pos<;> positivity
lemma direct_pos (x:Cell s)(v:0≤β): 0≤directQ c p β U x:=by unfold directQ PathData.clipped; have ht:= c.quadratic_pos; have he:=p.threshold_pos; have hv:=c.tail_pos; have := G.chord_nonneg (faceValue U x); split <;> positivity
lemma direct_c (x:Cell s) : Measurable (fun U:Config G s=>directQ c p β U x):= measurable_const.mul (PathData.clip_env p x (c:=c) (G:=G)).meas
lemma direct_g (x:Cell s)(g:Site s→G.El) : directQ c p β (Lattice.gauge g U) x=directQ c p β U x:=by simp [directQ]
lemma direct_here (x:Cell s) : LocalOn (↑(RG.touched x)) (fun U:Config G s=>directQ c p β U x):= fun U V h=> by dsimp only; unfold directQ; rw [show faceValue U x=faceValue V x from travel_local _ _ _ _ (agrees_mono h (fun i hi=> List.mem_toFinset.mpr hi))]
lemma direct_cost (x:Cell s)(v:0≤β)(h:p.threshold≤ 1): directQ c p β U x ≤ β*(c.direct*2):=by
 have hp:=G.chord_nonneg (faceValue U x); have hx:= G.chord_le_two (faceValue U x); have h1:= c.tail_pos; have h2:= c.kink; have he:=p.threshold_pos
 unfold directQ PathData.clipped; refine mul_le_mul_of_nonneg_left ?_ v; split; apply le_trans (b:=c.direct*(2:ℝ)^2/2) (by gcongr; have := c.quadratic_pos; positivity) (le_of_eq (by ring)); apply le_trans (b:=c.linear*1*2) (by gcongr); linarith
end YM.CF.BProof.Charge
