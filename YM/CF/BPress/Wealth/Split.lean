import YM.CF.BPress.Ledger
import YM.Push.SECTOR_MEASURE.Bounds
import YM.CF.BPress.Wealth.Groves
import YM.Push.LOCAL_SPLITTING.Orientation
import YM.Work.F05.Actions
import YM.Vac.Caps
/-!
True gauge charge split: eq:B-kept, direct, weak atoms and both-leg pairs. Same pair of locations of each real term; other than summing real orientations per direct term, don't move locations yet. Provide both per-unit price & actual decomposition before moving factors into marks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Push.Local ConnectedActivityE6.Raw Work.F05
variable {G : Gauge}{s:Side} (d : Clip) (p : BudgetPoint) (R : PathData G) (β : ℝ) (M : ℕ)
attribute [local instance] Gauge.frobInner
local notation "F" => Face (Per s)
local notation "ch" => Signed

-- direct on ORIGINAL orientation
abbrev hideH (U : Config G s)(x : F) := PathData.clipped d p.threshold (G.chord (faceValue U x))
def hide (U : Config G s)(x : F) := β * hideH d p U x
lemma h_conj (x : F) : GaugeInvariant fun U: Config G s=> hide d p β U x:=fun t U=>by simp only [hide,hideH,face_gauge,Gauge.chord_conj]
lemma h_borel (x : F) : Measurable fun U: Config G s=> hide d p β U x:= measurable_const.mul (PathData.clip_env ..).meas
lemma h_local (x : F): LocalOn (touched x) fun U: Config G s=> hide d p β U x:= by intro U V h; exact congrArg (fun z => β * PathData.clipped d p.threshold (G.chord z)) (travel_local x.1 _ U V (fun i a b=> h i (List.mem_toFinset.mpr a) (List.mem_toFinset.mpr b)))
lemma h_pos (x:F)(h : 0≤β) (U : Config G s): 0≤ hide d p β U x:= by
 apply mul_nonneg h; have hp:= p.threshold_pos; have hv:= d.tail_pos; have ht:= d.quadratic_pos; have hh:= G.chord_nonneg (faceValue U x); unfold hideH PathData.clipped; split <;> positivity
lemma h_cap (x:F)(h : 0 ≤ β)(U:Config G s): hide d p β U x ≤ β*(2*d.direct+2*d.linear):=by
 apply mul_le_mul_of_nonneg_left _ h; let t:=G.chord (faceValue U x); have hp:=d.tail_pos; have ht:=d.quadratic_pos; have hh:0≤t:=G.chord_nonneg _; have hz:t ≤2:=G.chord_le_two _; unfold hideH PathData.clipped; split
 · change d.direct*t^2/2 ≤ _; have hv:t^2≤4:=by nlinarith
   nlinarith [mul_le_mul_of_nonneg_left hv ht.le]
 change d.linear* _*t ≤ _; have hv:p.threshold ≤1:=p.threshold_le; nlinarith [mul_le_mul_of_nonneg_left hv (mul_nonneg hp.le hh)]
lemma count_dir (U:Config G s)(a:ch) : ∑ x:F, hide d p β (pull a 0 U) x= ∑ x:F, hide d p β U x:=by
 let i:= Face.send a (0:Site s); have he: Bijective i:= (Finite.injective_iff_bijective).mp (Face.injective_send _ _); let E:=Equiv.ofBijective i he; rw [←Equiv.sum_comp E (hide d p β U)]; apply sum_congr rfl; intro j _; unfold hide hideH; rw [show G.chord _= _ from Face.send_price U j a 0 G.chord G.chord_inv (fun x g=> G.chord_conj g x)]; rfl

-- units. channel root lives in the native pull coordinates for kept charges
def chPrice : ℝ:= (Fintype.card Signed:ℝ)⁻¹
lemma chPrice_pos : 0<chPrice:= by unfold chPrice; positivity
-- use Γ alphabet
abbrev unitR (U:Config G s) (x:F) := Pressure.shorten R M 1 U x
def keepR (U:Config G s)(x:F) := if PathData.kept d p.threshold x.1 U then ‖unitR R M U x‖^2/2 else 0
def kept (σ :ch) (U:Config G s)(x:F) := chPrice*β * keepR d p R M (pull σ 0 U) x
variable (U V : Config G s)
lemma kept_budget (x:F)(h:0 ≤ β)(σ:ch): 0 ≤ kept d p R β M σ U x:=by unfold kept keepR; split <;> positivity [chPrice_pos]
lemma enough_p (k:Site s→ G.El) (x:F) (T : Clip) (t:ℝ) : PathData.kept T t x.1 (gauge k U) = PathData.kept T t x.1 U:=by simp only [PathData.kept, face_gauge,Gauge.chord_conj] -- tune k

variable (a : ch)
def photo (X : Support s) := X.image (turnSites a 0)
def box (x : Site s) := halo (M+2) {x}
lemma halo_photo (x : Site s) (t:ℕ) : photo a (halo t {x})= halo t {a.act x}:=by
 unfold photo; rw [←halo_map, Finset.image_singleton]; simp [turnSites, Signed.actEquiv]; intro i j; exact turn_sep ..
lemma photo_g (x : Support s)(h:Grove (Grid.field 4 s) x): Grove (Grid.field 4 s) (photo a x):=by
 induction h with|single=>rw [photo,image_singleton]; exact Grove.single _|join _ t q ih=> rw [photo,image_insert]; exact Grove.join ih (mem_image_of_mem _ t) (turn_sep .. |>.le.trans q)
-- kept LOCAL at the price, magnitude & meas, and invariant. pick stride threshold Kn test exactly stipulated.
def Checks (M : ℕ)(p : BudgetPoint)(c: Clip): Prop:= ∀ k:ℕ, p.threshold*Real.exp (k/c.relaxation) <2 → k+2≤M+2
variable {M d p} {σ C Λ:ℝ}

lemma unit_agrees (x:F)(e:Agrees (box M x.1) U V): unitR R M U x=unitR R M V x:=by
 apply tsum_congr; intro i; unfold Pressure.shortenTerm; split; next t=>
    refine congrArg ((R.row x.2 i).1 • ·) (slot_local (R.row x.2 i).2 x.1 U V ?_); refine agrees_mono e (fun y v=> halo_spec.mpr ?_); obtain ⟨j,q,g⟩:= halo_spec.mp ((foot_limit ..).2.2.1 (show y∈foot x.1 (R.row x.2 i).2 from v)); refine ⟨j,q,g.trans ?_⟩; omega
 next=> rfl
lemma keep_local (x:F)(h:Checks M p d): LocalOn (photo a (box M x.1)) (fun U=> kept d p R β M a U x) := by
 intro U V g; let x':= agrees_pull _ _ g; have hp:= kept_agrees d p.threshold _ x.1 (pull a 0 U) (pull a 0 V) h x'; unfold kept keepR; dsimp only; rw [hp]; split; rw [unit_agrees R _ _ x x']; rfl
lemma keep_invariant (x:F)(h:R.Bounds d σ C Λ) : GaugeInvariant (fun U=>kept d p R β M a U x):=by
 intro k U; let g:=(fun i : Site s=> k (Lattice.affine a 0 i)); let V:= pull a 0 U; let L:= (G.adjoint (g x.1)).toContinuousLinearMap; let W:=gauge g V
 have he (U):= (R.ell_dominated h x).summable U
 have hv: unitR R M W x=L (unitR R M V x):=by
    have hu : Summable (fun i=> Pressure.shortenTerm R M 1 V x i):= by
       refine Summable.of_norm_bounded (he V).norm ?_; intro i; unfold Pressure.shortenTerm; split; rfl; rw [norm_zero]; exact norm_nonneg _
    refine Eq.trans ?_ (L.map_tsum hu).symm; apply tsum_congr; intro i; unfold Pressure.shortenTerm; split; next=> rw [PathData.ellTerms,PathData.ellTerms,map_smul]; rw [show (R.row x.2 i).2.atSite W x.1=_ from slot_gauge ..]; rfl
    next=> exact (L.map_zero).symm
 unfold kept keepR; dsimp only; rw [pull_gauge_zero,enough_p (pull a 0 U) g x]; change chPrice * β * (if PathData.kept d p.threshold x.1 V then ‖unitR R M W x‖^2/2 else 0)=_; split; rw [hv, show ‖L _‖=_ from G.norm_adjoint (g x.1) _]; rfl -- tune
lemma keep_meas (x:F) (h:R.Bounds d σ C Λ) : Measurable fun U=> kept d p R β M a U x := measurable_const.mul ((Measurable.ite (PathData.kept_closed .. |>.measurableSet) (((Push.SectorMeasure.shorten_cont h ..).measurable.norm.pow_const 2).div_const _) measurable_const).comp (continuous_pull ..).measurable) -- tune
lemma unit_cap (h:R.Bounds d σ C Λ)(x:F) : ‖unitR R M U x‖ ≤ 2*C:=by
 have hb:= budget_scale (zero_le_two (α:=ℝ)) (h.rows x.2); let f(i):=‖Pressure.shortenTerm R M 1 U x i‖; have p : SumBudget f (2*C):=by
   refine budget_mono hb (fun _=> norm_nonneg _) ?_; intro i; unfold f Pressure.shortenTerm; split; next=> have h0:= (h.rows x.2).2.1; refine le_trans ?_ (mul_comm (2:ℝ) _ |>.symm.le); rw [PathData.ellTerms,norm_smul]; apply mul_le_mul ?_ (Slot.eval_norm ..) (norm_nonneg _) (by positivity); exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity [h.width]))
   next=> rw [norm_zero]; exact hb.1 i -- tune `exact ?_`
 exact (norm_tsum_le_tsum_norm p.2.1).trans p.2.2
lemma keep_cap (h:R.Bounds d σ C Λ)(v:0≤β)(x:F) : kept d p R β M a U x ≤ chPrice * β *((2*C)^2/2):= by
 unfold kept keepR; split; have hu : 0≤chPrice*β:=by positivity [chPrice_pos]
 gcongr; exact unit_cap R _ h _; rw [mul_zero]; positivity [chPrice_pos]
-- equality splitting kept tail `pair_sum` in E6 path
lemma unit_split (U:Config G s)(x:F): β * R.baseTerm d p U x= hide d p β U x + β* keepR d p R M U x+ β* tails R d M 1 p.threshold x U:=by
 unfold PathData.baseTerm hide hideH tails keepR unitR; split <;> ring
lemma separate (U:Config G s): R.inChannels d p β U= ∑ x:F, hide d p β U x +
    ∑ z:ch, (∑ x:F, kept d p R β M z U x)+ ∑ z:ch, ( chPrice*β*(∑ x:F, tails R d M 1 p.threshold x (pull z 0 U)) +
    chPrice* ∑ o:Site s, (β*(PathData.atomSeries R.cubic p (pull z 0 U) o + PathData.atomSeries R.quartic p (pull z 0 U) o) + PathData.atomSeries R.loop p (pull z 0 U) o)) := by
 unfold PathData.inChannels PathData.principal kept;
 have he (a:ch)(V:Config G s) : β * (∑ x:F,R.baseTerm d p V x)= (∑ x:F,hide d p β V x) + β * (∑ x:F,keepR d p R M V x) + β * (∑ x:F, tails R d M 1 p.threshold x V):=by rw [mul_sum]; simp_rw [unit_split R β (M:=M), sum_add_distrib,mul_sum]
 simp only [mul_add (a:=β), he 1,count_dir,←mul_sum,sum_add_distrib]; unfold chPrice; simp only [sum_const,card_univ, nsmul_eq_mul]; field_simp
 ring -- inspect
end YM.CF.BPress.Wealth
