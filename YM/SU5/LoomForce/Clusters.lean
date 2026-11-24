import YM.SU5.LoomForce.AppointmentBooks
/-! Ordered, off-diagonal price payments at moving positive calendars for the
*Wake* computation in the IA.9 ancestry. -/
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Phase SU Rush Mir Reflect Lifted Window
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Shuttle Ballad Hiro Regis.Circuit
open YM.Stationary (Gaia)
open scoped Topology ContDiff BigOperators ENNReal InnerProductSpace Classical
local notation "F₀" => Prototype.goldF
local notation "WZ_" u:max => wakeZ (fun _=>pairMood) u
local notation "WG_" u:max => wakeG u (fun _=>F₀)

private lemma barClock (x:Gaia) (p:x≠0) :
    ‖Maxwell.bareCurl 0 1 0 1 x‖ ≤ (4*Maxwell.normal+2* (8*Maxwell.normal))*‖x‖⁻¹^4 := by
  have he:=Maxwell.normal_pos; have hh := norm_pos_iff.mpr p
  let u:= ‖x‖; have ht(i:Axis):0 ≤ x i*x i∧x i*x i ≤ u^2:=by
    rw [←sq]; exact ⟨sq_nonneg _, (by nth_rw 1 [←sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (PiLp.norm_apply_le (p:=2) x i) _)⟩
  let A(i:Axis):= 8*Maxwell.normal*(x i*x i)*(u^2)⁻¹^3
  let U:=(u^2)⁻¹^2; let κ:=Maxwell.normal
  have hv0 : 0 < U:= by unfold U u; positivity
  have hv(i:Axis):0≤A i∧ A i≤ 8*κ*U:= by
    obtain ⟨h,a⟩:=ht i
    unfold A; have ht:0<u:=hh
    constructor; · positivity
    calc _ ≤ 8*Maxwell.normal*u^2*(u^2)⁻¹^3 := by gcongr
         _ = _:=by unfold U κ; field_simp
  rw [Maxwell.bareCurl,Pi.sub_apply,Maxwell.Bare.opp_grad p, Maxwell.Bare.opp_grad p]; simp only [↓reduceIte, Maxwell.second_Green p, Real.norm_eq_abs]; norm_num -- tune leaves A
  obtain ⟨a,b⟩ := hv 0; obtain ⟨g,t⟩:= hv 1
  have hU : ‖x‖⁻¹^4=U:=by unfold U u; ring -- pow_inv
  rw [← inv_pow ‖x‖ 4,hU]; unfold A at a b g t; unfold u at a b g t; simp_rw [inv_pow] at a b g t
  unfold κ at b t; unfold U u at *; simp only [inv_pow] at *; rw [abs_le]; constructor <;> linarith

private lemma farCurl (x:ℕ→ Gaia) (p:Tendsto (fun i=> ‖x i‖) atTop atTop) :
    Tendsto (fun i=> specter F₀ F₀ (x i)) atTop (𝓝 0) :=by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let g:= ((4*Maxwell.normal+2*(8*Maxwell.normal)))
  have he:=((tendsto_inv_atTop_zero.comp p).pow 4).const_mul g; rw [zero_pow (by decide), mul_zero] at he
  refine squeeze_zero' (Eventually.of_forall (fun i=>norm_nonneg _)) (?_) he
  filter_upwards [p.eventually_gt_atTop 0] with i t; unfold specter; rw [Complex.norm_real]; exact barClock _ (norm_pos_iff.mp t)

variable {I J : Type*}
private lemma wakeZ_base (u v:I→Gaia)(i j:loomZ I)(p:u i.1-u j.1=v i.1-v j.1): (WZ_ u) i j=(WZ_ v) i j :=by
  unfold wakeZ costsWith; dsimp only; rw [p, show u j.1-u i.1= v j.1-v i.1 from (by rw [←neg_sub (u i.1),←neg_sub (v i.1),p])] -- check neg_sub
private lemma wakeG_base (u v:I→Gaia)(i j:loomG I)(p:u i.1-u j.1=v i.1-v j.1): (WG_ u) i j=(WG_ v) i j :=by unfold wakeG; rw [p]
lemma inked_at (tag:I→ Sewer) (u v:I→ Gaia) (L:List I)(p:∀ i j,u i-u j=v i-v j):
    inked tag (fun _=>F₀) (fun _=>pairMood) u L= inked tag (fun _=>F₀) (fun _=>pairMood) v L := by
  unfold inked; rw [show WZ_ u=WZ_ v from funext fun i=> funext fun j=> wakeZ_base u v _ _ (p _ _), show WG_ u=WG_ v from funext fun i=>funext fun j=>wakeG_base u v _ _ (p _ _)]

private lemma offZ (Y : ℕ→ I → Gaia)(i j:loomZ I) (h: Tendsto (fun n=>dist (Y n i.1) (Y n j.1)) atTop atTop) :
    Tendsto (fun n => (WZ_ (Y n)) i j) atTop (𝓝 0) := by -- syntax
  have he (a b:ℕ → Gaia)(p:Tendsto (fun n=>dist (a n) (b n)) atTop atTop) : Tendsto (fun n=>shotL (a n-b n) pairMood pairMood) atTop (𝓝 0):= SpinReceipt.kP_further (fun n=>a n-b n) (by simp_rw [dist_eq_norm] at p; exact p)
  have hv:=he _ _ h; let q(n) := dist (Y n j.1) (Y n i.1); have hh: Tendsto q atTop atTop:=h.congr (fun _=> dist_comm ..); have h':=he (fun n=>Y n j.1) (fun n=>Y n i.1) hh
  unfold wakeZ costsWith; split_ifs <;> first| exact tendsto_const_nhds| exact hv| simp only [neg_zero]; exact tendsto_const_nhds| simpa only [neg_zero] using h'.neg
private lemma offG (Y : ℕ→ I → Gaia)(i j:loomG I) (h: Tendsto (fun n=>dist (Y n i.1) (Y n j.1)) atTop atTop) :
    Tendsto (fun n => (WG_ (Y n)) i j) atTop (𝓝 0) := by
  unfold wakeG; have hp:= farCurl (fun n=>Y n i.1-Y n j.1) (by simp_rw [dist_eq_norm] at h; exact h); simpa using hp.const_mul (↑(Regis.Head.Brecht.sch (G:=SU.group) i.2 j.2):ℂ)
variable (tag : I → Sewer) (X Y : I→ Gaia) (u v : ℕ → I → Gaia) (L : List I)
    (i : ∀ n x y,u n x-u n y=X x-X y)(j : ∀ n x y, v n x-v n y= Y x-Y y) (h : ∀ a b, Tendsto (fun n=>dist (u n a) (v n b)) atTop atTop)

private def splitsC (b : I→ Bool) (C : Chart I) : Chart I:=fun i j=> if b i=b j then C i j else 0
local notation "Q_" u:max tag:max L:max => (inked tag (fun _=>F₀) (fun _=>pairMood) u L)
include i j h
lemma clusterWake : let T:= Sum.elim tag tag; Tendsto (fun n => Q_ (Sum.elim (u n) (v n)) T (Shuttle.twins L)) atTop
    (𝓝 (Q_ X tag L * Q_ Y tag L)) := by
  intro T
  let Q : Sort _ := I⊕I
  let S(n:ℕ):= Sum.elim (u n) (v n); let s: I⊕I → Gaia := Sum.elim X Y
  let left: I⊕I → Bool:= Sum.elim (fun _=> true) (fun _=>false)
  let H:=WZ_ s; let G:=WG_ s; let D:=splitsC (left ∘ Prod.fst) H; let M:=splitsC (left ∘ Prod.fst) G
  have hm(a b : I⊕I) (t:left a=left b) : ∀ n, S n a-S n b=s a - s b := by
    rcases a with a|a<;> rcases b with b|b --
    · exact fun n=> i n a b
    all_goals first | exact fun n=> j n a b | contradiction
  have he(a b:I⊕I) (t:left a≠left b): Tendsto (fun n=> dist (S n a) (S n b)) atTop atTop := by
    rcases a with a|a<;> rcases b with b|b
    exact (t rfl).elim
    exact h a b
    exact (h b a).congr fun n=> dist_comm ..
    exact (t rfl).elim
  have ht(a b:loomZ (I⊕I)): Tendsto (fun n=> (WZ_ (S n)) a b) atTop (𝓝 (D a b)) :=by
    unfold D splitsC; dsimp only [Function.comp_apply]; split
    next x=> exact tendsto_const_nhds.congr fun n=> (wakeZ_base (S n) s a b (hm _ _ x n)).symm
    next x=> exact offZ S a b (he _ _ x)
  have hf(a b:loomG (I⊕I)): Tendsto (fun n=> (WG_ (S n)) a b) atTop (𝓝 (M a b)) :=by
    unfold M splitsC; dsimp only [Function.comp_apply]; split
    next x=> exact tendsto_const_nhds.congr fun n=> (wakeG_base (S n) s a b (hm _ _ x n)).symm
    next x=> exact offG S a b (he _ _ x)
  let p:= (List.map Sum.inl L: List (I⊕I)); let q:= (List.map Sum.inr L: List (I⊕I)); let z :ℂ := (1/2:ℂ)
  have hz:= (attend_quoted (W:=M) (WT:=fun n=>WG_ (S n)) (tag:=T) ht (p++q) ?_).const_mul (z^(p++q).length)
  swap
  · apply List.pairwise_of_forall -- name
    exact fun _ _ _ _=> hf ..
  refine Eq.subst (motive:=fun Z:ℂ=> Tendsto (fun n => Q_ (S n) T (p++q)) atTop (𝓝 Z)) (a:=(z^(p++q).length*quoted T (p++q) D M)) ?_ hz
  have hp{E:Type} (i:(I⊕I)× E) (u:i.1∈p):left i.1=true:=by obtain ⟨v,k,t⟩:= List.mem_map.mp u; rw [←t]; rfl
  have hq{E:Type} (i:(I⊕I)× E) (u:i.1∈q):left i.1=false:=by obtain ⟨v,k,t⟩:= List.mem_map.mp u; rw [←t]; rfl
  rw [quoted_factor]; rotate_left
  · intro i u j t; unfold D splitsC; simp only [Function.comp_apply,hp i u,hq j t,Bool.true_eq_false,ite_false]
  · intro i u j t; unfold M splitsC; simp only [Function.comp_apply,hp i u,hq j t,Bool.true_eq_false,ite_false]
  have ha : quoted T p D M= quoted tag L (WZ_ X) (WG_ X):=by unfold p; rw [quote_big]; rfl
  have hb : quoted T q D M= quoted tag L (WZ_ Y) (WG_ Y):=by unfold q; rw [quote_big]; rfl
  rw [List.length_append,pow_add,ha,hb,show p.length=L.length from List.length_map _,show q.length=L.length from List.length_map _]; unfold inked z; ring
#print axioms clusterWake
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
