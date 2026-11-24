import YM.CF.Phase.Substitute

/-! Matrix-derived exponent terms before averaging. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {e : ℝ}
abbrev Eck (m B : Side) (S : Stamp m B) := Element (slotK (CSide m B)) S
def hsun (z:ℂ) : ℂ := (↑(z.re/4) : ℂ)
def dimP (m B : Side) (f : Post m B→ℂ) (v : Hub m) (x : Pack m B) : ℂ := hsun (accessK m B (stick 0) (stick 0) v x.1 (slot m x.2) f)
def dateB (B : Side) (i : ℕ) : Sq := increment B i (stick 0) (stick 1)
def glow (m B : Side) (f : Post m B→ℂ) (v : Hub m) (U : Skin m B) (x y : Cue m) (i : ℕ) := (accessK m B (dateB B i) (dateB B (i+1)) v U (twin m x y) f) / 2
def inks (m B : Side) (f : Post m B→ℂ) (v : Hub m) (t : Tide m B) := ∑ i∈range (way B), (glow m B f v t.1.1.1 t.1.2 t.2 i-glow m B f v t.1.1.1 t.1.1.2 t.2 i)

variable {S : Stamp m B} {w : ℝ} {f : Post m B→ℂ} (h : Eck m B S w f) (b : Room B e)
include b
lemma dark0 (v : Hub m) {t} (g:t∈payer m B e) : TenantK (stationP m B (stick 0) (stick 0) v t.1 (slot m t.2)) := by
  have he := stick_in (0:Row) (mem_singleton_self _); exact drives b g.1 (show Verified _ _ margin _ _ {0} from g.2) he he (by rw [sub_self,norm_zero]; positivity) v
lemma darkL (v : Hub m) (f : Post m B→ℂ) (g : Continuous f) : ContinuousOn (dimP m B f v) (payer m B e) := by
  let F := fun t:Pack m B=> (t.1,slot m t.2)
  let D := fun t:FlagU m B=> accessK m B (stick 0) (stick 0) v t.1 t.2 f
  let Y := banner m B e {0}; have hk : Continuous F := continuous_fst.prodMk ((slot_cont m).comp continuous_snd)
  have he : stick (0:Row)∈zone {0} := stick_in _ (mem_singleton_self _)
  have H : ContinuousOn D Y := access_cont Y _ _ _ f g (fun t p=> drives b p.1 p.2 he he (by rw [sub_self,norm_zero]; positivity) v) (dress _ _ _ he he v b)
  have hp : Continuous hsun := Complex.continuous_ofReal.comp (Complex.continuous_re.div_const _)
  exact hp.comp_continuousOn (H.comp hk.continuousOn (show Set.MapsTo F (payer m B e) Y from fun _ a=>a))
abbrev Knot : Zone := insert 1 {0}
omit b in
lemma day_in (B : Side) (i : ℕ) (h : i≤way B) : dateB B i∈zone Knot := inc_in (stick_in _ (show (0:Row)∈Knot by simp [Knot])) (stick_in _ (show (1:Row)∈Knot by simp [Knot])) B h
omit b in
lemma day_gap (B : Side) (i : ℕ) : ‖dateB B (i+1)-dateB B i‖≤2/(way B:ℝ) := inc_gap (stick_in _ (show (0:Row)∈Knot by simp [Knot])) (stick_in _ (show (1:Row)∈Knot by simp [Knot])) B i
lemma gear0 {U : Skin m B} (v : Hub m) {x z : Cue m} (g : Guard U e) (h : EdgeP m B U x z) (i : ℕ) (he : i < way B) : TenantK (stationP m B (dateB B i) (dateB B (i+1)) v U (twin m x z)) := drives b g (show Verified _ _ _ _ _ Knot from h) (day_in B i he.le) (day_in B (i+1) he) (day_gap B i) _
lemma day_cont (v : Hub m) (f : Post m B→ℂ) (g : Continuous f) (i : ℕ) (h:i < way B) : ContinuousOn (fun p:Skin m B×Cue m×Cue m=> glow m B f v p.1 p.2.1 p.2.2 i) (Ear m B e) := by
  let F := fun p:Skin m B×Cue m×Cue m=> (p.1,twin m p.2.1 p.2.2)
  let D := fun t:FlagU m B=> accessK m B (dateB B i) (dateB B (i+1)) v t.1 t.2 f
  let Y := banner m B e Knot; have hk : Continuous F := continuous_fst.prodMk ((twin_cont m).comp continuous_snd)
  have H : ContinuousOn D Y := access_cont Y _ _ _ _ g (fun t p=>drives b p.1 p.2 (day_in B _ h.le) (day_in B _ h) (day_gap B _) v) (dress _ _ _ (day_in B _ h.le) (day_in B _ h) v b)
  exact (H.comp hk.continuousOn (show Set.MapsTo F (Ear m B e) Y from fun _ a=>a)).div_const _
lemma shoneCont (v : Hub m) (f : Post m B→ℂ) (g : Continuous f) : ContinuousOn (inks m B f v) (checked m B e) := by
  apply continuousOn_finsetSum; intro i hi
  let F := fun t:Tide m B=>(t.1.1.1,t.1.2,t.2); let Y := fun t:Tide m B=>(t.1.1.1,t.1.1.2,t.2); let A := fun t:Skin m B×Cue m×Cue m=>glow m B f v t.1 t.2.1 t.2.2 i
  have H : ContinuousOn A _ := day_cont b v f g i (mem_range.mp hi)
  change ContinuousOn (fun i:Tide m B=>(A ∘ F) i-(A ∘ Y) i) _
  exact (H.comp (show Continuous F by unfold F; fun_prop).continuousOn (fun t h=> ⟨h.1.1.1,h.2.2⟩)).sub (H.comp (show Continuous Y by unfold Y; fun_prop).continuousOn (fun t h=>⟨h.1.1.1,h.2.1⟩))
omit b in
lemma sun_n (z:ℂ) : ‖hsun z‖≤ ‖z‖ := by
  unfold hsun; rw [Complex.norm_real,norm_div]; norm_num [Real.norm_eq_abs]; linarith [Complex.abs_re_le_norm z, norm_nonneg z]
omit b in
lemma sun_e (z t : ℂ) : hsun z-hsun t=hsun (z-t) := by unfold hsun; simp [sub_div]
include h
lemma dark_size {x:Pack m B} (g:x∈payer m B e) (v : Hub m) : ‖dimP m B f v x‖≤w := by
  rw [dimP,entrance (dark0 b v g)]; exact (sun_n _).trans (h.norms _)
lemma shine_price (v : Hub m) {U x z} (g : Guard U e) (e : EdgeP m B U x z) (i : ℕ) (hi:i < way B) :
    ‖glow m B f v U x z i‖≤w/2 := by
  rw [glow,entrance (gear0 b v g e i hi),norm_div]; norm_num; exact div_le_div_of_nonneg_right (h.norms _) (by norm_num)
lemma irradiates (v : Hub m) : Cargo (inks m B f v) e ((way B:ℝ)*w) := by
  refine ⟨fun t g=>?_, shoneCont b v f h.continuousE⟩
  apply (norm_sum_le ..).trans; apply (sum_le_sum (fun i l=>?_)).trans (show (∑ i∈range (way B), w)≤_ by simp)
  exact (norm_sub_le ..).trans ((add_le_add (shine_price h b v g.1.1.1 g.2.2 i (mem_range.mp l)) (shine_price h b v g.1.1.1 g.2.1 i (mem_range.mp l))).trans_eq (add_halves w))
lemma dark_g (v : Hub m) {t} (g:t∈payer m B e) (p) : dimP m B f v (Lattice.gauge p t.1,partner m B p t.2)=dimP m B f v t := congrArg hsun (exact_station f _ _ v t.1 _ p (dark0 b v g) (fun x g=> h.gauge g x))
lemma light_g (v : Hub m) {u x y} (H : ((u,x),y)∈checked m B e) (p) : inks m B f v (((Lattice.gauge p u.1,partner m B p u.2),partner m B p x),partner m B p y)=inks m B f v ((u,x),y) := by
  apply sum_congr rfl; intro i hi
  have he z (l:EdgeP m B u.1 z y) : glow m B f v (Lattice.gauge p u.1) (partner m B p z) (partner m B p y) i=glow m B f v u.1 z y i := by
    unfold glow; rw [twin_g, exact_station f _ _ v _ _ p (gear0 b v H.1.1.1 l i (mem_range.mp hi)) (fun x g=>h.gauge g x)]
  exact congrArg₂ (· - ·) (he x H.2.2) (he u.2 H.2.1)
lemma dark_local (v : Hub m) (p:sanctioned m B S v) {x y:Pack m B} (g:x∈payer m B e) (k:y∈payer m B e) (e : AgreeF (chairs m B S) x.2 y.2) (l : Agrees (window m B S v) x.1 y.1) : dimP m B f v x=dimP m B f v y := congrArg hsun (access_eq S h v p (dark0 b v g) (dark0 b v k) l (fun i hl=> e i.1 (mem_product.mp hl).1))
lemma light_local (v : Hub m) (p:sanctioned m B S v) {x y:Tide m B} (g:x∈checked m B e) (k:y∈checked m B e) : let K := chairs m B S; AgreeF K x.1.2 y.1.2 → AgreeF K x.2 y.2 → AgreeF K x.1.1.2 y.1.1.2 → Agrees (window m B S v) x.1.1.1 y.1.1.1 → inks m B f v x = inks m B f v y := by
  intro K p₁ p₂ p₃ p₄; apply sum_congr rfl; intro i hi
  let U := x.1.1.1; let W := y.1.1.1; have e := mem_range.mp hi
  have he X Y (t : EdgeP m B U X x.2) (L : EdgeP m B W Y y.2) (m' : AgreeF K X Y) : glow m B f v U X x.2 i=glow m B f v W Y y.2 i := by
    unfold glow; apply congrArg (·/2); refine access_eq S h v p (gear0 b v g.1.1.1 t i e) (gear0 b v k.1.1.1 L i e) p₄ ?_; intro j hl; unfold twin capRow; split
    · exact p₂ j.1 (mem_product.mp hl).1
    exact m' j.1 (mem_product.mp hl).1
  exact congrArg₂ (· - ·) (he _ _ g.2.2 k.2.2 p₁) (he _ _ g.2.1 k.2.1 p₃)
end YM.CF.Phase
