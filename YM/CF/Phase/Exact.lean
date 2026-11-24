import YM.CF.Phase.LocalBills

/-! Actual assigned scalar and correction, before symmetry averaging. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Sample
open Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {S : Stamp m B} {t : Part m B} {W : Scroll m B t}

lemma populated {Y : Type*} [DecidableEq Y] {t : Branch.Field Y} {T : Seal Y} (h : Branch.Grove t T) : Finset.Nonempty T := by
  induction h with
  | single=> simp
  | join _ _ _ _=> simp
def Budget (B : Side) (e c : ℝ) := Room B e ∧ 0≤c ∧ ∀ (m:Side) (U:Skin m B), Guard U e → ∀ (A:ArrayF m) (r : Zone) (x y : Sq), Verified m B margin U A r→x∈zone r→y∈zone r→∀ S:Stamp m B,S.card≤ B.val →∀ a, sanctioned m B S (some a) → vacancy S (touch m B x y U A) (flipR (aligner a U) (twinR m B a x y U A))≤c
-- Scaled gap estimates
section
variable {e c : ℝ} (b : Budget B e c) {a : Index m} (H:sanctioned m B S (some a)) (p:S.card≤B.val)
include b H p
lemma exposed {f : Post m B→ℂ} {w : ℝ} (l:Eck m B S w f) {U A i j r} (h:Guard U e) (g:Verified m B margin U A r) (x:i∈zone r) (y:j∈zone r) (hv : ‖j-i‖≤2/(way B:ℝ)) :
    ‖accessK m B i j none U A f-accessK m B i j (some a) U A f‖ ≤ w*c := by
  let G : Post m B := ⟨_, drives b.1 h g x y hv none⟩
  let P : Post m B := ⟨_, drives b.1 h g x y hv (some a)⟩
  rw [entrance (drives b.1 h g x y hv none), entrance (drives b.1 h g x y hv (some a))]; change ‖f G-f P‖≤_
  let k := aligner a U
  rw [←show f (toss k P)=f P from l.gauge k P]; exact (l.varies G (toss k P)).trans (mul_le_mul_of_nonneg_left (b.2.2 m U h A r i j g x y S p a H) l.posT)
lemma deviation {d K : ℝ} {t : Part m B} {W : Scroll m B t} (h : ScaleK d K W) {x} (g:x∈payer m B e) :
    ‖W.value S none x-W.value S (some a) x‖≤W.mint S*c := by
  let F := inks m B (W.phi S) none; let J := inks m B (W.phi S) (some a)
  have hl := h.t2.stamped S
  have hk (t:Tide m B) (v:t∈checked m B e) : ‖F t-J t‖≤(way B:ℝ)*W.din S*c := by
    let r := W.din S*c
    let U := t.1.1.1; let y := t.2; let f := W.phi S
    have hg x (g:EdgeP m B U x y) (i : ℕ) (k:i<way B) : ‖glow m B f none U x y i-glow m B f (some a) U x y i‖≤ r/2 := by
      unfold glow; rw [←sub_div,norm_div]; norm_num; exact div_le_div_of_nonneg_right (exposed b H p hl v.1.1.1 (show Verified _ _ _ _ _ Knot from g) (day_in B _ k.le) (day_in B _ k) (day_gap B i)) (by norm_num)
    unfold F J inks; rw [←sum_sub_distrib]
    apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>r) _).trans ?_); swap
    · simp only [sum_const,card_range,nsmul_eq_mul]; unfold r; rw [mul_assoc]
    intro i hi; rw [sub_sub_sub_comm]; exact (norm_sub_le ..).trans ((add_le_add (hg _ v.2.2 i (mem_range.mp hi)) (hg _ v.2.1 i (mem_range.mp hi))).trans_eq (add_halves _))
  unfold Scroll.value faresF; rw [add_sub_add_comm,Scroll.mint,gains,add_mul]; apply (norm_add_le ..).trans; apply add_le_add
  · rw [dimP,dimP,sun_e]; apply (sun_n _).trans
    have hv : stick (0:Row) ∈ zone {0} := stick_in _ (mem_singleton_self _); exact exposed b H p (h.t1.stamped S) g.1 (show Verified _ _ margin _ _ {0} from g.2) hv hv (by rw [sub_self,norm_zero]; positivity)
  change ‖sideS (coastal m B F x)-sideS (coastal m B J x)‖ ≤ _; rw [show ∀ x y,sideS x-sideS y=sideS (x-y) from fun x y=>by simp [sideS,sub_mul]]
  exact (side_n _).trans (Cargo.closeC g (irradiates hl b.1 none) (irradiates hl b.1 (some a)) _ hk)
end

noncomputable def pinpoint (m B : Side) (S : Stamp m B) :=
  @dite (Index m) (∃ a:Index m,sanctioned m B S (some a)) (Classical.propDecidable _)
    (fun h=>h.choose) fun _=>0
lemma Grove.plane (S : Stamp m B) (h : Branch.Grove (terr _) S) (p : S.card ≤ scallop B) : sanctioned m B S (some (pinpoint m B S)) := by
  have he : ∃ a:Index m,sanctioned m B S (some a) := by
    classical
    by_cases e:S.Nonempty
    · obtain ⟨x,k⟩ := e; obtain ⟨a,g⟩ := offered m B x
      exact ⟨a,fun y v=>g y ((h.lim x k y v).le.trans p)⟩
    exact ⟨0,fun i l=> False.elim (e ⟨i,l⟩)⟩
  rw [pinpoint,dif_pos he]; exact he.choose_spec

def Scroll.term {c : Part m B} (W : Scroll m B c) (S : Stamp m B) := if S.card≤scallop B then W.value S (some (pinpoint m B S)) else fun _=>0
def Scroll.leftover {c : Part m B} (W : Scroll m B c) (S : Stamp m B) (x : Pack m B) := W.value S none x-W.term S x
def dust {c : Part m B} (W : Scroll m B c) (q : ℝ) (S : Stamp m B) := if S.card≤scallop B then W.mint S*q else W.mint S
def supportsCup (m B : Side) (S : Stamp m B) (f : Pack m B →ℂ) (w e : ℝ) :=
  ContinuousOn f (payer m B e) ∧ (∀ x∈payer m B e,‖f x‖≤w) ∧ 0≤w ∧
  (∀ g x, x∈payer m B e → f (Lattice.gauge g x.1,partner m B g x.2)=f x) ∧ (w≠0→ Branch.Grove (terr _) S) ∧
  ∀ x∈payer m B e,∀ y∈payer m B e, AgreeF (chairs m B S) x.2 y.2 → Agrees (walls m B S) x.1 y.1→ f x=f y
variable {u d c e : ℝ} (H : ScaleK u d W) (b : Budget B e c)
include H b
lemma gainS (S : Stamp m B) : SealX m B (some (pinpoint m B S)) S (W.term S) (W.mint S) e := by
  unfold Scroll.term; let x := currency H b.1 S (some (pinpoint m B S)); split_ifs; exact x
  exact ⟨continuousOn_const,x.pos,fun _ _=> (le_of_eq (norm_zero)).trans x.pos,fun _ _ _=>rfl,x.connect,fun _ _ _ _ _ _ _=>rfl⟩
lemma plates (S : Stamp m B) {x y:Pack m B} (h:x∈payer m B e) (g:y∈payer m B e) (p:AgreeF (faces m (pinpoint m B S)) x.2 y.2) (k:Agrees (room m B (pinpoint m B S)) x.1 y.1) : W.term S x=W.term S y := by
  have he := gainS H b S
  by_cases hz : W.mint S=0
  · rw [norm_le_zero_iff.mp ((he.norm _ h).trans hz.le),norm_le_zero_iff.mp ((he.norm _ g).trans hz.le)]
  by_cases heq:S.card≤scallop B
  · have hp := Grove.plane S (he.connect hz) heq; exact he.matched _ _ hp h g (p.less (slab_ch hp)) k
  simp [Scroll.term,heq]
lemma leavings (S : Stamp m B) : supportsCup m B S (W.leftover S) (dust W c S) e := by
  let f := currency H b.1 S none; let g := gainS H b S; have ht := f.pos; have hc := b.2.1
  refine ⟨f.cont.sub g.cont,fun x h=>?_,?_, fun t x h=>by unfold Scroll.leftover; rw [f.gaugeEq,g.gaugeEq] <;> assumption,fun t=>?_,fun x hx y hy K u=>?_⟩
  · unfold Scroll.leftover dust Scroll.term; split_ifs with k
    · by_cases l:W.mint S=0
      · have H := g.norm x h; rw [Scroll.term,if_pos k] at H; rw [norm_le_zero_iff.mp (H.trans l.le),norm_le_zero_iff.mp ((f.norm x h).trans l.le)]; simp [l]
      exact deviation b (Grove.plane _ (g.connect l) k) (by unfold scallop at k; have he:=collar_lt B; omega) H h
    rw [sub_zero]; exact f.norm x h
  · unfold dust; split_ifs <;> positivity
  · apply f.connect; unfold dust at t; split_ifs at t; exact left_ne_zero_of_mul t; exact t
  unfold Scroll.leftover; rw [f.matched x y trivial hx hy K u]; apply congrArg
  -- tune
  by_cases he:W.mint S=0
  · rw [norm_le_zero_iff.mp ((g.norm _ hx).trans he.le),norm_le_zero_iff.mp ((g.norm _ hy).trans he.le)]
  by_cases k:S.card≤scallop B
  · have hp:= Grove.plane S (g.connect he) k; apply g.matched x y hp hx hy K
    by_cases hc : S.Nonempty
    · obtain ⟨i,hi⟩ := hc; exact fun j V L=> u j (in_wall (pad_slab (hp i hi) hi) V) (in_wall (pad_slab (hp i hi) hi) L)
    have he : Branch.Grove (terr (Domain m B)) S := f.connect he
    have hN : S.Nonempty := populated he
    contradiction
  simp [Scroll.term,k]
end YM.CF.Phase
