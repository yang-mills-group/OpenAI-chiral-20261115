import YM.CF.Buffered.Masters
/-! Receipt inequalities in terms of phase dimensions issued BEFORE g,h choice. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 470000
noncomputable section
namespace YM.CF.Buffered.Concert
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker ComplexOrder
open Cube Tenant Lat Spire Scroll Scree Jet Phase Branch Fock Skye
open Py Vale Vale.Grace Haro Nova
open Wilson Precision Next.Free Next.SectorChange Tulip Gauge Paige Vault Brace
open Push.SectorMeasure
open Heat Advance Pressure Region Ballad Alloy Burn Edition
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{J:Tiling K}{C:Conveyor K}{V:SpanCal K}
local notation "o" => K.q
local notation "m₃" => K.q*(3:Side)
variable {e:ℝ}
structure Venue (V:SpanCal K)(e:ℝ) where
 H : ℝ
 D₁ : ℝ
 C₁ : ℝ
 t : ℝ
 θ : ℝ
 width : ℕ
 w : ℕ
 v' : ℝ
 t' : ℝ
 k : ℕ
 p : 0 < e
 pos : 0<θ
 tower : Ballad.Tower V.spanX K.vertex D₁ H C₁ (e/16) t width w
 crop : Alloy.Crop K.K.j H v' t' k
 grows : v' ≤ K.h
 -- parameter tower phase including graph threshold C₁ paid before R

abbrev nameT (K:Calibration)(c:ℝ)(e:ℝ)(p:SpanCal K) (v:ℕ) : Prop := ∀ᶠ N:Side in atTop,Even N.val → ∀ A:Melody K.B v,∀ b:Bool,Ballad.LedgerR N K.K.j p.b c ((e/16)/8) b A
lemma affords_vertex (K:Calibration) (p:SpanCal K) (g:0<e) : ∃ c:ℝ,0<c∧ (∀ᶠ R:ℕ in atTop,nameT K c e p R) ∧∀ R:ℕ,∃ D H t:ℝ,∃ w i:ℕ, Tower p.spanX R D H c (e/16) t w i ∧ ∃ V' t':ℝ,∃ k:ℕ, Crop K.K.j H V' t' k:=by
 obtain ⟨c,t,G⟩:=Ballad.floored p.spanX _ (show 0<e/16 by positivity); refine ⟨c,t,Melody.atVertex p.spanX.p p.spanX.rP t _ (by positivity),fun R=>?_⟩; obtain ⟨D,H,u,w,i,F⟩:=G R; exact ⟨D,H,u,w,i,F,crop_f p.spanX.p F.loom.le⟩
variable (p: Venue V e) (W:Printed K C J V)
noncomputable def seat := (Filter.eventually_atTop.mp (playback K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ V.spanX V.portX K.positive_h V.enough_h p.tower p.crop (by linarith [p.p]) p.grows V.c V.k)).choose
noncomputable def chair := (Filter.eventually_atTop.mp (Edition.mounts K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ V.spanX K.positive_h V.c V.k p.pos)).choose
noncomputable def butt (k:nameT K p.C₁ e V K.vertex) : Side := (Filter.eventually_atTop.mp k).choose
def clicks (J:Tiling K)(m:Side):= (J.qcount m).val^4
abbrev minDr (V:SpanCal K):= V.read/(2*Nova.poseX)/2
lemma minDr_p(V:SpanCal K): 0< minDr V:=by have ht:=V.spanX.pos; have h:=Nova.pose_p; unfold minDr; positivity
abbrev hiDr (V:SpanCal K):= 2 * V.E'+1
abbrev cover (m:Side)(B:Side):=( (Vale.cell m B B 0).val:ℝ) -- adjust, rename
abbrev plusV(p: Venue V e):ℝ:= Real.log (2*hiDr V)-Real.log (minDr V /2)/81+2
abbrev hmark (p:Venue V e):ℝ:= 2*p.D₁+1
abbrev creditA : ℝ:= hmark p / minDr V
abbrev season (p:Venue V e)(J:Tiling K) := p.θ* (((K.c K.q).val:ℝ)^4) + plusV p -- simplify count arithmetic target later
structure Rates (p:Venue V e)(J:Tiling K) : Prop where
 x_cost : seat p ≤ K.x
 thermal : chair p ≤ K.x
 vertex : nameT K p.C₁ e V K.vertex
 z_age : butt p vertex ≤ K.c K.q
 power : (Real.log K.x)^4 ≤ (K.q.val:ℝ)
 distance : (3/2:ℝ)^4 * season p J ≤ Real.log 2 * (clicks J K.q)
 cash : creditA p +1≤ (2:ℝ)^(clicks J K.q)
-- distance and cash allowable by increasing q; explicitly also state eventual formulation later before any circle.
variable (F: Rates p J)
variable {n:ℕ} {m:Side}(Z:Flipbook K J C n){x:K.Allowed m n}
def reg {m:Side} (b:K.Allowed m n) : Volume.History K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ K.x m n:= ⟨K.T,K.monthSize m b.1,C.B₀ n,C.sharp m n,C.loom m,C.wave n,C.tilt n,Shots.sharp (Z.frame m b).pair⟩
include p F
lemma receives (h:under V m)(b:K.Allowed m n) : Passbook K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ (reg Z b) K.vertex V.kT V.b V.read V.E' (e/16) p.D₁ p.C₁ p.width :=
 ((Filter.eventually_atTop.mp (playback K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ V.spanX V.portX K.positive_h V.enough_h p.tower p.crop (by linarith [p.p]) p.grows V.c V.k)).choose_spec K.x F.x_cost m h.1 h.2 n (reg Z b))
include W
include Z in
lemma hasGap (x: K.Allowed K.q n) (b: K.Allowed (K.q*3) n) : Real.log (Graph.drip (C.sharp o n 0) K.P)-Real.log (Graph.drip (C.sharp m₃ n 0) K.P) /81 ≤ p.θ*( (K.c o).val:ℝ)^4 :=
 (Filter.eventually_atTop.mp (Edition.mounts K.V K.a K.p K.i K.N0 K.J K.η K.h K.R0 K.δ V.spanX K.positive_h V.c V.k p.pos)).choose_spec K.x F.thermal o W.window_q.1 W.window_q.2 W.window_3q.2 F.power n (reg Z x) (reg Z b) rfl
lemma range_p (h:K.takes m)(u:under V m) : ∀ᶠ n in atTop,
 0 < Graph.drip (C.sharp m n 0) K.P ∧ Graph.drip (C.sharp m n 0) K.P * (minDr V/2) ≤ lodestar C m n ∧ lodestar C m n ≤ 2*hiDr V *Graph.drip (C.sharp m n 0) K.P:=by
 obtain ⟨ν,H⟩:= W.spring h u; filter_upwards [W.sizes,K.eventually_allowed h,H, eventually_gt_atTop 0, (Burn.bill_shrinks K.b₀ m.val (trial₀ K+loss K)).eventually (ge_mem_nhds ν)] with n ⟨B⟩ b H w t -- ν is strict rake/2>0; temper threshold
 let U:= Graph.drip (C.sharp m n 0) K.P; have he:= receives p F B u b; refine ⟨he.pot,?_,?_⟩ <;> have hl := abs_le.mp ((B.frame m b).close w)
 · have hx: U*minDr V ≤ ‖vac0 K.P (C.sharp m n 0) (C.loom m 0)‖:= he.lower; change U*(minDr V/2)≤_; linarith [H.1]
 · have hx: ‖vac0 K.P (C.sharp m n 0) (C.loom m 0)‖ ≤ hiDr V*U := he.upper; have hg:= ((B.frame m b).low V W.qualify u).2; change _ ≤ 2*hiDr V* U; linarith
lemma eco : ∀ᶠ n in atTop,Region.Ticket.lux 3 (barestar C K.q n) (barestar C (K.q*3) n)/(J.qcount o).val^4 * (3/2:ℝ)^4 ≤ Real.log 2 := by
 filter_upwards [range_p (m:=K.q) p W F (big_one K) W.window_q, range_p (m:=m₃) p W F (big_three K) W.window_3q, W.sizes, K.eventually_allowed (big_one K), K.eventually_allowed (big_three K)] with n ⟨x,U,z⟩ ⟨X,u',v⟩ ⟨Z⟩ d₀ d₁
 let r:= barestar C o n; let s:=barestar C m₃ n; let V':=Graph.drip (C.sharp o n 0) K.P; let Q:=Graph.drip (C.sharp m₃ n 0) K.P
 have hp:0< minDr V/2:=half_pos (minDr_p _)
 have ht:0<lodestar C o n:= (mul_pos x hp).trans_le U; have hw:0<lodestar C m₃ n:=(mul_pos X hp).trans_le u'
 have he:= Real.log_le_log ht z; have hf:= Real.log_le_log (mul_pos X hp) u'; rw [invoice C ((same_sign C).1 ht),Real.log_mul (x:=2*hiDr V) (by have hh:=V.portX.lark; unfold hiDr; positivity) x.ne'] at he
 rw [invoice C ((same_sign C).1 hw),Real.log_mul X.ne' hp.ne'] at hf
 have ha:= hasGap p W F Z d₀ d₁; have hv: Region.Ticket.lux 3 r s≤ season p J:=by
    have hx:= (abs_le.mp (Z.offset _ 3 d₀ d₁ rfl)).2
    unfold Ticket.lux season plusV; unfold r s; norm_num only [PNat.val_ofNat] at hx ⊢; linarith
 let M:=clicks J o; have hh:(J.qcount o).val^4>0:=by positivity
 rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
 exact le_trans (mul_le_mul_of_nonneg_right hv (by positivity)) (by simpa [mul_comm (season p J),clicks] using F.distance)
lemma sound_stage : ∀ᶠ n in atTop, ∀ (I:Type)[Fintype I][DecidableEq I], ∀ (b:Bool)(S:Single (K.c K.q) → I) (Q:I→Melody K.B K.vertex)(L:List I), L.Nodup → L.length=clicks J K.q → L.length ≤ (K.c K.q).val^4 → Payments p.width S Q →
    ‖atZero K.P (C.warm K.q n) (C.loom K.q) (Melody.festival Q b L)‖ ≤ (e/8)^(clicks J K.q) := by
 let X:= W.narrative.hist; let s:=clicks J o; let μ:= (Melody.cuts K.vertex 0)^s; let A:= |μ|+1; have ha:0<A:=by unfold A; positivity
 let D:=(e/16)^s; have hx:=p.p; have hd:0<D:=by unfold D; positivity
 filter_upwards [cone_ratio X (div_pos hd ha), W.sizes, K.eventually_allowed (big_one K)] with n T ⟨Z⟩ r; intro I _ _ b S Q L l hu hv H
 let A':= Melody.festival Q b L (N:=K.c o); have hw:(Q=Q):=rfl; have hp:= T _ r A' (Env.compact (Melody.festival_cont ..)) A (fun v=> le_trans (Melody.festival_norm _ _ L v) (by rw [hu]; exact ((le_abs_self μ).trans (le_add_of_nonneg_right zero_le_one))))
 let x:= X.cap n A'; let B:=atZero K.P (C.warm o n) (C.loom o) A'; have he: ‖x-B‖ ≤ D:= (hp.trans_eq (by rw [div_mul_cancel₀ _ ha.ne'])) -- tune B let
 obtain W₀:= receives p F Z W.window_q r
 let G:=Graph.drip (C.sharp o n 0) K.P
 have hG:0<G:= W₀.pot; have hg:0< minDr V:=minDr_p V
 have hh:‖x‖ ≤ creditA p * D := by
   have ht: ∀ i,LedgerR (K.c o) K.K.j V.b p.C₁ ((e/16)/8) b (Q i):= fun i=> (Filter.eventually_atTop.mp F.vertex).choose_spec _ F.z_age (Vale.val_e ..) _ _
   have hp': L.length ≤ (cell o K.B K.R.L 0).val^4:=hv; have hv:= W₀.strings I S Q b L l (by exact_mod_cast hp') ht H; rw [hu] at hv
   unfold x Histories.cap atZero X; rw [← same_ratio,norm_div]; change ‖num0 K.P (C.sharp o n 0) _ A'‖/ ‖vac0 K.P (C.sharp o n 0) _‖≤ _; have hx: G * minDr V≤ ‖vac0 K.P (C.sharp o n 0) (C.loom o 0)‖:= W₀.lower
   refine (div_le_div₀ (show 0 ≤ hmark p * G * D from (norm_nonneg _).trans hv) hv (mul_pos hG hg) hx).trans ?_; apply le_of_eq; change (hmark p* G*D)/(G*minDr V)=_; unfold creditA; field_simp
 change ‖B‖ ≤ _; apply (norm_le_norm_sub_add B x).trans; rw [norm_sub_rev]; refine (add_le_add he hh).trans ?_; rw [show e/8=2*(e/16) from (by ring),mul_pow]; have hx:= mul_le_mul_of_nonneg_right F.cash hd.le; unfold D s clicks at *; linarith -- expensive
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.eco
#print axioms YM.CF.Buffered.Concert.sound_stage
