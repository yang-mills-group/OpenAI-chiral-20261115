import YM.SU5.FiniteGaugeData.Marked.Journey.Ignite
import YM.SU5.FiniteGaugeData.Marked.Stage

/-!
# On any elected Course: early and late period prices at EACH fixed
resolution. W is not used. Even for the periods/boxes not large enough
for the separated reflected doubling, we can add their prices: there are
only finitely many such periods for each box and observing level and even at
those fixed finite volumes we can pay the L1 local cost under that volume's
fixed base law. (Unlike for the `Settled` application, do this here so can
retrieve convergence also in each and every period of the Course, not just
the ones eventually reached in the volume extraction.)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
    (s i k:ℕ) (S:Finset Cover)
abbrev dusk:= (tent Y h).c (momentm Y i s)
local notation "K"=> tent Y h
local notation "Ω" i:max => (tent Y h).c (momentm Y i s)
local notation "lΩ" i:max=> deltaL Y h i s
-- First for isolated Course periods (including wrapping marks, no separated size assumptions)
local notation "C₀" i:max=> city (Ω i)
def toes (f:PairsC→ℂ)(x:Orbit (Ω i)):= f (Prod.map (onC (Ω i)) (onC (Ω i)) (drawn (lΩ i) x))
def youth (f:PairsC→ℂ):ℝ:=∫ x, ‖toes Y h s i f x‖ ∂city (Ω i)
lemma launch_toes : Measurable (lΩ i) := by
  unfold deltaL; apply transport (terrain Y h (Y.ir i) s).symm ((Y.voyage i).ownership s).paid.bill
where
 transport{t u:Side}{a:Loom t}(w:t=u)(p:Measurable a):Measurable (show Loom u from w ▸ a):=by subst t; exact p
lemma toes_m {f:PairsC→ℂ}(p:Coeff true S f): Envelope (toes Y h s i f):= Env.along p.env (((on_cont _).prodMap (on_cont _)).measurable.comp (drawn_m _ (launch_toes Y h s i)))
lemma youth_nonneg (f:PairsC→ℂ):0 ≤ youth Y h s i f:= integral_nonneg fun _=>norm_nonneg _
lemma youth_limit {u:Chorus} {f:PairsC→ℂ}(p:Coeff true S f):
    cash (lΩ i) (note (tent Y h) f u (momentm Y i s)) ≤ youth Y h s i f:=
  integral_mono_of_nonneg (Eventually.of_forall fun _=> norm_nonneg _)
    ((Env.integrableX (toes_m Y h s i S p) (city (Ω i))).norm)
    (Eventually.of_forall fun x=> pitched K u f (momentm Y i s) (drawn (lΩ i) x))

-- Purchase predicates before trimming
structure Ferry : Prop where
  depth:(Y.voyage i).kick ≤ k
  enters:s ≤ Y.uv k
  fire: LocalLimit.Donor.Gap Y.meter (Y.voyage i).funds Λ.C Λ.δ Λ.R0 Y.τ ((Y.voyage i).X (Y.uv k)) ((Y.voyage i).Q k depth) s
lemma ferry_all : ∀ᶠ k:ℕ in atTop, ∀ i:ℕ,(Y.voyage i).kick ≤ k → Ferry Y s i k := by
  filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop s,Y.heatGap s] with k u p i v
  exact ⟨v,u,p.2 i v⟩
lemma ferry_later: ∀ᶠ k:ℕ in atTop,Ferry Y s i k:= by filter_upwards [ferry_all Y s,eventually_ge_atTop (Y.voyage i).kick] with k p h using p i h

local notation "X"=> duetCharge Y s
lemma raised (s:ℕ) : StrictMono (fun i=> (momentm Y i s).val):=by
  intro i j t; exact Nat.mul_lt_mul_of_pos_right (Y.ir_grows t) (Λ.R.L^s).property
lemma momentum (s:ℕ):Tendsto (fun i=> momentm Y i s) atTop atTop:= tendsto_atTop.2 (fun r=> (raised Y s).tendsto_atTop.eventually_ge_atTop r.val)

def argument : ℝ:= (albums K S (duetCharge Y s)).choose
lemma ahead : 0 < argument Y h s S:= (albums K S (duetCharge Y s)).choose_spec.1
variable {i k} (p:Ferry Y s i k)

def traffic : Prop:= ∀ k, ∀ p:Ferry Y s i k, ∀ {u:Chorus}, Bracket S u→∀ {f:PairsC→ℂ},Coeff true S f →
  ‖collector Y h i k p.depth s (note (tent Y h) f u (momentm Y i s))‖ ≤ argument Y h s S * Touch S l f
lemma late_fee : ∀ᶠ i:ℕ in atTop, traffic (i:=i) Y h s S:= by
  filter_upwards [(momentum Y s).eventually ((albums K S X).choose_spec.2.and (awning S K l))] with i t k p u v f w
  have ht:= boxprice Y h i k p.depth s p.fire p.enters
  have hw:AtSupport false _ _:= v.harmony ▸ (note_t K u w v.tines).support (momentm Y i s)
  refine (t.1 (lΩ i) _ ht _ hw).trans (mul_le_mul_of_nonneg_left ?_ (ahead Y h s S).le)
  exact le_trans (youth_limit Y h s i S w) (t.2 _ (move_law Y h i s) (launch_toes Y h s i) f w)
include p
def counter : Chorus→Purse S→ℂ:= fun u f=>collector Y h i k p.depth s (note K f.val u (momentm Y i s))
local notation "δ" i:max=> Real.exp (duetCharge Y s*((momentm Y i s).val:ℝ)^4)
lemma early_fee (u:Chorus)(v:Bracket S u)(f:Purse S): ‖counter Y h s S p u f‖ ≤ (δ i) * youth Y h s i f.val:= by
  have e:=boxprice Y h i k p.depth s p.fire p.enters
  exact (e.tally _ ((note_t K u f.property v.tines).support _).env).trans (mul_le_mul_of_nonneg_left (youth_limit Y h s i S f.property) (Real.exp_pos _).le)


omit p
def start : ℕ:=(eventually_atTop.mp (late_fee Y h s S)).choose
abbrev Cadets := Fin (start Y h s S)
def extras (f:PairsC→ℂ) := ∑ i:Cadets Y h s S, (δ i.val)*youth Y h s i.val f
lemma extras_n (f:PairsC→ℂ):0≤extras Y h s S f:=sum_nonneg fun _ _=>mul_nonneg (Real.exp_pos _).le (youth_nonneg ..)
def receipt (f:PairsC→ℂ):= argument Y h s S*Touch S l f+extras Y h s S f
lemma receipt_pos (f:PairsC→ℂ):0≤receipt Y h s S f:=add_nonneg (mul_nonneg (ahead Y h s S).le (touch_pos ..)) (extras_n ..)

def output (u:Chorus)(f:Purse S)(i k:ℕ):ℂ:= if p:Ferry Y s i k∧Bracket S u then counter Y h s S p.1 u f else 0
variable (u:Chorus)
lemma paid_stage (f:Purse S) (i k:ℕ):‖output Y h s S u f i k‖ ≤ receipt Y h s S f.val:=by
  unfold output; split_ifs with t; swap; · rw [norm_zero]; exact receipt_pos ..
  by_cases hp:i < start Y h s S
  · refine (early_fee Y h s S t.1 u t.2 f).trans ((show _≤ extras Y h s S f.val from ?_).trans (le_add_of_nonneg_left (mul_nonneg (ahead Y h s S).le (touch_pos ..))))
    let j:Cadets Y h s S:=⟨i,hp⟩
    change (δ j.val)*youth Y h s j.val f.val ≤ (∑ i:Cadets Y h s S, (δ i.val)*youth Y h s i.val f.val)
    exact Finset.single_le_sum (f:=fun a:Cadets Y h s S=> (δ a.val)*youth Y h s a.val f.val) (fun _ _=>mul_nonneg (Real.exp_pos _).le (youth_nonneg ..)) (mem_univ j)
  exact (((eventually_atTop.mp (late_fee Y h s S)).choose_spec i (not_lt.mp hp)) k t.1 t.2 f.property).trans (le_add_of_nonneg_right (extras_n ..))
lemma paid_joint (f g:Purse S) (i k:ℕ):dist (output Y h s S u f i k) (output Y h s S u g i k) ≤ receipt Y h s S (f.val-g.val):=by
  let y:Purse S:=⟨f.val-g.val,pastel f.property g.property⟩
  refine (paid_stage Y h s S u y i k).trans' (le_of_eq ?_)
  unfold output y; split_ifs with t; swap; · rw [norm_zero,dist_self]
  let e:=boxprice Y h i k t.1.depth s t.1.fire t.1.enters
  unfold counter
  rw [dist_eq_norm,note_minus]; dsimp only [Pi.add_apply,Pi.smul_apply]
  rw [e.sum _ _ ((note_t K u f.property t.2.tines).support _).env ((((note_t K u g.property t.2.tines).support (momentm Y i s)).smulM _).env),e.mult,neg_one_mul,sub_eq_add_neg]
end YM.CF.Buffered.Afterglow.Journey
