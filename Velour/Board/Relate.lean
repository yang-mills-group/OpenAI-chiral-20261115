import Velour.Board.Replicate
import SatinThinCrystal
/-! # Conclude cap pricing from array pricing
Uses the `IcePlot` of the same journey. Pay all copies ultimately on the
sharp, at spacing and origins in ticks.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 1200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
open SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open SatinVerification
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Q₀"=>G.history

variable (j:Axis)(w:ℕ)(f:ℕ→Family (tent Y H))(S:Finset Cover)(t:∀i,InTest (tent Y H) true S false (f i))
variable (ψ:ℕ→ℕ)(ouT:Tendsto ψ atTop atTop)
local notation "π" r:max=>i (G.rows (ψ r))
local notation "ζ" r:max=> k (G.columns (ψ r))

local notation "Z" u:max r:max=> train Y H s u (π r) (ζ r) S (f r)
local notation "W" t:max=> volumeAround Λ l t S
local notation "uM" t:max=> (L₀^t*w)
local notation "b₀"=>ruler Λ.block

variable (o:Cell)
 /-- Extensive test to ask on a fixed subsequence of the `GroundExtension`
 path, even with a moving test converging in test cost.
 Hypothesis only for tightly packed arrays (lower fraction `fill`);
 `Deck` keeps motions **exact**, so one can ask an RG or marked-integral
 question on translated/mirrored copies of a leaf.
 -/
def Settle (θ:ℝ) : Prop :=
 ∀ᶠ e in atTop,∀ (d:List (Tile K)) (L U:Cell),
   Deck (m (π e) s) w o (f e) d L U →
    ‖sharp Y H s (π e) (ζ e) (Representation d)‖ ≤ θ^d.length

private lemma castPaid{t v:Side}{f:Mark t}(h:t=v)
 (e:Envelope f) {C:ℝ}(p:∀ x,‖f x‖≤ C) :
 let g : Mark v := h ▸ f
 Envelope g ∧ (∀x, ‖g x‖≤C):=by
 subst v; exact ⟨e,p⟩
lemma iceCream {i k:ℕ}(h:IcePlot Y s i k)(g:Ferry Y s i k) {f:Family (tent Y H)} (t:TestFamily K true f)
 {C:ℝ}(p:pay f C): ‖sharp Y H s i k f-hot Y H s i k f‖ ≤ iceRate Y s i*C:=by

 obtain ⟨_,u⟩:=t.paid
 have z:=castPaid (terrain Y H (Y.ir i) s) (u.support (m i s)).env (p (m i s))
 unfold hot; rw [dif_pos g.depth]; exact h g.depth _ _ z.1 z.2
include V ouT
private lemma cruiseIce (C θ:ℝ)(c:0<C)(r:0<θ):
 ∀ᶠ i' in atTop,let N:=(T₀ (π i') s).val;
    ∀ n ≤ (2*N)^4, iceRate Y s (π i') * C^n ≤ θ^n:=by
 -- fixed positive at this resolution 
 have u:C/θ ≤ Real.exp (C/θ):=by linarith [Real.add_one_le_exp (C/θ)]
 filter_upwards [ (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (rides Y H V G ψ ouT s)|>.eventually_ge_atTop (16*(C/θ))] with i' t
 intro N n h
 let e:=Real.exp (-((N:ℕ):ℝ)^5)
 have hd: e*(C/θ)^n ≤ 1:=by
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) u n)
             (Real.exp_pos _).le) ?_
    rw [←Real.exp_nat_mul]
    unfold e
    rw [←Real.exp_add, Real.exp_le_one_iff]
    have v:(n:ℝ) ≤ (2*(N:ℝ))^4 := by exact_mod_cast h
    change 16*(C/θ) ≤ (N:ℝ) at t
    linarith only [mul_le_mul_of_nonneg_right v (by positivity:0≤C/θ),
       mul_le_mul_of_nonneg_right t (show 0≤(N:ℝ)^4 from by positivity)]
 rwa [div_pow,←mul_div_assoc,div_le_one (by positivity)] at hd

variable (freeze:IcePath Y (i∘G.rows) (k∘G.columns))
 (shape:Parcel (tent Y H) w o 0 S)
 (margin:o j=0)
 (hw:0<w) (θ:ℝ)(positive:0 < θ)
 (ask:Settle Y H s G w f ψ o θ)
include ask positive hw t shape margin freeze
lemma peak_Plot (C:ℝ)(p:0<C) (p':∀ᶠi in atTop,pay (f i) C): Peak Y H s G j w f ψ (2*θ) :=by
 unfold Settle at ask; unfold Peak
 filter_upwards [ask,p',ouT.eventually (freeze s),ouT.eventually (G.history.finance s), 
   cruiseIce Y H V s G ψ ouT C θ p positive,
   (rides Y H V G ψ ouT s).eventually_ge_atTop (2*pitch K w)] with i' q paid ice g d far z
 have r : ∀ d L U, Deck (m (π i') s) w o (f i') d L U →
    ‖hot Y H s (π i') (ζ i') (Representation d)‖ ≤ (2*θ)^d.length:=by
    intro l A B e
    have hf := q l A B e
    obtain ⟨_,h,_⟩:= pavingReservation (t i') shape e.paved
    have hx :=iceCream Y H s ice g (aux_test h) (pavingCost paid e.paved)

    have hside : (K).c (m (π i') s)= T₀ (π i') s :=terrain Y H (Y.ir (π i')) s
    have hlen:= Deck.length_le hw e; rw [hside] at hlen -- warning rw dependent? l.length no Side
    refine le_trans ((norm_le_norm_sub_add _ (sharp Y H s (π i') (ζ i') (Representation l))).trans
       (add_le_add ((norm_sub_rev ..).trans_le (hx.trans (d l.length hlen))) hf)) ?_
    rw [mul_pow,←two_mul]
    have hk := Deck.length_pos e
    exact mul_le_mul_of_nonneg_right (calc (2:ℝ) = 2^1:=by rw [pow_one]
                                           _ ≤ _:= pow_le_pow_right₀ (by norm_num) hk) (by positivity)
 let n := π i'; let k' := ζ i'
 have hN : ((K).c (m n s)).val=(T₀ n s).val := by rw [show (K).c (m n s)= T₀ n s from terrain Y H (Y.ir n) s]
 have hp:=hotStrip (p:=boxprice Y H n k' g.depth s g.fire g.enters)
    (t i') shape j margin hw (far:=le_trans far hN.symm.le) (2*θ) (by positivity)
    (fun d L U t'=>by have h:=r d L U t'; unfold hot at h; rw [dif_pos g.depth] at h; exact h) z
 dsimp only at hp
 rw [hN] at hp
 unfold hot; rw [dif_pos g.depth]; exact hp

omit t
/-- **The sharp array criterion** for purchasing a cap. -/
lemma boardPrice (room:Arena Y H G.history.circuit j 0 false)
  (dome:Entry Y H s j false w) (p:BQueue S f dome.val.val) :
 ‖boxOp Y H V s G.history G.clipped j false room w dome hw‖ ≤ 4*θ:=by
 obtain ⟨c,pos,_,cost⟩:=p.bdd
 have h:=shape j
 unfold Wall at h
 simp only [Pi.zero_apply,margin,mul_zero,zero_add,mul_one] at h
 have ht:= peak_Plot Y H V s G j w f S p.whereTo ψ ouT o freeze shape margin hw θ positive ask c pos cost
 have q:=price Y H V s G j h ψ ouT (2*θ) ht (by positivity) hw dome p room
 linarith only [q]

end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard

#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard.boardPrice

