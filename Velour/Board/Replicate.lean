import Velour.Board.Strip
/-!
# Doubles along the short axes of the banner

2^q copies along each of three axes, with `b₀*w*2^q ≤ 2N`,
`N=K.c m` (in matter units, gauge period 2N).
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

variable {K:Calibration} {w:ℕ} {o:Cell} {f:Family K} {S:Finset Cover}
 {l: List (Tile K)} {L U:Cell}
variable {m:Side}{Loom:Scree.Loom (K.c m)}{Y:Mark (K.c m)→ℂ}{D:ℝ}
         (p:Metered K m Loom Y D) 
local notation "b₀"=>ruler K.B
local notation "N" => K.c m
local notation "a₀" => ruler K.B * (w:ℤ)

def FitsT (K:Calibration) (m:Side) (w:ℕ) (L U:Cell):Prop :=
 ∀ i,L i ≤ U i ∧ ruler K.B * w * (U i-L i) ≤ 2*((K.c m).val:ℤ)
def stretch(L U:Cell)(i:Axis) := cutOver L i (2*L i-U i)
lemma reflect_twice_edge
 (h:Paved w o f l L U) (i:Axis)(a:L i≤U i): 
 Paved w o f 
   (l.map (tumble w o i (2*L i)) ++ l) (stretch L U i) U:=by
 have t:=pavingMir h i (2*L i)
 apply pavingJoin t h i
 · simp [cutOver]; omega
 · intro j; by_cases e:j=i
   · subst j; simp [cutOver]; omega
   simp [cutOver,e]
 · intro j; by_cases e:j=i
   · subst j; simp [cutOver]; omega
   simp [cutOver,e]

variable (t:InTest K true S false f) (u:Parcel K w o 0 S)
include p t u
lemma edge_bound (h:Paved w o f l L U) (i:Axis)
 (hfits:a₀ * (U i-L i) ≤ (N).val):
 ‖Y (Representation l m)‖^2 ≤ ‖Y (Representation (l.map (tumble w o i (2*L i)) ++ l) m)‖:=by
 obtain ⟨T,hT,H⟩:= pavingReservation t u h
 let z : ℤ := 4*(o i+w*L i)
 have e: Heat.gaugeShift K.B z = Wall K w o i (L i):=by
    unfold Wall z Heat.gaugeShift ruler; ring
 have ec: PaneCut K w o i (2*L i)=Wall K w o i (L i):=by
    unfold PaneCut Wall gaugeT ruler Heat.gaugeShift; ring
 have a:Satin.region T N ⊆ band N i (Heat.gaugeShift K.B z) K.ℓ:=by
    rw [e]
    apply enters_arc K i _ rfl  -- maybe argument order adjusts
    intro x px; specialize H i x px
    refine ⟨H.1,H.2.trans ?_⟩
    unfold Wall; linarith only [hfits]
 rw [rep_append,rep_mirror,ec,←e]
 exact p.twiceX i z ((hT.support m).mono a)

lemma bulk_axis
 (h:Paved w o f l L U)
 (i:Axis) (L0:L i=0) (U0:U i=1) (q:ℕ)
 (hfits:a₀ * (2:ℤ)^q ≤ 2*((N).val:ℤ)):
 ∃ k:List (Tile K), Paved w o f k (cutOver L i (1-2^q)) U ∧ 
    k.length=l.length*2^q ∧ ‖Y (Representation l m)‖^(2^q:ℕ) ≤ ‖Y (Representation k m)‖:=by
 induction q with
 | zero=>
   rw [show cutOver L i (1-2^0)=L from by
       ext j; simp [cutOver]; rintro rfl; exact L0.symm] -- simp may normalize
   simp only [pow_zero,mul_one,pow_one]; exact ⟨l,h,rfl,le_rfl⟩
 | succ q ih=>
   let b:=ruler K.B * (w:ℤ)
   have bp:0≤b:=mul_nonneg (ruler_gene _).le (by positivity)
   rw [pow_succ,← mul_assoc] at hfits
   have ht: b * (2:ℤ)^q ≤ (N).val:=by change a₀ * _ ≤ _; linarith
   obtain ⟨k,hk,a,d⟩:=ih (ht.trans (by omega))
   let A:=cutOver L i (1-2^q)
   have e:A i=1-2^q:=by simp [A,cutOver]
   have e₀:b*(U i-A i)≤(N).val:=by rw [e,U0,sub_sub_cancel]; exact ht
   let k' := k.map (tumble w o i (2*A i)) ++ k

   have er:stretch A U i=cutOver L i (1-2^(q+1)):=by
      ext j; by_cases v:j=i
      · subst j; unfold stretch cutOver; rw [if_pos rfl,e,U0,if_pos rfl]; ring
      simp [stretch,A,cutOver,v]
   refine ⟨k',?_,?_,?_⟩
   · rw [← er]
     exact reflect_twice_edge hk i (show A i≤U i from by rw [e,U0]; linarith [show (0:ℤ)≤2^q by positivity])
   · rw [pow_succ,←mul_assoc,←a]; unfold k'
     rw [List.length_append,List.length_map,Nat.mul_two]
   rw [pow_succ,pow_mul]
   exact le_trans (pow_le_pow_left₀ (by positivity) d _) (edge_bound p t u hk i e₀)


omit p t u

lemma fitgrown
 (h:FitsT K m w L U) (i:Axis) (U0:U i=1)
 {q:ℕ}(hfits:a₀ * (2:ℤ)^q ≤ 2*((N).val:ℤ)):
 FitsT K m w (cutOver L i (1-2^q)) U :=by
 intro j; unfold cutOver
 by_cases v:j=i
 · subst j; rw [if_pos rfl,U0,sub_sub_cancel]
   exact ⟨by linarith [show (0:ℤ)≤2^q by positivity],hfits⟩
 rw [if_neg v]; exact h j
lemma three (j:Axis):∃ a b c:Axis, a≠j ∧ b≠j ∧ c≠j ∧ b≠a ∧ c≠a ∧ c≠b:=by
 fin_cases j <;> decide +revert -- maybe slow

include p t u
lemma bulk
 (j:Axis)(e:o j=0) (n:ℕ) (tight:2*a₀*n ≤ (N).val)
 (z:ℤ)(q:ℕ) (hfits:a₀ * (2:ℤ)^q ≤ 2*((N).val:ℤ)):
 ∃ (d:List (Tile K))(L U:Cell), Paved w o f d L U ∧ d.length=4*n*(2^q)^3 ∧ 
 FitsT K m w L U ∧ ‖Y (banner j w (w*z) n f m)‖^((2^q)^3:ℕ) ≤ ‖Y (Representation d m)‖:=by
 obtain ⟨a,b,c,ha,hb,hc,d,d',d''⟩:=three j

 obtain ⟨l,h₀,len,price⟩:=banner_line w o f e n z
 have hf : FitsT K m w (stripL j (z-3*n)) (stripU j (z+n)):=by
    intro i; unfold stripL stripU
    by_cases hi:i=j
    · rw [if_pos hi,if_pos hi]; refine ⟨by omega,?_⟩
      linarith only [tight]
    rw [if_neg hi,if_neg hi]; refine ⟨zero_le_one,?_⟩; rw [sub_zero,mul_one]
    have hnr : 1≤(2:ℤ)^q:=one_le_pow₀ (by decide)
    have hp : 0≤ ruler K.B * (w:ℤ):=mul_nonneg (ruler_gene _).le (by positivity)
    exact (le_mul_of_one_le_right hp hnr).trans hfits
 obtain ⟨l₁,h₁,p₁,F₁⟩:=bulk_axis p t u h₀ a (if_neg ha) (if_neg ha) q hfits
 obtain ⟨l₂,h₂,p₂,F₂⟩:=bulk_axis p t u h₁ b
    (by simp [cutOver,stripL,hb,d]) (if_neg hb) q hfits
 obtain ⟨l₃,h₃,p₃,F₃⟩:=bulk_axis p t u h₂ c
    (by simp [cutOver,stripL,hc,d',d'']) (if_neg hc) q hfits
 refine ⟨_,_,_,h₃,by rw [p₃,p₂,p₁,len]; ring,
     fitgrown (fitgrown (fitgrown hf a (if_neg ha) hfits) b (if_neg hb) hfits) c (if_neg hc) hfits,?_⟩

 rw [←price, show (2^q)^3=(2^q:ℕ)*(2^q)*(2^q) from by ring,pow_mul,pow_mul]
 refine le_trans ?_ F₃
 exact pow_le_pow_left₀ (by positivity) (le_trans (pow_le_pow_left₀ (by positivity) F₁ _) F₂) _


omit p t u
def Fill (b volumeSide len :ℕ) : Prop :=
  volumeSide^4 ≤ b^4*len ∧ b^4*len ≤ (2*volumeSide)^4

-- exact fraction retained, not just existence a positive density subsequence
lemma filled (n b volumeSide q:ℕ)(h₁:2*b*n≤volumeSide)(h₂:volumeSide ≤ 4*b*n)
   (g₁:b*2^q ≤ 2*volumeSide)(g₂:volumeSide ≤ b*2^q):
    Fill b volumeSide (4*n*(2^q)^3):=by
 unfold Fill
 rw [show volumeSide^4=volumeSide*volumeSide^3 from by ring,
     show (2*volumeSide)^4=(2*volumeSide)*(2*volumeSide)^3 from by ring,
     show b^4*(4*n*(2^q)^3)=(4*b*n)*(b*2^q)^3 from by ring]
 constructor
 · gcongr
 have hu:4*b*n ≤ 2*volumeSide:=by nlinarith
 gcongr

lemma power (volumeSide b:ℕ)(p:0<b)(e:b≤volumeSide): ∃ q:ℕ,b*2^q ≤ 2*volumeSide ∧ volumeSide ≤ b*2^q:=by
 have h:∃q:ℕ,volumeSide ≤ b*2^q := ⟨volumeSide,
   (Nat.lt_two_pow_self (n:=volumeSide)).le.trans (Nat.le_mul_of_pos_left _ p)⟩
 refine ⟨Nat.find h,?_,Nat.find_spec h⟩
 cases hv:Nat.find h
 · simpa only [pow_zero,mul_one] using e.trans (by omega:volumeSide ≤ 2*volumeSide)
 rename_i q; have H:=Nat.find_min h (by omega:q<Nat.find h)
 have H:b*2^q<volumeSide:=Nat.lt_of_not_ge H
 rw [pow_succ]; nlinarith


abbrev pitch (K:Calibration) (w:ℕ) :ℕ := 16*K.B.val*w
lemma pitch_cast (K:Calibration) (w:ℕ): (pitch K w:ℤ) = ruler K.B * (w:ℤ) :=by
 unfold pitch ruler; push_cast; rfl
lemma pitch_pos (K:Calibration) {w:ℕ} (h:0<w) : 0<pitch K w:=by
 unfold pitch; have h:=K.B.property; positivity
structure Deck (m:Side) (w:ℕ) (o:Cell) (f:Family K)
   (l:List (Tile K))(L U:Cell):Prop where
 paved:Paved w o f l L U
 fits:FitsT K m w L U
 fill:Fill (pitch K w) (K.c m).val l.length

lemma Deck.length_pos (h:Deck m w o f l L U):0<l.length := by
 by_contra! hn
 have ht := h.fill.1
 rw [Nat.eq_zero_of_le_zero hn,mul_zero] at ht
 have a:= (N).property
 exact not_le_of_gt (by positivity) ht
lemma Deck.length_le (e:0<w)(h:Deck m w o f l L U) : l.length ≤ (2*(N).val)^4 := 
 le_trans (Nat.le_mul_of_pos_left _ (pow_pos (pitch_pos K e) 4)) h.fill.2

include p t u
lemma hotStrip
 (j:Axis)(e:o j=0) (a:0<w)(far:2*(pitch K w) ≤ (N).val)
 (θ:ℝ)(ht:0≤θ)
 (h:∀ l L U,Deck m w o f l L U → ‖Y (Representation l m)‖ ≤ θ^l.length)
 (z:ℤ):
 let d:=finalN (N).val (pitch K w)
 ‖Y (banner j w (w*z) d f m)‖ ≤ θ^(4*d):=by
 intro d
 let b:=pitch K w
 have bp := pitch_pos K a
 obtain ⟨_,g,u',k⟩:=finalCount _ _ bp far
 obtain ⟨q,da,db⟩:=power (N).val b bp (by omega)
 obtain ⟨l,W,T,paved,len,fits,pow⟩:=bulk p t u j e d
   (by rw [show 2*a₀*d = (↑(2*(pitch K w)*d:ℕ):ℤ) by rw [Nat.cast_mul,Nat.cast_mul,pitch_cast]; push_cast; ring]
       exact_mod_cast g) z q
   (by rw [← pitch_cast]; exact_mod_cast da)
 have hh:=pow.trans (h l W T 
    ⟨paved,fits,len.symm ▸ (filled _ _ _ q g k da db)⟩)
 rw [len,pow_mul] at hh
 exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by positivity)).mp hh

end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard

