import Merino.Mitre.Favorite
import Merino.Mitre.Jetstream
import Merino.Mitre.Starlet
import Merino.Silk.Keeps
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 880000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Mitre
open Fock Finset Lattice Lat Spire Scroll Cube Branch Skye Tenant RG BProof
open scoped BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Buffered
variable {N:Side}
open Brooch

open Roots Lamour.Bridge.Celeste.Clock Fabric Thera

open Py Rate LocalLimit Preparation
open Afterglow Vale Journey Tower.VacuumSelection Coin Pressure Pressure.Worth
open Filter Medal Hem Diadem CF.Pannier.Chancel Tower.SlabMark
variable (P:Spine)(p:Bolts)(f:ℕ)(s i k:ℕ)
local notation "Ω"=>RegNum P s i
local notation "Γ"=>LedgerM P s i k
local notation "x"=>scaleM P s
local notation "n"=>priceTick P
local notation "K"=> LoomM P s i
local notation "z"=> hueM P s

variable (d:Gown P p (priceTick P) s i k)
def clothR (b:ℕ):=2*b+16
def corona:= clothR (Γ).p.B
def slack := max 1 (‖(z:ℂ)‖*rateOk p.c)
lemma ease_one:1≤ slack P p s:=le_max_left ..

abbrev stone:=d.y.opening K (Γ).p z
lemma smooth:
 AtSupport false (purse (corona P s i k) 0) (toMark (stone P p s i k d)) ∧
 Bide.plainP (stone P p s i k d) ∧
 separation 0 (node d.y.origin) ≤ corona P s i k∧
 ∀V, ‖stone P p s i k d V‖≤ slack P p s:=by
 have q:= d.ticket.hem.licensed z
 have g: separation 0 (node d.y.origin) ≤4 :=by rw [d.here];exact home_fits _
 refine ⟨q.loc.mono ?_,Bide.plain (allowedX q),
    g.trans ((le_trans (show 4≤16 from by decide) (Nat.le_add_left ..))),fun v=>(initial d.ticket.hem z v).trans (le_max_right ..)⟩
 intro j v
 obtain ⟨a,t,e⟩:=halo_spec.mp v
 rw [mem_singleton.mp t,Spool.post] at e
 apply halo_spec.mpr; unfold corona clothR
 have b:=d.ticket.width
 exact ⟨_,mem_singleton_self _, (separation_triangle _ _ _).trans ((Nat.add_le_add g e).trans (by omega))⟩



-- log power late
open Papal

/-- Actual positive-side pose. -/
abbrev matin (t:ℕ): BProof.Obs Ω:=
   Bide.move (up t)⁻¹ (stone P p s i k d)

lemma perching(t:ℕ): Spool.perches (stone P p s i k d)
   (matin P p s i k d t) (wrap _ (Lace.noon (t/2))) := sail _ (smooth P p s i k d).2.1

def mPrice (q:ℝ):=Real.exp 9 * q^2
def Flash(t:ℕ):Prop:=
 let Q:=ball (stone P p s i k d) (up t)
 AtSupport false (Buffered.band (RegNum P s i) Lace.pole 0 P.calibration.ℓ) Q ∧
 ‖Journey.compass P.run i k s (photo Q)‖≤ mPrice (gold P s f)

lemma Fview {t}(e:corona P s i k+P.calibration.ℓ ≤ t)
 (h:t%2=0)(r:4*t≤(RegNum P s i).val):
 AtSupport false (Buffered.band (RegNum P s i) Lace.pole 0 P.calibration.ℓ) (ball (stone P p s i k d) (up t)):=by
 obtain ⟨g,j,l,v⟩:=smooth P p s i k d
 apply ((flown _ j g v t).1.seat).mono; rw [upfly h]
 exact matinee_up e (le_trans (by omega) r)


local notation "C"=>P.calibration
def appointments:= diameter x + addgap C ≤ (RegNum P s i).val ∧
 Icicle (RegNum P s i).val (shimmer x*Diadem.tariff C (diameter x))
 |plumelet (gold P s f)| ((slack P p s)^2)
def choir (q:ℝ):Prop:=
 (0<shimmer q ∧ 3*(shimmer q*Diadem.tariff C (diameter q))≤1) ∧
 ∀ t, Strut q t→ clothR (radiusB q) + paddle (radiusB q) + (C).ℓ<t

set_option maxHeartbeats 160000 in
theorem flares {t a b} (h:merrier P s i k)
   (W:Worthy P s i k p f 1 a b)
   (E:appointments P p f s i)
   (c:choir P x)(g:Strut x t)(v:t%2=0):Flash P p f s i k d t:=by
 have r:4*t ≤ (RegNum P s i).val:= le_trans (le_trans (strut_d g).2 (Nat.le_add_right ..)) E.1
 obtain ⟨u,w,L⟩:= h
 obtain ⟨q,j,o,l⟩:=smooth P p s i k d
 let n0:=corona P s i k
 have e': n0+paddle (Γ).p.B + (C).ℓ<t:=by unfold n0 corona;rw [d.hot.claims];exact c.2 _ g
 refine ⟨Fview P p s i k d (by omega) v r,?_⟩
 have ht:=flown _ j q l t
 have m:appropriate P p s i k d ((slack P p s)^2) (mural (stone P p s i k d) t n0):=
    crown _ o v (by omega) r j ht.1 ht.2


 let a0:=solder P.run i k w.depth s
 have j1:Marble (Journey.compass P.run i k s) a0:= L w.depth
 have j2:Twosome C Ω a0:= revive P.run P.large s i k w
 have j3:∀h,cows h (Lattice.halo (paddle (Γ).p.B) (mural (stone P p s i k d) t n0).S) (diameter (scaleM P s)) :=patio _ (by omega) (strut_d g).2
 have hz:= pearls f d W (w:=diameter (scaleM P s)) E.1 j1 j2 (terrain P.run P.large (P.run.ir i) s).symm c.1.1 (one_le_pow₀ (ease_one P p s)) c.1.2 E.2 (mural (stone P p s i k d) t n0) m j3
 exact hz
open Garter Gleam Gleam.clocks
lemma hymn:∀ᶠ y in atTop, choir P y:=by
 filter_upwards [haze,peaks.eventually_ge_atTop ((C).ℓ+50:ℝ),harvest C 1,
   eventually_gt_atTop (0:ℝ)] with y h u t v
 have a:0< meterC y:=by unfold meterC BProof.coin; positivity
 constructor
 · refine ⟨mul_pos (by norm_num) a,?_⟩
   have d:0 ≤ oar y:=by unfold oar; positivity
   have e:3*(shimmer y*Diadem.tariff C (diameter y)) ≤
        3*(3*(Medal.dusk y*Diadem.tariff C (diameter y))) := by
      have r:shimmer y≤3*Medal.dusk y:=by unfold shimmer Medal.dusk; linarith
      have:= mul_le_mul_of_nonneg_right r (tariff_pos C (diameter y)).le
      linarith only [this]
   have b:0≤ tiltB y:=by unfold tiltB;positivity
   have f:= (mul_le_of_le_one_right b t.2.1)
   exact e.trans <|le_trans (mul_le_mul_of_nonneg_left (t.2.2.2.trans f) (by norm_num:(0:ℝ)≤3)) (by linarith only [t.1])
 intro n' p

 have j: ↑(radiusB y)≤wp y := h
 have hn: (↑(clothR (radiusB y) + paddle (radiusB y) + (C).ℓ):ℝ)<wp y^4:=by
    have j3:=pow_le_pow_left₀ (Nat.cast_nonneg _) j 3
    have b: (40:ℝ) ≤wp y:=le_trans (by linarith [(Nat.cast_nonneg (α:=ℝ) (C).ℓ)] : (40:ℝ) ≤ _) u
    have f:=pow_le_pow_right₀ (spire y) (by decide : 1 ≤ 3)
    change wp y ^ 1 ≤ wp y ^ 3 at f
    unfold clothR paddle cape_B
    push_cast
    linarith only [u,j,j3,b,
       mul_le_mul_of_nonneg_left b (pow_nonneg (zero_le_one.trans (spire y)) 3), f]
 exact_mod_cast hn.trans_le ((pow_le_pow_right₀ (spire y) (by decide:4≤99)).trans p.1)


lemma moments(h:choir P x):∀ᶠ i':ℕ in atTop,appointments P p f s i':=
 ((count_grows P.run s).eventually_ge_atTop (diameter x+addgap C)).and <|
  (count_grows P.run s).eventually (ramp (mul_pos h.1.1 (tariff_pos ..))
    (abs_nonneg _) (one_le_pow₀ (ease_one P p s)))

def Rosette:Prop:=
 ∀ f',∀ᶠ s':ℕ in atTop,
 ∀ᶠ i':ℕ in atTop,∀ k',merrier P s' i' k'→
  ∀d t,Strut (scaleM P s') t→ t%2=0→ Flash P p f' s' i' k' d t

theorem finery(h:Windfall P p):Rosette P p:=by
 intro f
 obtain ⟨_,_,_,_,u⟩:=h
 have a:=u f 1
 unfold onReg at a
 filter_upwards [a,(turnover P.par).eventually (hymn P)] with s' b c
 filter_upwards [b,moments P p f s' c] with i' v g k' r d t j y
 exact flares P p f s' i' k' d r (v k' r.1) g c j y
#print Rosette
#check P
end YM.CF.Merino.Mitre 

