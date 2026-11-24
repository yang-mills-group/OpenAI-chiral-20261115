import Merino.Tiara.Side
import Merino.Mitre.Azure
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 620000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Tiara
open Merino.Mitre
open Fock Finset Lattice Lat Spire Scroll Cube Branch Skye Tenant RG BProof
open scoped BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Buffered
variable {N:Side}
open Brooch

open Roots Lamour.Bridge.Celeste.Clock Fabric Thera

open Cuff Lace Medal Garter
variable (F:Obs N)

open Swell Hem
variable {A:Sa N} {b t:ℕ}{c:ℝ}
lemma folds(u:LicenseY A F)(h:AtSupport false (purse b 0) (toMark F))
 (D:∀ V,‖F V‖≤c)(s:Sweep N):Sits F s b c:=by
 have j:LicenseY (purse b 0) F:=⟨h,u.bill,u.gauge_x⟩
 refine ⟨(inlay s j).loc.mono ?_,fun V=> (beaded s V.1 (F:=F)).trans_le (D _)⟩
 unfold purse mount Bide.regionD
 rw [←show Salt.actY s⁻¹ _ = Finset.map .. from rfl,←Salt.walkA]
 simp [Salt.actY,sitU]

lemma rim0(σ:Signed):boxA (rim N σ) 0=0:=by
 change (castX _).anon N _=_
 rw [stir_l,affine,Signed.act_zero]
 rw [show (rim N σ).b=0 by rfl, zero_add]
 rw [←Ratio.root_embed, map_zero]

variable (σ:Signed)
abbrev sun(t:ℕ)(σ:Signed):Sweep N:= Mitre.up t * rim N σ
abbrev eve(t:ℕ)(σ:Signed):Sweep N:= flipL pole 0 * sun t σ
def palm(t b:ℕ)(σ:Signed):Fabric N:=
 ⟨photo (ball F (sun t σ)),duet b (showtime (More N) t),0,0⟩
open CF.Pannier.Chancel StepIn
lemma chapel{r:ℕ}{z:Site N}(head:separation 0 (node z)≤b)
 (g:t%2=0)(L:b+paddle r<t)(R:4*t≤N.val)
 (h:Bide.plainP F)(U:Sits F (sun t σ) b c)(A:Sits F (eve t σ) b c):
 Ample F z (c^2) r (palm F t b σ):=by
 have m: (palm F t b σ).x=ball F (eve t σ)*ball F (sun t σ):=
    congrArg (· * ball F (sun t σ)) (posed pole 0 (sun t σ) h).symm
 have low:purse b (boxA (sun t σ:Sweep N) 0) = baseball b (matinee (More N) t).there:=by rw [sun,push_box,rim0,upfly g]
 have hi:purse b (boxA (eve t σ:Sweep N) 0)= baseball b (soiree (More N) t).there:=by rw [eve,sun,←mul_assoc,push_box,rim0];rw [show flipL pole 0 * Mitre.up t = (down t : Sweep N) from rfl,downfly g]
 have here(s:Sweep N):birthplace z s∈purse b (boxA s 0):=halo_spec.mpr ⟨_,mem_singleton_self _,(sitT s 0 _).trans_le head⟩
 have a:=here (sun t σ); rw [low] at a
 have d:=here (eve t σ);rw [hi] at d
 refine ⟨?_,?_,eve t σ,sun t σ,mem_union_right _ d,mem_union_left _ a,fardel a d _ L R,m⟩
 · rw [m]
   have y:=A.seat;rw [hi] at y;have v:=U.seat;rw [low] at v
   exact (y.mono subset_union_right).mulM (v.mono subset_union_left)


 intro V;rw [m,Pi.mul_apply,sq]
 exact (norm_mul_le ..).trans (mul_le_mul (A.cost _) (U.cost _) (norm_nonneg _) ((norm_nonneg _).trans (A.cost V)))


section
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
local notation "C"=>P.calibration
variable (d:Gown P p (priceTick P) s i k) (σ:Signed)

open Papal
def Wickday(t:ℕ)(σ:Signed):Prop:=
 let Q:=ball (stone P p s i k d) (sun t σ)
 AtSupport false (Buffered.band (RegNum P s i) Lace.pole 0 P.calibration.ℓ) Q ∧
 ‖Journey.compass P.run i k s (photo Q)‖≤ mPrice (gold P s f)
set_option maxHeartbeats 600000 in
theorem wickday {t a b} (h:merrier P s i k)
   (W:Worthy P s i k p f 1 a b)
   (E:appointments P p f s i)
   (c:choir P x)(g:Strut x t)(v:t%2=0):Wickday P p f s i k d t σ:=by
 have r:4*t ≤ (RegNum P s i).val:= le_trans (le_trans (strut_d g).2 (Nat.le_add_right ..)) E.1
 obtain ⟨u,w,L⟩:= h
 obtain ⟨q,j,o,l⟩:=smooth P p s i k d
 let n0:=corona P s i k
 have e': n0+paddle (Γ).p.B + (C).ℓ<t:=by unfold n0 corona;rw [d.hot.claims];exact c.2 _ g
 have ht:∀u,Sits (stone P p s i k d) u n0 (Mitre.slack P p s):=fun _=>folds _ (d.ticket.hem.licensed z) q l _
 refine ⟨(ht _).seat.mono ?_,?_⟩
 · rw [sun,push_box,rim0,upfly v];exact matinee_up (by omega) (le_trans (by omega) r)
 have m:appropriate P p s i k d ((Mitre.slack P p s)^2) (palm (stone P p s i k d) t n0 σ):=
    chapel _ σ o v (by omega) r j (ht _) (ht _)


 let a0:=solder P.run i k w.depth s
 have j1:Marble (Journey.compass P.run i k s) a0:= L w.depth
 have j2:Twosome C Ω a0:= revive P.run P.large s i k w
 have j3:∀h,cows h (Lattice.halo (paddle (Γ).p.B) (palm (stone P p s i k d) t n0 σ).S) (diameter (scaleM P s)) :=patio (F:=stone P p s i k d) (t:=t) (b:=n0) (by omega) (strut_d g).2
 have hz:= pearls f d W (w:=diameter (scaleM P s)) E.1 j1 j2 (terrain P.run P.large (P.run.ir i) s).symm c.1.1 (one_le_pow₀ (ease_one P p s)) c.1.2 E.2 (palm (stone P p s i k d) t n0 σ) m j3
 exact hz

def Charms:Prop:=
 ∀ f',∀ᶠ s':ℕ in atTop,
 ∀ᶠ i':ℕ in atTop,∀ k',merrier P s' i' k'→
  ∀d t,Strut (scaleM P s') t→ t%2=0→ ∀σ,Wickday P p f' s' i' k' d t σ

theorem favored(h:Windfall P p):Charms P p:=by
 intro f'
 obtain ⟨_,_,_,_,u⟩:=h
 have a:=u f' 1
 unfold onReg at a
 filter_upwards [a,(turnover P.par).eventually (hymn P)] with s' b' c'
 filter_upwards [b',moments P p f' s' c'] with i' v g k' r d t j y σ
 exact wickday P p f' s' i' k' d σ r (v k' r.1) g c' j y
end
end YM.CF.Merino.Tiara
