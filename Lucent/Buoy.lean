import Lucent.Bay
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

open Vale
open Worth.Pays Jewel WakeInvestment Regis Gleam Pressure Laurent
open Gleam.Wake
local notation "X" => hat P.R.L P.x s
local notation "σ" => sPow P s
variable {I:Type} [Fintype I] {m d:ℕ}
/-- Exponent inflation. separate gauge degree and geometry cost. -/

def ripe (A:ℝ)(m:ℕ):= grass A+ 4*m+2
structure Annual (I:Type)[Fintype I](C A:ℝ) (m:ℕ) (P:Preparation)(s:ℕ):Prop where
   stage : CircusPrice P C A s
   fresh : 1≤ sPow P s 2
   bar : ∀ {ρ:ℝ}, |ρ|≤2*bornQ P s→ |ρ| * temp (hat P.R.L P.x s) ≤ sPow P s 2
   raise : sPow P s (grass A) ≤ sPow P s (ripe A m)
   priceA : C ≤ sPow P s (ripe A m)
   pier : (Fintype.card (Tint I):ℝ) ≤ sPow P s (ripe A m)
   scaled : C * sPow P s 2 ^ m ≤ sPow P s (ripe A m)
   sails : ∀ {w e:ℕ}, (e:ℝ) ≤ sPow P s A → (w:ℝ) ≤ sPow P s A→ ∀ {t:ℝ}, 0≤t → t≤ sPow P s 2→ let x:=hat P.R.L P.x s
      C * sPow P s 2 ^ m * Staff.armRent e (skyline x) t w ≤ scratch x

open Regis.Wake
lemma yearly (I:Type)[Fintype I] (m:ℕ)(P:Preparation) {C A:ℝ}(h:0≤C)(p:0<A): ∀ᶠ s in atTop, Annual I C A m P s := by
 let B:=ripe A m; have hm:0≤ (m:ℝ):=Nat.cast_nonneg _
 have hr:grass A < B:=by unfold B ripe; linarith only [hm]
 have hB:0<B:=lt_trans (by unfold grass; positivity) hr
 have ht:(2:ℝ)*m < B:=by unfold B ripe grass; linarith only [p,hm]
 let T:=fun x=>2*Real.sqrt x*temp x
 have hv:Worth.Pays 0 1 0 T:= by
    refine Worth.Pays.fix (Worth.Pays.scale 2 (whole 0 1 0)) ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x z; unfold T; rw [Head.Garland.era x z,←BProof.thresh_eq z,BProof.thresh,mul_assoc,BProof.coin_mul]; norm_num
 let W:=whole 0 A 0; let D:=whole 0 2 0
 let x:=whole 0 (grass A) 0
 have y:= Worth.Pays.scale C (pot D m)

 have z:= times y (times (times (Worth.Pays.scale (2*SU.group.colorScale) (plus W (Worth.Pays.scale 4 W))) (whole (-120000/400000) 0 0)) D)
 let v:=leap (w:=0) (p:=B) (q:=0) y (by apply Or.inr; left; exact ⟨zero_mul _,ht⟩)
 let b:=leap (w:= -7/400000) (p:=0) (q:=0) z (Or.inl (by ring_nf; norm_num))
 filter_upwards [CircusPrice.ready P C A h p,grow_e 2 1 (by norm_num) P, (turnover P).eventually (leap (w:=0) (p:=2) (q:=0) hv (Or.inr (Or.inl ⟨rfl,by norm_num⟩))), (turnover P).eventually (leap (w:=0) (p:=B) (q:=0) x (Or.inr (Or.inl ⟨rfl,hr⟩))),grow_e B C hB P,grow_e B (Fintype.card (Tint I)) hB P,(turnover P).eventually v,(turnover P).eventually b] with s hp h₁ h₂ h₃ h₄ h₅ h₆ h₇
 refine ⟨hp,h₁,fun u=>le_trans (mul_le_mul_of_nonneg_right u (Work.E04.temp_nonneg _)) h₂,h₃,h₄,h₅,h₆,?_⟩

 intro w e hu he t z₂ z₃ X'
 apply le_trans _ h₇
 change _≤ C*sPow P s 2 ^m * Staff.armRent (sPow P s A) (skyline X') (sPow P s 2) (sPow P s A)
 have hl:0≤ skyline X':=(chip_pos ..).le
 have hg:=SU.group.colorScale_pos
 have hy:0≤ sPow P s A:= (BProof.coin_pos ..).le
 unfold Staff.armRent; gcongr
