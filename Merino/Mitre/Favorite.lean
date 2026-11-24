import Merino.Coin.Spoils
import Merino.Mitre.Crystal

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
variable (P:Spine)(p:Bolts)(f:ℕ)(s i k:ℕ)
local notation "Ω"=>RegNum P s i
local notation "Γ"=>LedgerM P s i k
local notation "x"=>scaleM P s
local notation "n"=>priceTick P
local notation "K"=> LoomM P s i
local notation "z"=> hueM P s

variable {o:Site (RegNum P s i)}(d:Dress P s i k p (priceTick P) o)
abbrev appropriate (a:ℝ) (A:Fabric Ω):=Ample (d.y.opening K (Γ).p z) d.y.origin a (Γ).p.B A
abbrev gold (s f:ℕ):ℝ:=Corolla.cur P.par.R.L f (scaleM P s)
def plumelet(q:ℝ):=8+2*Real.log q
def shimmer(r:ℝ):=14*meterC r
lemma entire {q:ℝ}(h:0<q)(m:ℕ): aroma P.par q s (Ω) (2*m) (2*m) =
 Real.exp (m*plumelet q+shimmer x*sites Ω):=by
 unfold aroma
 nth_rw 1 [← Real.exp_log h]
 rw [←Real.exp_nat_mul,←Real.exp_add]
 congr 1
 unfold scaleM plumelet shimmer
 push_cast; ring


variable {P p s i k}
lemma allin {a b c:ℝ}(y:Worthy P s i k p f 1 a b)
 (U:List (Fabric Ω))(h:Sylvan (appropriate P p s i k d c) (paddle (Γ).p.B) U):
  ‖Journey.compass P.run i k s (buffet U)‖≤
   Real.exp (U.length*plumelet (gold P s f)+shimmer x*sites Ω):=by
 obtain ⟨J,g,u,r,v⟩:=flatten h
 let α:=Fin J.length
 let l:List α:=List.finRange _
 let t:=J.get
 let F:α → Obs (Ω):=trophy P p s i k (o₀:=fun _=>o) (fun _ :α=>d) t
 let j:=host d.y.origin ∘ t
 have hx:node ∘ j=sit d.y.origin J:=by rw [show node∘j=(node∘host d.y.origin)∘t from rfl, arrived]
 obtain ⟨m,w⟩:=guests _ J v
 rw [← hx] at m w
 have hc(j':α): inReach (Γ).p (j j') (t j') d.y:=by 
    change separation ((node∘j) j') (birthplace d.y.origin (t j')) ≤ _
    rw [hx]; exact (separation_self _).trans_le (Nat.zero_le _)
 have H : row F l=buffet U:=by
    rw [u,← List.map_get_finRange J,List.map_map]
    rfl
 rw [← H,←entire P s i y.bought.gate]
 have r':=Worthy.reward P p s i k y (o₀:=fun _ => o) j m (fun _=>d) _ hc _ w
 rw [Fintype.card_fin,List.length_finRange] at r'
 rw [←g]
 exact r'


open CF.Pannier.Chancel Diadem

lemma pearls {a b c:ℝ}(y:Worthy P s i k p f 1 a b)
 {w:ℕ}{L:Calibration}(E: w+addgap L≤ (RegNum P s i).val)
 {ν:Mark Ω→ℂ}{m:Side}
 (S:Marble (Journey.compass P.run i k s) ν)
 (R:Twosome L (RegNum P s i) ν) (G: RegNum P s i=L.c m)
 (D0:0<shimmer x)(hd:1≤c)(Y:3*(shimmer x*Diadem.tariff L w) ≤ 1)
 (v:Icicle (RegNum P s i).val (shimmer x*Diadem.tariff L w)
    |plumelet (gold P s f)| c)
 (A:Fabric Ω)(W:appropriate P p s i k d c A)
 (T:∀ j,cows j (Lattice.halo (paddle (Γ).p.B) A.S) w):
 ‖Journey.compass P.run i k s A.x‖ ≤ Real.exp 9 * (gold P s f)^2 :=by
 refine (Diadem.chess _ D0 (abs_nonneg _) hd (neg_abs_le _) v S
     (fun h=>flips (Bide.plain (allowedX (d.ticket.hem.licensed _))) h)
     (fun _ h=>h.keep)
     (fun _ h=>h.val)
     (allin f d y) R G E A W T).trans ?_
 have u:0<gold P s f:= y.bought.gate
 nth_rw 2 [← Real.exp_log u]
 rw [← Real.exp_nat_mul,← Real.exp_add]
 apply Real.exp_monotone
 unfold plumelet
 push_cast; linarith only [Y]
end YM.CF.Merino.Mitre
