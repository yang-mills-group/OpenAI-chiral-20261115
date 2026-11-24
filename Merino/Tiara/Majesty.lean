import Merino.Tiara.Corsage
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open BProof Hive Swell Hem Merino.Mitre Plume
open Afterglow Tower Lifted Journey

open Py.Rate.LocalLimit Preparation Tower.VacuumSelection
open Medal Lace Cuff Swell Hem
variable (P:Spine)(p:Bolts)(s i k:ℕ)
local notation "Ω"=>RegNum P s i
local notation "Γ"=>LedgerM P s i k
local notation "K"=> LoomM P s i

open scoped InnerProductSpace
variable {C:Constellation}
local notation "D"=> P.calibration
local notation "H"=> Lace.pole
local notation "n"=> (priceTick P)
local notation "x"=> (scaleM P s)
variable {r:ℕ→ℕ}(a:StrictMono r)
 {F:ℕ→LinksC→ℂ}{g:LinksC→ℂ}
 {X:ℕ→Reins P.calibration}{J:Reins P.calibration}
 (M:Carol P p C r s F g X J)

/-- amplified clear pose factor: Q=Qprice, T=1/τ², 
Y at scale TQ. Z' at scale TQ, Jhat at scale Q. -/
abbrev Tcoef:ℝ:=(tempM P s ^ 2)⁻¹
abbrev booster:ℝ:=Py.stemS x
abbrev col(P:Spine)(s:ℕ):= Lattice.box (etch P s)
abbrev august (t:ℕ) (f:LinksC→ℂ)(j:Reins P.calibration):Horse D:=
 roses D n H (t/2:ℕ) (clearM P s) f j
abbrev beret (j:Reins P.calibration)(i:Axis):Horse D:= tassels D (Qprice P s) j i
lemma scepter(g:LinksC→ℂ)(J:Reins P.calibration)(t:ℕ)(even:t%2=0):
 august P s t g J=half P s t g+
  (Tcoef P s:ℂ) • Tower.chime D H (t/2:ℕ) (rolling D n (beret P s J)):=by
 rw [august,sword _ _ _ _ _ (Q:=Qprice P s) (T:=Tcoef P s) _ _ (by unfold clearM Tcoef;rw [div_eq_mul_inv,mul_comm])]
 have z:danceAt H (t/2:ℕ)=Lace.noon t:=by
    unfold danceAt; rw [show 2*((t/2:ℕ):ℤ)=(t:ℤ) by omega]
 rw [z]

lemma orb(g:LinksC→ℂ)(J:Reins P.calibration)(t:ℕ):
 roses D n H (t/2:ℕ) (hueM P s) g J=(booster P s:ℂ) • august P s t g J:=by


 have h:hueM P s=booster P s * clearM P s:=mul_comm ..
 unfold august roses
 rw [smul_sum,h]
 refine sum_congr rfl fun i0 _=>?_
 rw [smul_comm]; exact congrArg ((Hem.ramp i0:ℂ) • ·) (front P i0 _ _ _ _)


abbrev Unison (P:Spine)(p:Bolts)(C:Constellation)
 (r:ℕ→ℕ)(f s:ℕ)(F:ℕ→LinksC→ℂ)(g:LinksC→ℂ)
 (X:ℕ→Reins P.calibration)(J:Reins P.calibration):Prop:=
 Carol P p C r s F g X J ∧
 (∀j,Elite (col P s) (fun u=>beret P s (X u) j) (beret P s J j)) ∧
 ∀ t,Strut (scaleM P s) t→t%2=0→
 Elite (couch P s t) (fun u=>august P s t (F u) (X u)) (august P s t g J) ∧
 ∃U V:P.Vox Lace.pole s, U.val=august P s t g J ∧ V.val=Plume.half P s t g ∧
    (booster P s)^2*‖P.piece Lace.pole s U‖^2 ≤ mPrice (gold P s f) ∧
    Ct C*cost₀ P s t^2 ≤ ‖P.piece Lace.pole s V‖^2

variable (f:ℕ)(w:
   ∀ᶠ i in atTop, ∀k, merrier P s i k →∀d t,Strut (scaleM P s) t→t%2=0→∀σ,Wickday P p f s i k d t σ)
include M a w
lemma laurels
 (l:∀ t,Strut (scaleM P s) t→t%2=0→ArenaLet P s t):
 Unison P p C r f s F g X J:=by
 refine ⟨M,brim M.rail _,fun t h v=>?_⟩
 have u:=cluster M.rail M.rolls n H (t/2:ℕ) (clearM P s)
 obtain ⟨_,_,V,m,_,y⟩:=M.stellar h
 let R:P.Vox H s:=⟨_,snapOK P s (l t h v) u.landing⟩
 refine ⟨u,R,V,rfl,m,?_,y⟩
 obtain ⟨W,j,i⟩:=procession P p s a M f w (l t h v) h v
 have e:W=(booster P s:ℂ) • R:=Subtype.ext (j.trans (orb ..))
 rw [e] at i
 let z:=arrows P.run P.large P.law P.history.circuit H 0 false (P.room H) s
 change ‖z ((booster P s:ℂ) • R)‖^2 ≤ _ at i
 rw [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at i
 exact i


/-- One subsequence of the unselected P prices, with all heights and
poly-radii parameters f (arbitrary but fixed before prices in s). Use
with scepter. -/
abbrev Throne(P:Spine)(p:Bolts)(C:Constellation):Prop:=
 ∃ (r:ℕ→ℕ)(F:ℕ→ℕ→LinksC→ℂ)(g:ℕ→LinksC→ℂ)
  (X:ℕ→ℕ→Reins P.calibration)(J:ℕ→Reins P.calibration),
    StrictMono r ∧ ∀f,∀ᶠ s in atTop,Unison P p C r f s (F s) (g s) (X s) (J s)
omit M a w in
lemma crowned (h:Hill P p C)(q: Charms P p):
 Throne P p C:=by
 obtain ⟨r,F,g,X,J,k,h⟩:=aria P p C h
 refine ⟨r,F,g,X,J,k,fun f'=>?_⟩
 filter_upwards [airborne P,h,q f'] with s d e j
 exact laurels P p s k e f' j d
end YM.CF.Merino.Tiara
