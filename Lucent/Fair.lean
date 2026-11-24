import Lucent.Breath
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
/- Exponent inflation. separate gauge degree and geometry cost. -/

open Regis.Circuit Regis.Head.Brecht Regis.Resonance Exterior Gist
open ProbabilityTheory Precision RG
local notation "vuseq"=> reachCost Y s i k 
local notation "Bd"=> P.V.L.H (Y.uv k-s)
local notation "GN"=> More (side Y i s)

open CF.Onyx
open Stationary (Gaia)
structure Hand where
 p : Gaia
 shade : PlaqAxes
def fair (d:I→Hand) (t z:Tint I):ℂ:= (sch (G:=SU.group) t.2 z.2:ℂ) * specter (d t.1).shade (d z.1).shade ((d t.1).p - (d z.1).p)
/-- gauge appointment, may be weakened to relative -/
def FairRoad (W:ℕ→I→Staff)(R:ℕ→ℝ)(d:I→Hand):Prop:=∀ j:I,
      (∀ᶠ n in atTop,(W n j).face.2=(d j).shade) ∧
      Tendsto (fun n=> riseX (R n) (W n j).face.1) atTop (𝓝 (d j).p)
lemma rising (r:ℝ)(x y:Cover): riseX r (x-y)=riseX r x-riseX r y:=by
 ext i; change (((x i-y i:ℤ):ℝ)/r:ℝ)= ((x i:ℝ)/r)-((y i:ℝ)/r); push_cast; ring

lemma fare_duet {S:ℕ→Side}{H:ℕ→Bed}{R:ℕ→ℝ}{d:I→Hand}{W:ℕ→I→Staff}{η ν V:ℝ} {q:Clip}
 (Q:Yard (fun n=>More (S n)) R)(g:FairRoad W R d)
 (U:∀ n,(H n).covered ν V)(v:∀ n,Floor (H n) q (More (S n)) η V)(a: 0 < ν)(b:0<V)
 {u:ℕ→ℝ}(h:Tendsto u atTop (𝓝 1))(t z:Tint I)(e:(d t.1).p ≠ (d z.1).p):
 Tendsto (fun n=> ((R n:ℂ)^2)^2* splitG (S n) (H n) (u n) (W n) t z) atTop (𝓝 (fair d t z)):= by
 let x(n):=(W n t.1).face.1; let y(n):= (W n z.1).face.1
 have ht:Tendsto (fun n=>riseX (R n) (x n-y n)) atTop (𝓝 ((d t.1).p-(d z.1).p)):=by simp_rw [rising]; exact ((g t.1).2.sub (g z.1).2)
 have he:= mercury (d t.1).shade (d z.1).shade (x:=(d t.1).p-(d z.1).p) Q (z:=fun n=>x n-y n) ht (sub_ne_zero.mpr e) U v a b

 let α:ℂ:= sch (G:=SU.group) t.2 z.2
 have hw:= ((tendsto_const_nhds (x:=α)).mul ((h.ofReal).pow 2)).mul he; rw [Complex.ofReal_one,one_pow,mul_one] at hw; apply hw.congr'
 filter_upwards [(g t.1).1,(g z.1).1] with n l j
 unfold splitG emittance; rw [←l,←j,magnify]; let N:=More (S n); let A:=plaquette (W n t.1).face.2; let B:=plaquette (W n z.1).face.2
 rw [rimflare _ _ _ _ _ (sub_zero (wrap N (x n-y n))),
   rimflare N (H n) (wrap N (x n)) (wrap N (y n)) (x n-y n) (map_sub (wrap N) (x n) (y n)).symm]
 ring
#check @mercury

def Dust (d:I→Hand) (L:List (Tint I)):= L.Pairwise (fun t z=>(d t.1).p≠(d z.1).p)
variable {ss ii kk:ℕ→ℕ}{R:ℕ→ℝ}{d:I→Hand}{ρ:ℕ→ℝ}{W:ℕ→I→Staff}
theorem vellFare
    (Q:Yard (fun n=>More (side Y (ii n) (ss n))) R)(g:FairRoad W R d)
    (h:Tendsto (fun n=> reachCost Y (ss n) (ii n) (kk n) (ρ n)) atTop (𝓝 1)) (L:List (Tint I))(e:Dust d L):
    Tendsto (fun n=> ((R n:ℂ)^2)^L.length * vell (splitG
        (side Y (ii n) (ss n)) (P.V.L.H (Y.uv (kk n) -ss n))
        (reachCost Y (ss n) (ii n) (kk n) (ρ n)) (W n)) L) atTop (𝓝 (vell (fair d) L)):= by
 simp_rw [←vellScale]
 let f(n):= Y.uv (kk n)-ss n
 apply vellTendsto
 exact List.Pairwise.imp (fun {a b} t=>fare_duet Q g (fun n=> cover_revise (P.V.L.roof (f n)).1 le_rfl (le_max_left P.K.C 1)) (fun n=> floor_revise ((P.V.L.roof (f n)).2.1 _) le_rfl (le_max_left P.K.C 1)) P.K.width (lt_max_of_lt_right (show (0:ℝ)<1 from zero_lt_one)) h a b t) e
#print axioms vellFare
