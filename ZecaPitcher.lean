import SatinThinFusionTrumpets
import ZecaChord
import ZecaStar
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

set_option maxHeartbeats 600000
variable (P: Spine)(x:P.Spectrum0 3)
local notation "S"=> P.seasons 3 x
local notation "T" => timeMesh P.par
open SatinJets.Stellar

variable (A:P.Apron)(n:ℕ)
local notation "r"=> A.realWidth P 3
local notation "δ"=> bell (timeMesh P.par) A.s 1
local notation "h"=>whenly (timeMesh P.par) A.s 1
local notation "W" n:max=> P.ladder A n
local notation "G"=>P.ruby 3 x
lemma rungs_grow {a b:ℝ}
 (p:0<a)(q:0<b)
 (i:(W (n+1)).realWidth P 3 ≤ a/2)(u:(W (n+1)).realWidth P 3 ≤ b/2):
 P.ruby 3 x (W (n+1)) 0 a b=
    Stellar.growth (S) (whenly T A.s 1) (a/2).toNNReal (b/2).toNNReal
        (P.ruby 3 x (W n) 0 (a/2) (b/2-δ)):= by
 rw [P.rungs_next x A n a b (i.trans (half_le_self p.le)) (u.trans (half_le_self q.le)), growth_eq]
 set α:=a/2; set θ:=b/2
 have p':0≤α:= (half_pos p).le
 have q':0≤θ:= (half_pos q).le
 have t:δ=(h:ℝ):=natural_time ..
 have r₀:0≤δ:=t ▸ NNReal.coe_nonneg _
 have w0:(W (n+1)).realWidth P 3=(W n).realWidth P 3+δ:=by
      rw [P.ladder_width,P.ladder_width,Nat.cast_add,Nat.cast_one]; ring
 have v:(W n).realWidth P 3≤α:=by rw [w0] at i; linarith only [i,r₀]
 have w:(W n).realWidth P 3≤θ-δ:= le_sub_iff_add_le.mpr (w0 ▸ u)
 let U:=P.ruby 3 x (W n) 0 α (θ-δ)
 have l:=(P.ruby_large 3 x (W n) (α+δ) θ
   (show α+δ+α=a+δ by dsimp [α]; ring) (show θ-δ+θ=b-δ by dsimp [θ]; ring) (add_nonneg p' r₀) q' v w 0)
 have j:=P.ruby_large 3 x (W n) α (θ+δ) (show α+α=a by dsimp [α]; ring) (show θ-δ+(θ+δ)=b by dsimp [θ]; ring) p' (add_nonneg q' r₀) v w 0
 rw [←l,←j]
 unfold buff
 rw [bun_here,bun_here, Real.toNNReal_add p' r₀,Real.toNNReal_add q' r₀, t,Real.toNNReal_coe]
variable (F:P.Nib 3 x)
def notchD : P.Nib 3 x:= fun a b=>
 ladle (P.seasons 3 x) (a/2).toNNReal (b/2).toNNReal (F (a/2) (b/2))
lemma NibPay.notched (y:P.NibPay 3 x F):
 P.NibPay 3 x (P.notchD x F):=by
 obtain ⟨c,d,u,v⟩:=y
 refine ⟨c * 8 * 2^d, d+1,by positivity,fun t p q=>?_⟩
 apply (ladle_pay (S) (half_pos p) _).trans
 apply (mul_le_mul_of_nonneg_right (v _ (half_pos p) ((half_le_self p.le).trans q)) (by positivity : (0:ℝ) ≤ 4/(t/2))).trans
 rw [div_pow,pow_succ]
 exact le_of_eq (by field_simp; ring)

def pitchJar (n:ℕ):= (P.notchD x)^[n] F
def trophy (D:Prism):P.Nib 3 x:=fun a b=>∑i∈D.support,D i • P.pitchJar x F (i+1) a b
#check pitchJar
