import ZecaLatticeFieldEstimates
import ZecaPitcher
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


private lemma latticeFieldEstimates_pitch {M:Hilbert}{j:Axis}(C: OS.Semigroup M j)
 {u v:ℝ≥0}(x:0<u)(y:0<v) {t:ℕ→ℝ≥0}
 (p:Tendsto t atTop (𝓝 0))(q:∀ᶠ i in atTop,0<t i) {g:ℕ→M.Op}{V:M.Op}
 (wg:LatticeFieldEstimates M atTop g V):
 LatticeFieldEstimates M atTop (fun i=>Stellar.growth C (t i) u v (g i)) (ladle C u v V):=by
 exact (((LatticeFieldEstimates.pops (star_conv C p q x)).mul wg).mul (LatticeFieldEstimates.const _)).sub (((LatticeFieldEstimates.const _).mul wg).mul
      (LatticeFieldEstimates.pops (star_conv C p q y)))

variable (F:P.Nib 3 x)(D:ℕ→P.Apron)
 (y:P.Iguana 3 x F D)
 (v:Tendsto (fun i=> (D i).s) atTop atTop)
local notation "W" n:max => fun i=>P.ladder (D i) n
local notation "d" i:max=> bell (timeMesh P.par) (D i).s 1
include v in
lemma steam0:Tendsto (fun i=> bell (timeMesh P.par) (D i).s 1) atTop (𝓝 0):=
    (P.macroStep_zero.comp v).congr (fun i => by rw [bell,Int.cast_one,one_mul];rfl)
include v y
lemma ladder0(n:ℕ):
 Tendsto (fun i=> (P.ladder (D i) n).realWidth P 3) atTop (𝓝 0):=by
 simpa only [mul_zero,add_zero,P.ladder_width] using
    (y.thin.add ((P.steam0 D v).const_mul (n:ℝ)))
omit v y in
lemma dyelight{m n:ℕ→ℝ}{B:ℕ→P.Apron}{a b:ℝ}
 (f:P.Iguana 3 x F B)
 (p:0<a)(q:0<b) (ma:Tendsto m atTop (𝓝 a))(nb:Tendsto n atTop (𝓝 b)):
 LatticeFieldEstimates (P.ManyF 3 x) atTop
    (fun i=> P.ruby 3 x (B i) 0 (m i) (n i)) (F a b):=by
 exact f.read p q ma nb
lemma charge_pitcher(n:ℕ): P.Iguana 3 x (P.pitchJar x F n) (W n):=by
 induction n with
 | zero=>
    refine ⟨y.pay,P.ladder0 x F D y v _,fun a b p q=>?_⟩
    refine (y.dye a b p q).congr' ?_
    filter_upwards [y.nib.fit p q] with i ⟨h,m⟩
    rw [P.rungs_zero x (D i) _ _ h m]
 | succ n ih=>
    rw [pitchJar,Function.iterate_succ_apply']
    let J:=P.pitchJar x F n
    refine ⟨NibPay.notched P x _ ih.pay,P.ladder0 x F D y v _,fun a b p q=>?_⟩
    let e(i:ℕ):=whenly (timeMesh P.par) (D i).s 1
    have eh(i:ℕ):0<e i:=when_pos _ _ 1 Nat.one_pos
    have eg:Tendsto e atTop (𝓝 0):= NNReal.tendsto_coe.mp
     ((P.steam0 D v).congr (fun i=>natural_time ..))
    have x':=half_pos p; have w':=half_pos q
    have t:=P.dyelight x J ih x' w'
        tendsto_const_nhds (show Tendsto (fun i=>b/2-d i) atTop (𝓝 (b/2)) by
            simpa only [sub_zero] using (P.steam0 D v).const_sub (b/2))
    have he:=latticeFieldEstimates_pitch S (Real.toNNReal_pos.mpr x') (Real.toNNReal_pos.mpr w')
                  eg (Eventually.of_forall eh) t
    refine he.congr' ?_
    have h:=P.ladder0 x F D y v (n+1)
    filter_upwards [h.eventually_le_const x',h.eventually_le_const w'] with i m n'
    exact (P.rungs_grow x (D i) n p q m n').symm

lemma pours_trophy (q:Prism) :
 P.Iguana 3 x (P.trophy x F q) (fun i=>P.aTuba q (D i)):=by
 let Z:=lastTuba q + 1
 have h:Tendsto (fun i=> (P.aTuba q (D i)).realWidth P 3) atTop (𝓝 0):=by
     simpa only [mul_zero,add_zero,P.tuba_width,Z,Function.comp_apply] using
        (y.thin.add ((P.macroStep_zero.comp v).const_mul (Z:ℝ)))
 have x' n:=P.charge_pitcher x F D y v (n+1)
 refine ⟨NibPay.sum q.support _ (fun n _=>NibPay.smul (q n) (x' n).pay),h, fun a b m n=>?_⟩
 have nd(index:ℕ): LatticeFieldEstimates (P.ManyF 3 x) atTop (fun i=>q index • P.ruby 3 x
         (P.ladder (D i) (index+1)) 0 (a+d i) (b-d i))
       (q index • P.pitchJar x F (index+1) a b):=by
    have hg : Tendsto (fun i=>b-d i) atTop (𝓝 b):= by simpa using (P.steam0 D v).const_sub b
    have hj : Tendsto (fun i=>a+d i) atTop (𝓝 a):= by simpa using (P.steam0 D v).const_add a
    exact (P.dyelight x _ (x' index) m n hj hg).smul _
 refine (LatticeFieldEstimates.sum q.support _ _ (fun j _=>nd j)).congr' ?_
 filter_upwards [h.eventually_le_const m,h.eventually_le_const n] with i f t
 exact (P.aTuba_ruby x (D i) q a b f t).symm
