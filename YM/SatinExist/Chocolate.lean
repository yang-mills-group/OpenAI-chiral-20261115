import YM.SatinExist.Pepper
import YM.SatinExist.Tipple
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 330000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste Ballad
namespace Spine
open MacroGrid
variable (P:Spine)(R : P.Register)(j:Axis)(C A:ℝ)(Y:Supplier)(T:uniform P R Y C A)(D:P.NightCop)
local notation "W"=>P.calibration
local notation "Λ"=>P.par
local notation "Ψ"=>P.run
local notation "H"=>P.large
local notation "ℓ"=>P.calibration.ℓ
local notation "b"=> ruler P.calibration.B
local notation "θ"=> P.tuneK
variable {w N a b':ℕ} {F:Weaver}{S:Finset Cover}(v: Lamour.Bridge.Celeste.Voice F S) (h:Clarity F P.par.K.j (1/4))
-- true shift & prism material rights on cards
section card
variable (x:P.Spectrum0 j){F:P.Test}{n w:ℕ}
local notation "E'" s:max i:max=> whenly (timeMesh P.par) s i
local notation "R'"=> P.physicalEnergy j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "Φ"=> P.colorSpace j x
lemma cashOne (p:0<w):P.PrismS j x n w p 1 (E (E' n w)):=
 ⟨SlabMark.identity P.run P.large n j false w,(enclave W).one_mem,rfl,P.tubePulse j x n w p⟩
local notation "ϕ" w:max p:max=> P.PrismS j x n w p
lemma cashMul {v:ℕ}{A0 B:(P.ColorHil j x).Op}{u:0<v}{p:0<w}{Y Z:P.Test}
    (h:P.PrismS j x n v u Y A0)(d:P.PrismS j x n w p Z B): P.PrismS j x n (v+w) (add_pos u p) (Y* (P.shifts j v Z)) (A0*B) :=by
 obtain ⟨F,h,rfl,rfl⟩:= h; obtain ⟨B',d,rfl,rfl⟩:= d
 obtain ⟨G,q,v,k⟩:=P.editPulse j x n u p F B' h d; exact ⟨G,q,v,k.symm⟩
lemma meterRule (A:P.Apron)(p:A.s≤n):P.PrismS j x n (A.zoom P n j+A.zoom P n j) (add_pos (A.zoomP P j n) (A.zoomP P j n)) (P.shifts j (A.zoom P n j) (A.full P n)) (A.engine P j x):=by
 obtain ⟨U,t,q⟩:= A.full_realizes P j n p; have h:P.voxTest j n U.val∈ enclave W:= t ▸ P.shifts_keep j _ (A.fullColor P n); exact ⟨U,h,t,congrArg (fun p:P.Physical j=>Φ p) (Subtype.ext q)⟩
lemma meterRule0 (A:P.Apron):P.PrismS j x A.s (A.u j+A.u j) (add_pos (A.pos j) (A.pos j)) (P.shifts j (A.u j) A.F) (A.engine P j x):=
 ⟨A.cardB P j,A.color P j,rfl,rfl⟩
lemma frontRule (Z:Lead.Clan) (n m:ℕ)(p:P.probeClock m j<w) (q:0<w):
    P.PrismS j x n (w+w) (add_pos q q) (P.shifts j w ((P.thinMat Z n m).F)) (E (E' n (w-P.probeClock m j))*(P.thinMat Z n m).engine P j x* E (E' n (w-P.probeClock m j))):=by
 let Y:=P.thinMat Z n m; have hv:Y.u j=P.probeClock m j:=rfl; let z:=w-Y.u j
 rw [←hv] at p ⊢ -- simp issue
 have hz:0<z:=by unfold z; omega
 let Ω:(P.ColorHil j x).Op:= E (E' n z)
 have h0:= P.cashOne j x (n:=n) hz
 have hi:= P.cashMul j x (P.cashMul j x h0 (P.meterRule0 j x Y)) h0
 simp only [one_mul,P.shifts_sum,map_one,mul_one] at hi -- P.shifts_sum
 have ht: (z:ℤ)+(Y.u j:ℤ)=w:=by unfold z; omega
 rw [ht] at hi
 let M:= (Ω * Y.engine P j x * Ω)
 change P.PrismS j x n (w+w) (add_pos q q) _ M -- tune
 -- integer arithmetic length
 convert hi using 1; unfold z; omega
end card
-- flag glamour
variable (Z:Lead.Clan)
private lemma melody {n:ℕ}(A:Lead n)(B:Side): ∃ Y:Ballad.Melody B n,Y.first=A:=by
 let X:= Ballad.direction (Ballad.sail false (Ballad.gap B n))
 let V:Lead n := { A with
     birth:= X+A.birth
     death:= X+A.death
     aligns:= congrArg (X+·) A.aligns |>.trans (add_assoc ..).symm
     moves:=by
        have h(y:Cover):nodeC (X+y)= 2 • X + nodeC y:=by unfold nodeC; rw [smul_add]; abel
        rw [h,h,Cube.stop_trans,A.moves] -- tune
     }; exact ⟨⟨A,V,rfl,rfl,false,add_comm ..⟩,rfl⟩
abbrev demerit (Z:Lead.Clan):ℂ:= (purePrice Z:ℂ)
lemma epaulet (δ:ℝ)(p:0<δ): ∀ᶠ n:ℕ in atTop, Clarity ((δ:ℂ) • ((P.flash n).groundWord Z - demerit Z • (1:Weaver))) P.par.K.j (1/4):=by
 let K:=P.par; have hf:1 ≤ K.K.j:=by unfold K; rw [P.par.kJ]; decide
 have e:= Melody.eraFlag K.block hf (show 0<(1/4:ℝ)/δ from (by positivity))
 filter_upwards [e] with n h
 obtain ⟨A,hA⟩:= melody (P.flash n) K.block; rw [←hA]
 have hp:= h A Z false
 filter_upwards [hp] with N g hg M x v; change ‖_‖≤_; simp only [Pi.smul_apply,map_smul,norm_smul]; rw [Complex.norm_real, Real.norm_eq_abs,abs_of_pos p, mul_comm]; exact (le_div_iff₀ p).mp (g hg M x v)
open Ballad
lemma crowning (n:ℕ)(z:ℝ): (P.tuneK (((flourish (P.flash n) Z).sub (((Voice.one _).hushed (demerit Z)))).hushed (z:ℂ))) =(z:ℂ) • (P.frontMat Z n-demerit Z • (1:P.Test)):=rfl -- maybe sub requires equal sets
section
include D
-- tune W.i
include T
lemma cardSerif {δ:ℝ} (p:0<δ):∀ᶠ n:ℕ in atTop,∃ (w:ℕ)(_ : P.probeClock n j<w),
    ∀ᶠ s:ℕ in atTop,∀ (x:P.Spectrum0 j), let Y:=P.thinMat Z s n; let E:= (P.physicalEnergy j x).E (whenly (timeMesh P.par) s (w-P.probeClock n j))
                                            ‖E*Y.engine P j x* E - demerit Z • (P.physicalEnergy j x).E (whenly (timeMesh P.par) s (w+w))‖ ≤ Real.sqrt (RedD+3)/δ:=by
 filter_upwards [P.epaulet Z δ p] with n h
 let v:= (flourish (P.flash n) Z); let q:= (v.sub ((Voice.one _).hushed (demerit Z))).hushed (δ:ℂ)
 obtain ⟨w,e,t⟩:= P.pay_arena R j C A Y T D q h (P.probeClock n j)
 refine ⟨w,e,?_⟩
 filter_upwards [t] with s hp x Y E
 let u:=(P.physicalEnergy j x).E (whenly (timeMesh P.par) s (w+w))
 let B:=P.colorSpace j x
 let t:=P.voxTest j s
 let X:P.ColorHil j x |>.Op:= E*Y.engine P j x* E
 have hx:0<w:=by omega
 have ht:0<w+w:= add_pos hx hx
 have hk:=P.prismS_astr j x s (w+w) ht (-demerit Z) (P.cashOne j x (n:=s) ht) (P.frontRule j x Z s n e hx)
 have hh:= P.prismS_astr j x s (w+w) ht (δ:ℂ) hk (P.prism_null j x s _ ht)
 rw [add_zero,add_zero] at hh
 have hF: (δ:ℂ) • (-demerit Z • (1:P.Test)+P.shifts j w Y.F)=P.shifts j w (θ q):= by rw [P.crowning,map_smul,map_sub,map_smul,map_one]; change _=(δ:ℂ) •(P.shifts j w Y.F-_); module
 rw [show P.shifts j (w:ℤ) ((P.thinMat Z s n).F)=P.shifts j w Y.F from rfl,hF] at hh
 obtain ⟨F,h0,Y',s⟩:= hh -- shadow s
 have hz: ‖(δ:ℂ) • (X-demerit Z • u)‖ ≤ Real.sqrt (RedD +3):=by
    rw [show X-demerit Z • u= -demerit Z • u+X from (by module), show (δ:ℂ) • _ = _ from s]
    exact (NonUnitalStarAlgHom.norm_apply_le B _).trans (hp F Y')
 rw [norm_smul,Complex.norm_real, Real.norm_eq_abs,abs_of_pos p,mul_comm] at hz; exact (le_div_iff₀ p).mpr hz
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
