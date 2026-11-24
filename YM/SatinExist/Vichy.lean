import YM.SatinExist.Toast
import YM.SatinExist.Chocolate
import YM.SatinExist.Marina
/-! # Price the unbounded-order (over j) Test Card at true widths. Laurent. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 680000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste
namespace Spine
open MacroGrid
open CF.Lamour.Bridge
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open SatinTails SatinJets Boundary Spectral
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
variable (P:Spine)(x:P.Spectrum0 3)
local notation "C"=>P.calibration
local notation "M"=>timeMesh P.par
local notation "X"=>P.ColorHil 3 (P.advocate 3 x 3)
local notation "Y"=>P.ManyF 3 (P.advocate 3 x 3)
local notation "ℰ" => P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "R"=>P.seasons 3 (P.advocate 3 x 3)
local notation "Λ"=>P.kiosk 3 (P.advocate 3 x 3)
local notation "E"=> (ℰ).E
local notation "U"=> (R).E
local notation "V"=>P.advocate 3 x 3
local notation "E!" s:max i:max=> whenly (timeMesh P.par) s i
local notation "q'" n:max=> P.probeClock n 3
variable (F:P.Apron)
noncomputable def gearT(n:ℕ):P.Apron:=
 { s:=F.s
   F:=P.tubaField F.s F.F n
   S:= P.tubaStencil F.S n
   u:= fun i=> F.u i+n
   pos:= fun i=> (F.pos i).trans_le (by omega)
   bay:= P.tuba_bay F.s _ _ _ F.bay
   realM:=P.tuba_real F.s _ _ F.realM
   shelter:= fun i=> P.tubaShelter i (F.shelter i) n}
lemma gearH (n:ℕ): gearT P (gearT P F n) 1= gearT P F (n+1):=by
 unfold gearT tubaField tubaStencil; simp [Nat.add_assoc,tubaStencil,tubaField]
lemma gear0 : gearT P F 0=F:=rfl
local notation "Ψ" L:max a:max t:max => P.pillar 3 V L (- (a:ℝ)) (t:ℝ) 0
variable {a b:ℝ≥0}
lemma ztd (n:ℕ): P.zt (P.gearT F n)= P.zt F + whenly (timeMesh P.par) F.s n:=by simp [zt, gearT,whenly,add_mul]
-- augmentation at tight cards
lemma salve :
    let G:=P.gearT F 1; let L:=E (P.burst F.s); let A:=F.engine P 3 (P.advocate 3 x 3)
    G.engine P 3 (P.advocate 3 x 3)=(duration (P.burst F.s))⁻¹ • (L*L*A-L*A*L):=by
 intro G L A
 let f:= F.u 3; let e':= f+f; let p:= F.F; let D:= G.u 3; have h:D=f+1:=rfl; have ht:0< D:= G.pos 3; have hp:0 < f:=F.pos 3
 have hf:= P.meterRule0 3 V F
 let d:= P.burst F.s; let c:=(duration d)⁻¹
 have he:P.PrismS 3 V F.s (D+D) (add_pos ht ht) (c • P.shifts 3 (D:ℤ) (P.shifts 3 1 F.F)) (c • (L*L*A)):=by
    have hy:=P.cashOne 3 V (n:=F.s) (w:=1) zero_lt_one; have hz:= P.cashMul 3 V (P.cashMul 3 V hy hy) hf; let g:ℕ:=1+1+(f+f)
    have hr:P.PrismS 3 V F.s (1+1+(F.u 3+ F.u 3)) (by omega) (P.shifts 3 (D:ℤ) (P.shifts 3 1 F.F)) (L*L*A):=by
       change P.PrismS 3 V F.s _ _ (P.shifts 3 (D:ℤ) (P.shifts 3 1 F.F)) (L*L*A); rw [P.shifts_sum]; rw [one_mul, map_one,one_mul,P.shifts_sum] at hz
       rw [show (D:ℤ)+1=↑(1+1:ℕ)+ (F.u 3:ℕ) from ?_]; · exact hz
       unfold f at h; omega
    let e{v w:ℕ}{u p}{i:P.Test}{X':(X).Op}(g:v=w)(x':P.PrismS 3 V F.s v u i X'): P.PrismS 3 V F.s w p i X':=by subst v; exact x'
    have hh:=P.prismS_astr 3 V F.s g (by unfold g; omega) c hr (P.prism_null 3 V F.s g (by unfold g; omega)); rw [add_zero,add_zero] at hh
    exact e (by unfold g; omega) hh
 have hv:= P.cashOne 3 V (n:=F.s) (w:=1) zero_lt_one
 have hb:=P.cashMul 3 V (P.cashMul 3 V hv hf) hv
 rw [one_mul,P.shifts_sum, map_one,mul_one] at hb
 have ha:P.PrismS 3 V F.s (D+D) (add_pos ht ht) (P.shifts 3 D F.F) (L*A*L):=by
    have g : (↑D:ℤ)=↑(1:ℕ)+(F.u 3:ℕ):=by unfold f at h; omega
    rw [g];
    let e{v w:ℕ}{u p}{i:P.Test}{X':(X).Op}(g:v=w)(x':P.PrismS 3 V F.s v u i X'): P.PrismS 3 V F.s w p i X':=by subst v; exact x'
    exact e (by unfold f at h; omega) hb -- tune
 refine P.values_too 3 V F.s (D+D) (add_pos ht ht) (P.meterRule0 3 V G) ?_
 have hg:= P.prismS_astr 3 V F.s (D+D) (add_pos ht ht) (-c) ha he
 rw [show G.F=c • (P.shifts 3 1 F.F-F.F) from rfl,map_smul,map_sub];
 change P.PrismS 3 V F.s (D+D) (add_pos ht ht) (c • _) (c • _); rw [show (-(c:ℂ) • P.shifts 3 D F.F+c • P.shifts 3 D (P.shifts 3 1 F.F) :P.Test) = c • ((P.shifts 3 D) (P.shifts 3 (1:ℤ) F.F)-P.shifts 3 D F.F) from (by module),show -c • (L*A*L)+c • (L*L*A) = c • (L*L*A-L*A*L) from (by module)] at hg; exact hg
-- at larger p and common: use min engine rule and translate heat. Exponents
lemma voucher_LocalFieldBounds (r:ℕ)(a:ℝ≥0)(h:P.zt (P.gearT F 1)≤ a) :
    (Ψ (P.gearT F 1) ((a+a:ℝ≥0):ℝ) ((a+a:ℝ≥0):ℝ))= jerk (r:=r) (R) (P.burst F.s) (Ψ F a a) a:=by
 let G:=P.gearT F 1; let d:= P.burst F.s; let u:= P.zt F
 have ht:P.zt G=u+d:=P.ztd F 1
 have hg:P.zt G≤a:=h
 let v:=a-u; let z:=a+a-P.zt G; have hp:u+d≤a:=ht ▸ h
 have hz: d ≤ a:= le_trans le_add_self hp
 have hu: u ≤ a:=le_trans le_self_add hp
 have hw0:u+v=a:=add_tsub_cancel_of_le hu
 have hw:z+(u+d)=a+a:=by rw [←ht]; exact tsub_add_cancel_of_le (hg.trans le_self_add)
 let A:=Λ (F.engine P 3 V); let L:= U d; let c:= (duration d)⁻¹
 have hs: Λ (G.engine P 3 V)= c • (L*L*A-L*A*L):=by
    have hf:=P.salve x F; change Λ ( (P.gearT F 1).engine P 3 V)=_; rw [hf,P.kiosk_scale]; apply congrArg (fun p:(Y).Op=> c • p)
    obtain ⟨Q,hQ⟩:= P.kioskL 3 V; have hb (a b:(X).Op): Λ (a-b)=Λ a-Λ b:=by rw [←hQ, ←hQ,←hQ,map_sub]
    rw [hb]; let W:=F.engine P 3 V
    have he: Λ (E d*E d*W)=L*L*A:=by
       have hg:=P.projectionLingo x W (d+d) 0
       rw [(ℰ).time,(ℰ).eZero, show ContinuousLinearMap.id ℂ _ = (1:(X).Op) from rfl,mul_one,(R).time,(R).eZero, show ContinuousLinearMap.id ℂ _=(1:(Y).Op) from rfl,mul_one] at hg; exact hg
    rw [←he]; exact congrArg₂ (· - ·) rfl (P.projectionLingo x _ _ _)
 change (Ψ G ((a+a:ℝ≥0):ℝ) ((a+a:ℝ≥0):ℝ))= _
 rw [stampPoint _ x _ _ _ (hg.trans le_self_add) (hg.trans le_self_add), hs, stampPoint _ x _ _ _ hu hu, jerk]
 change U z * (c • (L * L* A - L*A* L))*U z = c • (U (a+d) * (U v*A*U v) * U (a-d) - U a * (U v*A*U v)* U a)
 rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; apply congrArg (fun p:(Y).Op=> c • p); rw [mul_sub,_root_.sub_mul];
 have rH (t s:ℝ≥0):U t* U s= U (t+s):=((R).time t s).symm
 have hv: z+d = a+v:= by
    apply add_right_cancel (b:=u); calc -- tune
         _=a+a:= by convert hw using 1; ac_rfl
         _= a+v+u:=by nth_rw 2 [←hw0]; ac_rfl
 have hb: z = v + (a-d):=by apply add_right_cancel (b:=d); rw [hv,add_assoc,tsub_add_cancel_of_le hz,add_comm a]
 apply congrArg₂ (·-·)
 · calc
    _= (U z*L*L)* A* U z:=by simp only [mul_assoc]
    _= (U (a+d)* U v)*A*(U v*U (a-d)):=by rw [rH,rH,rH,(by change z+d+d = a+d+v; rw [hv]; ac_rfl : z+d+d = _),rH,← hb]
    _=_:=by simp [mul_assoc]
 calc
    _= (U z*L)* A * (L*U z):=by simp only [mul_assoc]
    _= (U a * U v)*A*(U v* U a):=by rw [show L= U d from rfl,rH,rH,rH,rH,hv, add_comm d z,hv,add_comm a v]
    _=_:=by simp only [mul_assoc]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
