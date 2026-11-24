import YM.SU5.SatinWard.Resolution.SparkM
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Laurent
variable {S:Type}{F: Ultrafilter S}{s:ℕ}(X': Cross s (F:Filter S)) {p:Stack}
local notation "X★"=> X'
local notation "Nβ"=> X'.N
local notation "Mβ"=> X'.M
open Ember Hove
variable (D:Division)
local notation "H"=> Coats I
local notation "X"=> bins SU.Slot
local notation "Z"=> SectorLayer
-- sums at every fixed t. labels in target Coupled in same epoch (calibration true v) weak.Atomic payments.CP.
local notation "A" d:max k:max=> seam d k
local notation "ℐ"=> Complex.I
variable (h:Axis) (U:Z→ Op I) (a κ:ℝ)(pU:∀ x:Z, ‖U x‖≤ κ*expNote a x.1 x.2)(hp:0<a)(L:Cover)
-- p shadows Stack here until omit. rename later
include hp
abbrev ebbF(a:ℝ)(x:Cover):ℝ:=Real.exp (-(a/4)*size x)
lemma expTogether (x:Z):expNote a x.1 x.2=ebbF a x.1*ebbF a x.2:=by unfold expNote ebbF; rw [←Real.exp_add]; congr 1; ring
lemma ebbFrame : Summable (ebbF a):=by
 have he:= fast_kernel 1 (show 0<a/4 by positivity); simpa only [one_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le] using he.abs
lemma expPair : Summable (fun x:Z=> expNote a x.1 x.2):=by simp_rw [expTogether a hp]; exact (ebbFrame a hp).mul_of_nonneg (ebbFrame a hp) (fun i=> (Real.exp_pos _).le) (fun i=>(Real.exp_pos _).le)
include pU
lemma lensFunded :Summable U:= ((expPair a hp).mul_left κ |>.of_nonneg_of_le (fun x=>norm_nonneg _) pU).of_norm
set_option quotPrecheck false
local notation "ξx" x:max=> (↑((x:Cover) h):ℂ)
abbrev struck (U:Z→Op I)(h:Axis)(z:Z) : Op I:= (↑(z.1 h):ℂ) • U z -- `→ Op` parser issue
lemma strikes : Summable (struck U h):=by
 let f(x:Cover):=ebbF a x; have hF: Summable (fun i=> ‖ξx i‖*f i):=by
    let F:= fast_kernel 1 (show 0<a/4 by positivity)|>.rune h; have hu(i):‖rune h i‖= ‖ξx i‖:=by rw [rune,norm_mul,Complex.norm_I,one_mul]
    simpa only [one_mul,Complex.norm_real,hu, norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le] using F.abs -- semicolon scope
 let q:=hF.mul_of_nonneg (ebbFrame a hp) (fun i=> mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (fun i=>(Real.exp_pos _).le); apply Summable.of_norm; refine (q.mul_left κ).of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>?_); unfold struck; rw [norm_smul]; have hm:=pU i; rw [expTogether a hp i] at hm; exact (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans_eq (by unfold f; ring)
omit hp pU
-- shift equiv (o,y)→( -o for x,.. ). use can∎.G col y translated.
def swingOver (d:Cover) : SectorLayer ≃ SectorLayer where
 toFun Y:=(-(Y.1+d),Y.2-(Y.1+d))
 invFun Y:= (-Y.1-d,Y.2-Y.1)
 left_inv(Y):=Prod.ext (by dsimp; abel) (by dsimp; abel)
 right_inv(Y):=Prod.ext (by dsimp; abel) (by dsimp; abel)
def flourLap (d:Cover)(T:Z) : Op I := (ξx T.1) • U (-(T.1+d), T.2-(T.1+d))
lemma springTurn(d:Cover):flourLap h U d=(fun z=> -((ξx (z:SectorLayer).1) • U z+(ξx d) • U z)) ∘ swingOver d:=by
 funext z; unfold flourLap; dsimp only [swingOver,Function.comp_apply]; change _ = -((ξx (-(z.1+d))) • U _+_); rw [←add_smul, ←neg_smul,Pi.neg_apply,Pi.add_apply, Int.cast_neg,Int.cast_add]; congr 1; ring
variable (u:Summable U)(w:Summable (struck U h))
include u w
lemma springBack (d:Cover): HasSum (flourLap h U d) (-((∑' z,struck U h z)+(ξx d) • ∑' z:Z,U z)):=by rw [springTurn]; apply (Equiv.hasSum_iff ..).2; exact (w.hasSum.add (u.hasSum.const_smul _)).neg
lemma pulseYield (z:Cover) : HasSum (fun x:Z=> lacquer (flourLap h U z x - flourLap h U (-z) x)) ((-(2:ℂ)*(ξx z)) • lacquer (∑' z:Z,U z)):=by
 have he:= ((springBack h U u w z).sub (springBack h U u w (-z))).mapL lacquer
 convert! he using 1
 simp only [Pi.neg_apply,Int.cast_neg,map_neg,map_add,map_sub,map_smul]; module
omit u w
-- right layer yield combined
variable (u₁:flash 0 (p 0) =1-X) -- fix
variable (u₂:flash 0 (Δ h (p 0))=Tap.boom h)
include u₁ u₂
-- `Case illumination:`
noncomputable abbrev portrait (p:Stack)(r:ℕ)(z:SectorLayer) : Op I:= (ξx z.1) • lacquer (porchL D p r 0 z.2 z.1)
lemma flairRight {r:ℕ} : HasSum (fun z=> portrait D h p r z) ((bmass r:ℂ) • (ℐ • (petal h⊗ₖ commission D))):=by
 let P:=p 0; let W:=1-P; let Zz:=layer D P W h; let Y:= layer D W P h; let F:=ℐ • (petal h⊗ₖ commission D); let C:= fun q z=> lacquer (Zz q 0 z+Y q 0 z)
 have ht(q:Cover): HasSum (C q) F:= by
    have het:= ((layerTrue D h P W q).add (layerTrue D h W P q)).mapL lacquer; -- need equality of functions C q.Last. test
    rw [map_add, lampOut h (p 0) u₁ u₂ q D] at het; exact het
 let L:=floorLine r; have hL(b:Z): portrait D h p r b=(L.map (fun x=> C x b)).sum:=by
    unfold L portrait porchL; generalize floorLine r=Zq; induction Zq with
    | nil=> simp only [List.map_nil,List.sum_nil,map_add,map_zero,add_zero,smul_zero]
    | cons a L i => simp only [List.map_cons,List.sum_cons]; rw [add_add_add_comm,map_add, smul_add,i]; apply congrArg (fun x:Op I=>x+(L.map fun x=> C x b).sum); unfold C Zz Y layer; dsimp only; rw [←smul_add, map_smul]; rfl
 have hx(L:List Cover): HasSum (fun i=> (L.map (fun j=> C j i)).sum) ((L.length:ℂ) • F):=by induction L with|nil=>simpa using (hasSum_zero (β:=SectorLayer) (α:=Op I)) | cons a L i=>rw [List.length_cons,Nat.cast_add_one,add_smul,one_smul,add_comm _ F]; exact (ht a).add i
 simp_rw [hL]; exact (layout_mass (r:=r) 0) ▸ hx L
#print axioms pulseYield
end AuroraX
end YM.CF.LitCurrent
