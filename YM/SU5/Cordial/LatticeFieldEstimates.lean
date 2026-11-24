import YM.SU5.Cordial.Fountain
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
namespace Designs
variable {R:ℕ}(A:Lead R)(a:Axis)(i:ℤ)
def liftS (a:Lead R):Twah:=⟨a.birth,a.death,a.slot,a.slot,a.traceV,a.moves⟩
def roam : Lead R:= (A.mirror a 0).mirror a i
lemma marchS(k:Cover) : (plane a i).flee ((plane a 0).flee k)=k+i • step a:= by funext x; simp only [flee_pos]; by_cases h:a=x<;> (first | (subst x; simp; omega) | simp [h,Ne.symm h]) -- tune
lemma proceeds : (roam A a i).birth=A.birth+i • step a:= marchS a i A.birth
lemma track_cost : (roam A a i).death=A.death+i • step a:= marchS a i _
lemma costSpin : (roam A a i).slot=A.slot∧(roam A a i).wave=A.wave:=by
 simp only [roam,Lead.mirror]; unfold Lead.shuffle axis_val; split <;> split <;> simp
variable (Z:Lead.Clan)
lemma transferMark : A.groundWord Z=Lead.cash A.wave • (liftS A).groundWord R Z:= by
 funext N X
 simp only [Lead.groundWord,Twah.groundWord,Lead.cash,Pi.smul_apply,smul_smul]
 rw [show Lead.sing R A.wave=(phaseF A.wave:ℂ)/5*Twah.gold R by unfold Lead.sing Twah.gold; ring]; rfl
lemma journeyV : (roam A a i).groundWord Z=traction a i (A.groundWord Z) := by
 have he (b:Lead R)(u:ℤ): (b.mirror a u).groundWord Z=fluent a u (b.groundWord Z):=funext fun N=> (b.bk_chant_mirror ..).symm
 rw [roam,he,he]; rfl
end Designs
open Prototype Designs
namespace Spine
open Twah
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z:Lead.Clan)(a:Axis)(c r:ℕ→ℕ)
local notation "ε" => YM.basis (3:Axis)
local notation "σ" n:max=> P.singleState a (c n) (P.otherSpectrum 3 a x)
def stockS(A:Lead q) : P.Test := P.tuneK (Lamour.Bridge.Celeste.flourish A Z)
abbrev crewB(s:ℤ):= Heat.gaugeShift P.par.block (2*s)
def migrate (A:Lead q)(t:ℤ):= roam A a (P.crewB t)
lemma acrossStocks (A:Lead q) (i:ℤ): P.shifts a i (P.stockS Z A)= P.stockS Z (P.migrate a A i):= by
 change P.tuneK ((flourish A Z).tract a (P.crewB i))= _; exact P.songsAg _ _ (journeyV ..).symm
lemma mirror_stock (A:Lead q) : P.reflectTest a (P.stockS Z A)=P.stockS Z (A.mirror a 0) := by
 change P.tuneK ((flourish A Z).turn a 0)= _; exact P.songsAg _ _ (funext fun N=> A.bk_chant_mirror ..)
lemma liftS_paid (A:Lead q) : P.stockS Z A= Lead.cash A.wave • P.tuneK (Gemini.flourish (liftS A) Z (R:=q)):= by
 have w:=(Gemini.flourish (liftS A) Z (R:=q)).hushed (Lead.cash A.wave); exact P.songsAg (flourish A Z) w (transferMark ..)
private def unitSl (A:Lead q)(Z:Lead.Clan):= plait (fun _:Fin 1=>liftS A) (fun _=> Z) (Twah.letters 1) q
private lemma unitSl_val (A:Lead q): unitSl A Z=(liftS A).groundWord q Z:=mul_one _ -- need rfl unfolding
private def pairSl (A B: Lead q)(Z:Lead.Clan):= plait ![liftS A,liftS B] (fun _=>Z) (Twah.letters 2) q
private lemma pairSl_val (A B:Lead q): pairSl A B Z=(liftS A).groundWord q Z*(liftS B).groundWord q Z:= congrArg ((liftS A).groundWord q Z * ·) (mul_one ((liftS B).groundWord q Z))
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
def marchesR (A:∀ i,Lead (r i)) (x y:Gaia): Prop:= Tendsto (fun i=>riseX (r i) (A i).birth) atTop (𝓝 x) ∧ Tendsto (fun i=>riseX (r i) (A i).death) atTop (𝓝 y)
def remainsR (A:∀ i,Lead (r i))(b:Bool)(i:Fin 2) : Prop:= ∀ n:ℕ,(A n).wave=b∧(A n).slot=i
variable {c r}{P x} {d:ℕ→ℝ}
variable (S:Launch P c r) (A B:∀ i,Lead (r i)) (h:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
variable (U V:Gaia)(b:Bool)(i:Fin 2)(t:marchesR r A U V)(v:remainsR r A b i)
include S h p t v
-- one slot, canonical price
private def firstTime (x y:Gaia)(q:Cellz (Fin 1)) : Gaia:= if q.2 then y else x
omit t v in -- tune
 lemma shineUV {w:ℕ}(D:Cellz (Fin w)→Gaia)(r': Fin w→ DirSpin) (F:ℕ→Fin w→Twah) (hu:riseUp F r D)(hc:Injective D)(u:∀ n:ℕ,∀ j:Fin w,(F n j).traceV.length=2*r n)(v:∀ n:ℕ, bodyF (F n)=r') : Tendsto (fun n=> (σ n) (P.tuneK (lovely (F n) (fun _=>Z) (Twah.letters w) (r n)))) atTop (𝓝 (Twah.witness (fun _=>Z) (Twah.letters w) D r')):= by
    have ht:plateau F D:=fun i j p=> Eventually.of_forall (fun l=> congrArg _ (hc p)); refine rightRide S _ D F r' (Eventually.of_forall v) hu ht (Eventually.of_forall fun n k=>?_) h p a
    rw [u]; calc _ ≤ 32*((0+2)*r n):=by omega
                 _ ≤ _:=by gcongr; exact Nat.zero_le _
set_option maxHeartbeats 300000
lemma solo_win (hu:U≠V): Tendsto (fun n=> (σ n) (P.stockS Z (A n))) atTop (𝓝 (Lead.cash b * numberX Z * (Onyx.pencil (V-U) (dnSpin i) (upSpin i)))):=by
 let F(k:ℕ)(_:Fin 1):=liftS (A k); let G:=firstTime U V
 have ht(G':Cellz (Fin 1)): G'= (0,G'.2):=Prod.ext (Subsingleton.elim ..) rfl
 have hv : Injective G:= fun x y p=> by rw [ht x,ht y]; rcases x with ⟨x,_|_⟩; all_goals cases y with| mk y z=> cases z<;> first | rfl| exact (hu p).elim | exact (hu p.symm).elim -- tune syntax x true pattern
 have hf:riseUp F r G:=by rintro ⟨k,b⟩; cases b; exact t.1; exact t.2
 have he(n:ℕ):bodyF (F n)=fun _=>(i,i):= funext fun _=> congrArg (fun z:Fin 2=>(z,z)) (v n).2
 let W:=fun _:Fin 1=> Z
 have hq:= (shineUV Z a S h p G _ F hf hv (fun i j=>(A i).costs) he).const_mul (Lead.cash b)
 have eqf : Lead.cash b*(Twah.witness W (Twah.letters 1) G (fun _=>(i,i)))=Lead.cash b*numberX Z* (Onyx.pencil (V-U) (dnSpin i) (upSpin i)):=by rw [show Twah.letters 1=[0] from rfl,show W=(fun _=>Z) from rfl,chorus2,lyric,Cordial.billX,mul_assoc]; rfl
 have EQ(n:ℕ): P.stockS Z (A n) = Lead.cash b • P.tuneK (lovely (F n) W (Twah.letters 1) (r n)):= by
    simp only [P.liftS_paid]; rw [(v n).1]; exact congrArg (Lead.cash b • ·) (P.songsAg (lovely (F n) W (Twah.letters 1) (r n)) (Gemini.flourish (liftS (A n)) Z) (unitSl_val Z (A n))).symm
 simp_rw [EQ,map_smul,smul_eq_mul]; exact eqf ▸ hq -- tune
noncomputable def zephyr (U V X Y:Gaia):Cellz (Fin 2)→ Gaia:= fun x=> if x.2 then ![V,Y] x.1 else ![U,X] x.1
lemma duo_wins (X Y: Gaia)(b': Bool)(j:Fin 2)(T:marchesR r B X Y)(e:remainsR r B b' j)(u:Injective (zephyr U V X Y)):
 Tendsto (fun n=>(σ n) (P.stockS Z (A n)*P.stockS Z (B n))) atTop (𝓝 (Lead.cash b*Lead.cash b' * Twah.witness (fun _=>Z) (Twah.letters 2) (zephyr U V X Y) ![(i,i),(j,j)])):=by
 let f(n:ℕ): Fin 2→ Twah:=![liftS (A n),liftS (B n)]; let D: Fin 2→DirSpin:= ![(i,i),(j,j)]
 let χ(n:ℕ):= Gemini.flourish (liftS (A n)) Z (R:=r n) -- proofs unicode
 let W:=fun _:Fin 2=>Z; let Z' := zephyr U V X Y;
 have h₁:riseUp f r Z':= by rintro ⟨k,z⟩; fin_cases k <;> cases z <;> first| exact t.1| exact t.2| exact T.1|exact T.2
 have h₂(n:ℕ)(i:Fin 2): (f n i).traceV.length=2*r n:=by fin_cases i<;> first | exact (A _).costs| exact (B _).costs
 have h₃(n:ℕ): bodyF (f n)= D:=by funext k; fin_cases k; exact congrArg (fun z:Fin 2=>(z,z)) (v n).2; exact congrArg (fun z:Fin 2=>(z,z)) (e n).2
 have hq:= (shineUV Z a S h p _ _ _ h₁ u h₂ h₃).const_mul (Lead.cash b*Lead.cash b')
 have he(n:ℕ):
   P.stockS Z (A n)*P.stockS Z (B n) = (Lead.cash b*Lead.cash b') • P.tuneK (lovely (f n) W (Twah.letters 2) (r n)):= by
    simp only [P.liftS_paid,(v n).1,(e n).1,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
    rw [mul_comm (Lead.cash b') (Lead.cash b)]
    exact congrArg (fun t:P.Test=> (Lead.cash b * Lead.cash b') • t) (P.songsAg (lovely (f n) W (Twah.letters 2) _) ((χ n).mul (Gemini.flourish (liftS (B n)) Z)) (pairSl_val Z (A n) (B n))).symm
 simp_rw [he,map_smul,smul_eq_mul]; exact hq
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.acrossStocks
#print axioms Spine.solo_win
#print axioms Spine.duo_wins
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
