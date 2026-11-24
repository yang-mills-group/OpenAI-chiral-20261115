import YM.SU5.SatinWard.Resolution.CasaF
import YM.SU5.SatinWard.Resolution.Chalice
import YM.SU5.SatinWard.Resolution.Costaria
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Tapestry
open SlabMark Papal Papal.Moon Papal.Moon.Moonlit SwitchC Garland Terrace Juniper
namespace CasaF
-- Move algebra availability Cover.Publish literal movement all fixed scale. No covariance assertion after precise cost? Tapestry launch supplies.
open QuadClock Preparation.Tabletop Fock -- remove unsupported
open Vacancy
section support
variable {Λ':Preparation}{l':ℕ}(Y:Course Λ' (VolumeCape.Dream.Nimbus l'))(H:Real.exp 1 ≤ Λ'.x)(s i:ℕ)
local notation "T"=> tent Y H
local notation "n"=> side Y i s
-- moment height P.layout. later.
local notation "η" => exhibit Y H s i
lemma exhibitC (S:Finset Cover)(j:Axis)(X:Family (tent Y H))(p:ℤ) : exhibit Y H s i (Tower.chime T j p X)= reflMark j p (reflMark j 0 (η X)):= by
 let g:=terrain Y H (Y.ir i) s; change arrange _ _ g (reflMark _ _ (reflMark _ _ _))=reflMark _ _ (reflMark _ _ (arrange _ _ g _)); rw [displayRef g,displayRef g]; rfl
def Aligns {N:Side}(M:Site N→Mark N):Prop:=∀ (u:Axis),∃ c:ℝ,‖c‖=1∧∀ (x:Site N)(j:ℤ), reflMark u j (M x)= c • M ((plane u j).mills _ x)
lemma poised {N:Side}{M:Site N→Mark N}(u:Poisson N M)(h:∀ x,AtSupport false univ (M x)): Aligns M:=fun i=> ⟨1,norm_one,fun x j=> (u.tagged _ _ x (h x)).trans (one_smul ..).symm⟩
lemma lyrical{N:Side} {M:Axis→Site N→ Mark N}(j:Axis)(u:Dirfield N M)(h:∀ x,AtSupport false univ (M j x)): Aligns (M j):= fun i=> ⟨StressFlux.sign (Signed.mirror i) j,by unfold StressFlux.sign; split <;> simp, fun x d=> u.tagged j i d x (h x)⟩
variable {M:Site (side Y i s)→ Mark (side Y i s)} {x:Family (tent Y H)} {p:Cover}
local notation "Y♭"=> (wrap (side Y i s))
lemma travelP {P:Side}(x:Cover)(i:Axis)(j:ℤ): (plane i j).mills P ((plane i 0).mills P (wrap P x))= wrap P (x+j • step i):=by
 rw [Shape.mill,Shape.mill]; -- direction tune
 apply congrArg; funext a; by_cases t:a=i; · subst a; simp [flee_pos]; omega
 simp [flee_pos,t, Ne.symm t]
private lemma mirror_linen {N:Side}(M: Mark N)(t:ℝ)(i:Axis)(j:ℤ): reflMark i j (t • M)=t • reflMark i j M:=by simp_rw [←Complex.coe_smul]; exact funext fun i=> by unfold reflMark; simp only [Pi.smul_apply,theta_smul,Complex.star_def,Complex.conj_ofReal]
lemma exhibit_box (g:Aligns M)(u:η x=M (Y♭ p))(V:Cover)(q:List Axis): η (moving q V x)= M (Y♭ (movesBy q V p)):=by
 induction q with
 | nil=>exact u
 | cons j q ih=>
    obtain ⟨a,h,e⟩:= g j; rw [show moving (j::q) V x=_ from (show moving (j::q) V x=chime T j (V j) (moving q V x) from rfl),exhibitC Y H s i ∅,ih, e,mirror_linen,e,smul_smul,show a*a=1 from ?_,one_smul,travelP]; rfl
    have hu:|a|=1:=h; cases abs_cases a <;> grind -- check
lemma exhibit_carriage (g:Aligns M)(u:η x=M (Y♭ p))(V:Cover): η (carriage V x) = M (Y♭ (p+V)):= (exhibit_box Y H s i g u V ordinate).trans (by rw [moved_box _ _ ordinates ordinate_one])
lemma travel_carriage {K:Calibration} (F:Cover→Family K) (u:∀ (j:Axis) (x:Cover)(m:ℤ), chime K j m (F x)= F (x+m • step j)) (y p:Cover): carriage y (F p)= F (p+y):=by
 have hv(v:List Axis):moving v y (F p)= F (movesBy v y p):=by induction v with|nil=> rfl| cons j v h=> exact (congrArg (chime K j (y j)) h).trans (u j _ (y j)) -- syntax
 rw [carriage,hv,moved_box _ _ ordinates ordinate_one]
end support
end CasaF
end YM.CF.Buffered.Afterglow.Tower
