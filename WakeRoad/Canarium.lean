import WakeRoad.Shantel
import WakeRoad.Lizard
import WakeRoad.Moscatel
set_option quotPrecheck false
/-! # Response in finite uniform curl space, symmetric coefficients -/
set_option autoImplicit false
set_option maxHeartbeats 190000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry 
open QuadClock Preparation.Yoke
namespace Spine.Gingham
namespace VoyageB
open Diary CF.Gingham.Ruff GarlandBook Drapes
open YM.WakeRoad _root_.Zephyr.Chern
open Dial
open scoped ContDiff
open YM.ConnectedActivityE6.SliceRows
open YM.WakeRoad.Boom

section Common
variable {N:Side}{e a c b ρ:ℝ}{A:Fob N e}{u:Side}{l r:ℕ}{E₀:ℝ}
  (X:Rialto 6 e ρ b)(B:Plastron (0:Site N) u e a c A)(m:ℕ)(tag: Tagbill (4*a) E₀ u l r (10*m)) -- will fix m=tender actual B; variable tag types
local notation "o*"=>bouton (0:Site N)
local notation "L"=>SU.group.Color

abbrev fuel (q:ℕ):Doub N→ℂ:= Gingham.Ruff.hum X (Shells.light B (tenderb q))
-- choose width q/10
abbrev atoms(q:ℕ): Press (Postcard (q/10)):=review (batik (q/10) (bouton (0:Site N)) X (B.lightP (tenderb q)))
variable {q:ℕ}(T: Tagbill (4*a) E₀ u l r q)
include T
lemma atoms_fee:WakeRoad.coin (atoms X B q)≤ Lion u a c:=by refine (review_paid _).trans ((batik_paid (q/10) X _ (fun t p=>p.1) (by linarith only [T.apos])).trans (Eq.le (by rw [one_mul])))
lemma jet_scores(h:2*(q/10+1)<(More N).val)(p:0<ρ)(f:tangD N):
 quadraticChi (fuel X B q) (f,0)= WakeRoad.Score (atoms X B q) (WakeRoad.native (q/10) (bouton (0:Site N)) f):=by
 rw [atoms,revised]
 refine WakeRoad.ballot _ _ _ p (by linarith only [T.apos]) h (fun S a i v=>?_)
 have hx:= a.1 i v -- tune R defeq
 change separation (bouton 0) i ≤ _+5*S.card at hx
 have hv := T.largeB; obtain ⟨q',w'⟩:=a; unfold tenderb at w'
 omega

-- color vector used for response
local notation "Cχ"=>SU.group.ColorIndex
local notation "C☆"=> (SU.group.projectColor (Matrix.diagonal (fun i:SU.F=>Complex.I * ↑(dye.val i))))
def clair (δ:ℝ)(i:PlaqAxes)(c:Cχ):ℝ:= (δ⁻¹*_root_.Zephyr.Chern.flux (Lattice.step i.val.1) (Lattice.step i.val.2))* C☆ c
omit T
lemma native_jet (m:ℕ)(g:2*(m+2)<(More N).val): WakeRoad.native m (bouton (0:Site N)) (jetColor N ρ).1=fun i=> clair ρ i.1.2 i.2:=by
 funext i; let a:=i.1.2.val.1; let b:=i.1.2.val.2; let x:=i.1.1.val
 let y:=Boom.port (bouton (0:Site N)) x
 have e0: bouton (0:Site N)=0:= by unfold bouton; rw [←Ratio.root_embed,map_zero]
 have e:y=Lattice.wrap (More N) x:=by simp [y,Boom.port,e0]
 have hw(j:Axis):y+step j=Lattice.wrap (More N) (x+step j):=by rw [e,map_add,wrap_step]
 have p {z:Cover}(p:z∈Lattice.box (m+1)):_root_.Zephyr.Chern.rel (wrap (More N) z)+ (1:Cover)= z:=by
    rw [_root_.Zephyr.Chern.rel,← show wrap (More N) (1:Cover)=(1:Seat N) from ?_,←map_sub,show Lattice.lift (wrap (More N) _)=z-1 from ?_,sub_add_cancel]
    · apply lift_eq_iff.mpr ⟨rfl,fun i=> ?_⟩
      obtain ⟨t,w⟩:= box_test.mp p; have h:= t i; have hh:= w i; change -( (More N).val:ℤ)<2*(z i- (1:ℤ)) ∧ 2*(z i - 1) ≤ ((More N).val:ℤ); omega
    · funext j; change ((1:ℤ):Per (More N)) = 1; rw [Int.cast_one]
 have hv : x∈Lattice.box (m+1):=by
    obtain ⟨t,w⟩:= box_test.mp i.1.1.property
    apply box_test.mpr; constructor <;> intro j <;> have z:=t j <;> have h:=w j <;> unfold x <;> omega
 have hz(j:Axis): x+step j ∈ Lattice.box (m+1):=by
    obtain ⟨t,w⟩:= box_test.mp i.1.1.property
    apply box_test.mpr; constructor <;> intro k <;> have v:=t k <;> have h:=w k <;> simp only [x,Pi.add_apply,step_apply] <;> split <;> omega
 let F':= _root_.Zephyr.Chern.flux
 let K:=C☆ i.2
 have t(j k:Axis): (jetColor N ρ).1 (y+step j,k) i.2= (ρ⁻¹*_root_.Zephyr.Chern.stream N (y+step j,k))* K:=rfl
 have w(j:Axis): (jetColor N ρ).1 (y,j) i.2= (ρ⁻¹*_root_.Zephyr.Chern.stream N (y,j))* K:=rfl
 let χ:=_root_.Zephyr.Chern.stream N
 change ((jetColor N ρ).1 (y+step a,b) i.2-(jetColor N ρ).1 (y,b) i.2-((jetColor N ρ).1 (y+step b,a) i.2-(jetColor N ρ).1 (y,a) i.2))= (ρ⁻¹ *F' (Lattice.step a) (Lattice.step b))*K
 rw [t,t,w,w,hw,hw,e]; simp only [_root_.Zephyr.Chern.stream,twistAt,p (hz _),p hv,flux_left]
 rw [flux_switch (Lattice.step b)]; unfold F'; ring
end Common

variable (P:Spine)(a c μ:ℝ)(d:ℕ){ρ b:ℝ}(X:Rialto 6 P.par.d ρ b)
private lemma traffic : ∀ᶠ s:ℕ in atTop,∀ᶠ n:ℕ in atTop,2*((P.run.meter.a s).B/10+2)<(More (side P.run (Diary.irr P n) s)).val:= by
 refine Eventually.of_forall (fun s=>?_)
 -- irr tendsto
 let S:= 2*((P.run.meter.a s).B/10+2)
 filter_upwards [(P.run.ir_grows.tendsto_atTop.comp (rising_i P).tendsto_atTop).eventually_gt_atTop
     S] with n h
 change S < _
 suffices S < (P.run.ir (irr P n)).val from this.trans_le (le_trans (amplit ..) (show (side P.run (irr P n) s).val ≤ (More (side P.run (Diary.irr P n) s)).val by unfold More; exact Nat.le_mul_of_pos_right _ two_pos)) -- amplit term check
 exact h

-- size & Hessian goals with the issued atmosphere stamps
local notation "v*" s:max i:max=> side P.run i s
local notation "?R?" s:max i:max k:max=> RootBook P.run i k s
local notation "b*" s:max i:max k:max=> (RootBook P.run i k s).p.B
lemma chargeMirror(hρ:0<ρ)(v:0<a)(T:Anthem P a c μ d ρ b X) {ν:ℕ→ℕ}(hν:Tendsto ν atTop atTop):
   ∃ C:ℝ, ∃δ:ℝ,0<δ ∧ ∀ᶠ s:ℕ in atTop,∀ᶠ n:ℕ in atTop,∀p:Scene P a c μ d s (Diary.irr P (ν n)) (Diary.uvv P (ν n)), let b:=(RootBook P.run (Diary.irr P (ν n)) (Diary.uvv P (ν n)) s).p.B; let T':=atoms X p.gb.pump b;
    WakeRoad.coin T' ≤ C ∧ δ < (WakeRoad.Score T' (fun i=> clair ρ i.1.2 i.2)).re ∧ 2*(b/10+2)< (More (side P.run (Diary.irr P (ν n)) s)).val:= by
 obtain ⟨δ,t,H⟩:=reportCard P a c μ d X hρ v T
 let V:=pepCharge (underlay P.par) a c
 refine ⟨Lion (underlay P.par) (a/4) V,δ,t,?_⟩
 filter_upwards [traffic P,H] with s u b
 filter_upwards [hν.eventually u] with n y p B T'
 let i:=irr P (ν n)
 let k:=uvv P (ν n)
 have t:= b _ _ p
 have v: Tagbill (4*(a/4)) 1 (underlay P.par) 2 P.par.J.n B :=by
    rw [show (4:ℝ)*(a/4)=a from by ring]; exact p.gears.tag
 have h₁: (?R? s i k).p=P.run.meter.a s:= (((P.run.voyage i).X (P.run.uv k)).pull.owns s p.ok.le).width.symm
 change 2*((P.run.meter.a s).B/10+2)< (More (v* s i)).val at y
 rw [← h₁] at y
 refine ⟨atoms_fee X p.gb.pump v,?_,y⟩
 rw [← native_jet (N:=v* s i) (B/10) y,show (T')=atoms X p.gb.pump B from rfl,← jet_scores X p.gb.pump v (lt_trans ?_ y) hρ]
 swap; · change 2*(B/10+1)<2*(B/10+2); omega
 exact t.1
#print axioms chargeMirror
