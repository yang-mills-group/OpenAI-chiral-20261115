import YM.SU5.SatinWard.Resolution.Meson
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open Maxwell.Free
namespace PSE
open LitCurrent Surplus Next.Rank Next.Rank.Spindle
section algebraic
variable (B:ℕ)(G:Sheds B → Sheds B→ℂ)
abbrev plumI{B:ℕ}(i:Sheds B):=i.1.val.2
abbrev sailF (s:Signed)(l:Sage)(i:Sheds B):ℝ:= sch (G:=SU.group) i.2 l * orientAx s (plumI i)
abbrev chordF {B:ℕ}(j:Sheds B)(A:PlaqAxes)(i:Sage)(d:Gaia):ℂ:= (sch (G:=SU.group) j.2 i:ℂ)* specter (plumI j) A d
abbrev luteP (i j:Sheds B)(n:Fin 3)(s:Sage)(x:Gaia):ℂ := chordF i (foilA n) s x * chordF j (foilB n) s x + chordF i (foilB n) s x * chordF j (foilA n) s x
noncomputable def concLead (d:Gaia):ℂ:= ∑ i:Sheds B,∑ j:Sheds B, G i j*Complex.I* (∑ n:Fin 3,coeff2 1 1 n * ∑ l:Sage,luteP B i j n l d) -- args include B likely section. notation
abbrev concQuery (s:Signed)(i:Sage) :ℂ:=∑ j:Sheds B,∑ l:Sheds B, G j l*(sailF B s i j:ℝ)*(sailF B s i l:ℝ)
abbrev WStyle (v:ℂ):Prop:= ∀ i l, concQuery B G (sailUp i) l=(5/2:ℂ)*v ∧ concQuery B G (sailDown i) l = -(5/2:ℂ)*v
variable {N:Side}{p:BudgetPoint}{K:Scree.Loom N}{s q r:ℕ}{P T:SOp N}{a b v d e:ℝ}{Z:Gaia}{B:ℕ}
lemma newsprint (o:Site N)(w:Pattern P T s d a v)(D:LitCurrent.Chamber.Division)(h:2*(B+1)<(More N).val)(z:Checked p K e d a r q)(pB:B=p.B) (yQ:4*(B+separation (node o) 1+2)+1< N.val) (g:Bud (btraceF D w o K p r)) : WStyle B (bcashY B h D o w r) (bud (btraceF D w o K p r) 2):=by
 let F:=bcashY B h D o w r; let C:=bud (btraceF D w o K p r) 2; let U(x:Signed)(j:Sage):=concQuery B F x j
 have he(x:Signed)(j:Sage): U x j=(5/2:ℂ)*((if detX x then -1 else 1)*C):=by
    obtain ⟨ξ,hh,hp,v⟩:= poseAll (n:=N) x o o; rw [←hh, show detX ξ.s=Sour.det_S ξ from rfl,← show blapAsset D o r B h w (orientF ξ.s B)= _ from style_receipt z w D o ξ B h yQ hp v pB g]
    let V:SU.group.Color:=EuclideanSpace.single j 1; rw [← accountant_color z w D o B h ξ.s (show ‖V‖=1 from by unfold V; simp), bpolynomial] -- issue
    unfold U concQuery
    let Ψ:= sailF B ξ.s j; suffices hv: snapFace B (berry_map ξ.s B V)= Ψ by rw [bfineY,hv] -- tune
    funext i; change (orientAx ξ.s (plumI i)* V i.2)= _; unfold V Ψ sailF; by_cases i.2=j <;> simp [sch, *]
 intro i l; have hy:=he (sailDown i) l; refine ⟨?_,?_⟩
 · exact (he (sailUp i) l).trans (by rw [presenceUp]; simp; rfl)
 exact hy.trans (by rw [presenceDown]; simp only [ite_true,C]; ring) -- ring_nf leaves maybe
lemma conc_earns (g:Z≠0) {B:ℕ} (G:Sheds B→ Sheds B→ℂ){v:ℂ} (h:WStyle B G v): concLead B G Z=(5/2:ℂ)*v*(posix Z:ℝ):=by
 let T:= (↑(4*Maxwell.normal*(‖Z‖^2)⁻¹^2:ℝ):ℂ)^2; let Ω:Sage→ Sheds B→ ℂ:= fun k i=> (sch (G:=SU.group) i.2 k:ℂ)
 let F(i j:Sheds B)(l:Sage):= (∑ n:Fin 3,coeff2 1 1 n* luteP B i j n l Z)
 have he(i j:Sheds B)(l:Sage): Complex.I* F i j l = Ω l i*Ω l j*(↑(palG (plumI i) (plumI j)):ℂ)*T:=by
    unfold F; rw [show (∑ n:Fin 3, _)= Ω l i*Ω l j* webC (plumI i) (plumI j) Z from ?_]; rotate_left
    · unfold webC; rw [mul_sum]; refine sum_congr rfl fun n _=>?_; unfold Ω luteP chordF; ring
    rw [mul_left_comm,mul_assoc (Ω _ _*Ω _ _) _,webValue Z (plumI i) (plumI j) g] -- syntax
 -- sum identity for one color via sailQuery
 let c(i j:Sheds B)(l:Sage)(u:Signed):= G i j*(↑(sailF B u l i):ℂ)*(↑(sailF B u l j):ℂ)
 have hv(i j:Sheds B)(l:Sage): G i j*(Complex.I* F i j l)= T/2 *∑ k:Fin 3,(c i j l (sailUp k)-c i j l (sailDown k)):=by
    rw [he]; unfold palG; unfold c sailF Ω flyP flyM; push_cast; calc _ = G i j*(Ω l i*Ω l j)*T/2* ∑ k:Fin 3, ((orientAx (sailUp k) (plumI i):ℂ)*(orientAx (sailUp k) (plumI j):ℂ) -(orientAx (sailDown k) (plumI i):ℂ)*(orientAx (sailDown k) (plumI j):ℂ)):=by unfold Ω; push_cast; ring
                                                                         _ = _:= by rw [mul_sum, mul_sum]; apply sum_congr rfl; intro k _; unfold Ω; push_cast; ring
 let Z':=(5/2:ℂ)*v*T; have hk(l:Sage): (∑ i:Sheds B,∑ j:Sheds B,G i j*(Complex.I* F i j l))=3*Z':=by
    simp_rw [hv,←mul_sum]; let g(x y:Sheds B)(k:Fin 3):ℂ:=c x y l (sailUp k)-c x y l (sailDown k)
    change T/2*(∑ i,∑ j,∑ k,g i j k)= _
    have hu(k:Fin 3): ∑ i,∑ j,g i j k= (5/2:ℂ)*v-(-(5/2):ℂ)*v:=by
       unfold g; simp_rw [sum_sub_distrib]; rw [← (h k l).1,← (h k l).2]; -- danger negative grouping minus ring parentheses
    simp_rw [sum_comm (f:=fun (j:Sheds B)(k:Fin 3)=>g _ j k),sum_comm (f:=fun (i:Sheds B)(k:Fin 3)=>∑ j:Sheds B,g i j k),hu]; rw [sum_const,card_univ]; unfold Z'; simp; ring
 unfold concLead; calc _ = ∑ l:Sage, (∑ i:Sheds B,∑ j:Sheds B,G i j*(Complex.I* F i j l)):=by
                               rw [sum_comm (f:=fun (l:Sage)(i:Sheds B)=>∑ j:Sheds B,G i j*(Complex.I*F i j l))]; apply sum_congr rfl; intro i _; rw [sum_comm (f:=fun (l:Sage)(j:Sheds B)=>G i j * (Complex.I* F i j l))]; apply sum_congr rfl; intro j _; simp_rw [←mul_assoc (G i j), ←mul_sum]; apply congrArg; unfold F; simp_rw [mul_sum]; rw [sum_comm (f:=fun n l=>coeff2 1 1 n*luteP B i j n l Z)]
                       _ = _:=by simp_rw [hk]; rw [sum_const,card_univ,nsmul_eq_mul]; unfold Z' T posix; push_cast; ring
end algebraic
end PSE
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
