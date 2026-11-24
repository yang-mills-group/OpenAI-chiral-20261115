import YM.SU5.SatinWard.Resolution.Aspen
import YM.SU5.SatinWard.Resolution.Carmel
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered Salt
-- Circ on Pane too: note one mesh q, areal. shared mask for tax (inc bar subtraction)
-- and for each chir ingredient.
variable {P T:SOp N} {p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
open Urn

namespace Chamber
section proof
variable (bI:Division)(K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)
local notation "S"=>offsetMask p.B x
local notation "Â"=> skyHat bI x E K p k
local notation "J"=> centHat bI x E K p k
local notation "Λ"=> (tickA N)
private lemma seed_dg (w:ℝ)(A:Op I): Continuous (preHalf w A):=by
 have he: Continuous (Fock.dg (n:=I)):=by unfold dg dyad; refine continuous_finsetSum _ fun i _=>?_ ; refine continuous_finsetSum _ fun j _=>?_ ; exact (continuous_id.matrix_elem i j).smul continuous_const
 unfold preHalf preJ; exact ((((continuous_const.mul continuous_id).matrix_trace).smul continuous_const).add (he.comp ((continuous_const.mul continuous_id).mul continuous_const))).sub ((continuous_const (y:=(w:ℂ))).smul ((continuous_id.matrix_trace).smul (continuous_const (y:=(1:FC I)))))
variable (z:Checked p K t d a k q)
include z
open QuadClock QuadClock.Lampshade
open Salt Buffered
open Urn ShapeLab
open SweepSign
local notation "stock"=>jewelO bI x E K p k w
local notation "starling"=>jewelY bI x E K p k
omit z in
lemma frontSite (P':Site N→Mark N) (v:∀ (s:Sweep N) (x:Site N)(z Q: Fields N),Q.1= flashA s z.1 → lotB s.charge (det_S s) (γS s) (P' x z)= Scroll.hush (det_S s) (P' (pose s x) Q)) :∀ (s:Sweep N)(x y:Site N), Earlier s x y→ flyMark s ((Complex.I) • P' x)= (pseudoCharacter N).sgn s • ((Complex.I) • P' y):=by -- remove z
 intro t x y h; funext u; unfold flyMark; rw [Pi.smul_apply]; let U:Fields N:=⟨flashA t⁻¹ u.1,flashA t⁻¹ u.2⟩
 have ht:pose t x=y:= (earlier_mills ..).mp h.backward
 change lotB t.charge (det_S t) (γS t) ((Complex.I) • P' x U)= hush t.charge (1:ℝ) • ((Complex.I) • P' y u)
 have hp:=v t x U u (by unfold U; dsimp only; nth_rw 1 [←inv_inv t]; -- check direction? goal u.1= flashA t; nth_rw matches inside U? 
                                         rw [revB])
 rw [ht] at hp; rw [visage,hp]; cases t.charge<;> cases (det_S t)<;> simp [cSignX]
omit z
local notation "χw"=> pseudoCharacter N
include z
lemma bodyStar : QuadClock.Waxy.SignBent χw BodyPull (fun y=> Complex.I • jewelO bI y E K p k (1/2)):=by
 intro s hu x y t; exact frontSite (fun y=>jewelO bI y E K p k (1/2)) (fun s x y q h=> posesY bI x z E s y q h) s⁻¹ y x t.backward
lemma bodyGlow : QuadClock.Waxy.SignBent χw BodyPull (fun y=> Complex.I • jewelY bI y E K p k):=by intro s hu x y t; exact frontSite (fun y=>jewelY bI y E K p k) (fun s x y q h=> poses_gauge bI x z E s y q h) s⁻¹ y x t.backward
lemma fly_current (s:Sweep N)(t:FaceDir)(y:Site N)(h:Earlier s x y): flyMark s ((Complex.I) • jewelJ bI x E K p k (1/2) t)= (χw).sgn s • ((Complex.I) • jewelJ bI y E K p k (1/2) (faceAt s t)):=by
 funext u; unfold flyMark; rw [Pi.smul_apply]; let U:Fields N:=⟨flashA s⁻¹ u.1,flashA s⁻¹ u.2⟩
 have ht:pose s x=y:= (earlier_mills ..).mp h.backward
 change lotB s.charge (det_S s) (γS s) ((Complex.I) • jewelJ bI x E K p k (1/2) t U)= hush s.charge (1:ℝ) • ((Complex.I) • (_:FC I))
 have hp:=poses_current bI x z E s U u (by unfold U; dsimp only; nth_rw 1 [←inv_inv s]; rw [revB]) t
 rw [ht] at hp; rw [visage,hp]; cases s.charge<;> cases (det_S s)<;> simp [cSignX]
open StressFlux
lemma bodyBeat (i:Axis) : QuadClock.Waxy.SignBent (spinCharacter N i) BodyPull (fun y=> Complex.I • jewelJ bI y E K p k (1/2) (i,false)):=by
 intro s g x y t; change flyMark s⁻¹ _=_; rw [fly_current bI K p k y E z s⁻¹ (i,false) x t.backward]; obtain ⟨q,h,hp⟩:= (mem_spin ..).1 g
 let U(j):=jewelJ bI x E K p k (1/2) j; change hush (s⁻¹.charge) (1:ℝ) • (Complex.I • U _)= sign s.s i • (Complex.I • U (i,false))
 have hv:faceAt s⁻¹ (i,false)=(i,s.s.flip i):=by unfold faceAt strideD; rw [show s⁻¹.s=s.s⁻¹ from rfl]; simp [Step.rotate,h]
 rw [show s⁻¹.charge=false from hp,hv,hush_false,one_smul]; unfold sign; cases h':s.s.flip i
 · rw [if_neg,one_smul]; simp
 rw [show (i,true)=axisFlip (i,false) from rfl,if_pos rfl,neg_smul,one_smul, show U (axisFlip (i,false))= -U (i,false) from funext fun v=>currentSeed_anti bI K p k (1/2) x E z v _, smul_neg]
-- no coherence requirement on contact of surrogate post.Leg read old snapshot. Window then Groove.Signproof.
lemma metaStamp(l:ℕ)(h:p.B+2*r+12 ≤ l*p.B)(t:8*r ≤ p.B): let j:=l*p.B; let f:=jewelO bI x E K p k w; let v:= jewelT bI x E K p k w; ∃ B:ℝ, WindowTag f x j B ∧ Contact K (offsetMask j x) f (fun i=> v (i.1,K i)):= by
 intro j f v; let Vp:= offsetMask j x; have ht:(tendril p r x) ⊆ Vp:=words_fit p x l h
 let V:= (physical_support bI _ _ _ w x E z).mono ht
 obtain ⟨C,W'⟩:= V.env.cost
 refine ⟨C,⟨V, physical_moves bI _ _ _ w x E z,W',?_⟩,V,fun i=> surrogate_sector bI _ _ _ w x E z l h t _,fun i=>centered_bra bI _ _ _ w x E _⟩ -- check Carmel params order
 intro a b c; unfold f jewelO; rw [Pi.add_apply,Pi.add_apply,Finset.sum_apply,Finset.sum_apply]; apply congrArg₂ (·+·) _ (sum_congr rfl fun i _=>?_)
 · unfold jewelY; rw [c]
 unfold jewelJ; rw [c]
end proof
end Chamber
end YM.CF.LitCurrent
