import YM.SU5.FiniteGaugeData.Tower.Hours
import YM.SU5.SatinWard.Resolution.Juniper
import Velour.Crepe.Wiggle
import Anomaly.Cover.Collection
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
-- uses matter cover translation (pitch= 2*h). For chart proper `shifts` use gaugeT v = (ruler*v)/2. No priori Euclidean.
variable {K:Calibration} {L:Scree.Loom 1}{F:Family K}{S:Finset Cover}(G:InTest K true S false F){t:ℝ}
lemma chimes_pav (p:Cover)(z:ℤ)(k:ℕ)(j:Axis): Tower.address j z (pavilion (nodeC p) k) ⊆ pavilion (nodeC (p+z • step j)) k:=by
 intro y h; obtain ⟨v,t,rfl⟩:= Finset.mem_image.mp h; apply (pav_v ..).mpr; intro i; obtain ⟨f,g⟩:= (pav_v ..).1 t i; have hw(p:Cover): nodeC p i=2*p i+1:=by change (2:ℕ) • p i+1=_; push_cast; rfl
 rw [hw p] at f g; rw [hw]; by_cases z:i=j
 · subst i; simp only [moves,if_true]; omega
 simp only [moves,z,if_false]; exact ⟨f,g⟩
noncomputable def movesBy (s:List Axis)(p:Cover)(v:Cover):Cover:= s.foldr (fun j a=> a + p j • step j) v
noncomputable def moving (s:List Axis)(p:Cover)(F:Family K):Family K:= s.foldr (fun j f=> Tower.chime K j (p j) f) F
variable {p p' u x:Cover} (v:List Axis) (y:Cover)
variable (p₀:Cover)(k:ℕ)
lemma moving_test (h:InTest K true (pavilion (nodeC p) k) false F): InTest K true (pavilion (nodeC (movesBy v y p)) k) false (moving v y F):=by
 induction v with
 | nil=> exact h
 | cons i v ih=> exact (flow_port K i (y i) ih).mono (chimes_pav ..)
lemma moved_box (p:∀ i:Axis,i∈ v)(d:v.Nodup)(x:Cover): movesBy v y x=x+y:=by
 let f(V:List Axis)(i:Axis):ℤ:= if i∈ V then x i+y i else x i; have hz(V:List Axis)(D:V.Nodup): movesBy V y x=f V:=by
    funext i; induction V with
    | nil=> simp [movesBy,f]
    | cons j V ih=>
       simp only [movesBy, List.foldr_cons] at ih ⊢; rw [moves, ih (List.Nodup.of_cons D)]; by_cases h:i=j; · subst i; simp [f,(List.nodup_cons.mp D).1]
       simp [h,f]
 rw [hz v d]; exact funext fun i=>if_pos (p i)
local notation "Υ"=> chime K
include G
lemma chimes_main {j:Axis}{z:ℤ}: TestFamily K true (Υ j z F):= aux_test (flow_port K j z G)
lemma moving_c(k:Axis)(z:ℤ): moving v y (Υ k z F)= Υ k z (moving v y F) :=by
 induction v with
 | nil=>rfl
 | cons i v ih=>
    change Υ i _ (moving v y (Υ k z F))=_; rw [ih]; have he(L:List Axis): ∃ p:Finset Cover,InTest K true p false (moving L y F):=by induction L with | nil=> exact ⟨_,G⟩| cons j V ih=> obtain ⟨A,g⟩:= ih; exact ⟨_, flow_port K j (y j) g⟩
    exact twin_slide _ _ _ _ (he v).choose_spec
-- show by induction using twin_slide, even relative art manifests all exact. credit lifts.
lemma move_ticket (p:Cover) : moving v y (moving v p F)= moving v (p+y) F:=by
 induction v with
 | nil=>simp only [moving,List.foldr_nil]
 | cons i v ih=>
    let Z:= moving v p F; have hp(L:List Axis)(f:Family K){S:Finset Cover}(p:InTest K true S false f)(z:Cover):∃ A:Finset Cover, InTest K true A false (moving L z f):=by
       induction L with| nil=>exact ⟨_,p⟩|cons j l ih=>obtain ⟨A,h⟩:=ih; exact ⟨_,flow_port K j (z j) h⟩
    change Υ i (y i) (moving v y (Υ i (p i) Z)) = Υ i _ _
    rw [moving_c (hp v F G p).choose_spec, bumps K _ _ _ (hp v Z (hp v F G p).choose_spec y).choose_spec, add_comm]; unfold Z; rw [ih]; rfl
lemma move_void : moving v 0 F=F:=by induction v with| nil=>rfl| cons j v ih=> change Υ j 0 (moving v 0 F)=F; rw [ih,wake K j G]
private lemma negAxis(i:Axis)(r:ℤ)(p:i∉ v): moving v (r • step i) F=F:=by
 induction v with
 | nil=>rfl
 | cons j v h=>
    change Υ j ((r • step i:Cover) j) (moving v _ F)=_
    rw [h (fun t=>p (List.mem_cons_of_mem _ t)), show (r • step i:Cover) j=0 from ?_,wake K j G]; have ht:j≠i:=fun e=> p (e ▸ List.mem_cons_self); simp [ht,Ne.symm ht]
lemma move_one_axis (i:Axis)(p:i∈v)(d:v.Nodup)(r:ℤ): moving v (r • step i) F= Υ i r F:=by
 induction v with
 | nil=>nomatch p
 | cons j v ih=>
    change (Υ j ((r • step i:Cover) j) (moving v _ F))=_; have he(v:List Axis): ∃ p:Finset Cover, InTest K true p false (moving v (r • step i) F):=by induction v with|nil=> exact ⟨_,G⟩|cons i' v ih=>obtain ⟨X,p⟩:=ih; exact ⟨_,flow_port K i' ((r • step i:Cover) i') p⟩
    obtain h|h:= List.mem_cons.mp p
    · subst j; have hg:i∉ v:=(List.nodup_cons.mp d).1; rw [show (r • step i:Cover) i=r from (by simp)]
      rw [negAxis G v i r hg]
    rw [show (r • step i:Cover) j=0 from by simp [show i≠j from fun e=>(List.nodup_cons.mp d).1 (e ▸ h), Ne.symm (show i≠j from fun e=>(List.nodup_cons.mp d).1 (e ▸ h))],wake K j (he v).choose_spec, ih h (List.Nodup.of_cons d)]
omit G
noncomputable abbrev carriage(k:Cover)(F:Family K):Family K:= moving Vacancy.ordinate k F
open Vacancy
-- footprints credits
variable {r:ℕ}
lemma carriage_test (u:Cover) (h:InTest K true (pavilion (nodeC p) r) false F): InTest K true (pavilion (nodeC (p+u)) r) false (carriage u F):=by unfold carriage; rw [← moved_box ordinate u ordinates ordinate_one]; exact moving_test _ _ _ h
lemma moving_color (h:InTest K true (pavilion (nodeC p) r) false F)(u:Tapestry.Neutral K F) : Neutral K (moving v y F):=by induction v with| nil=> exact u| cons i v ih=> apply chime_cov; exact moving_test v y r h; exact ih
variable {F0:ℕ→Family K}(h:BQueue (pavilion (nodeC p) r) F0 F)
include h
lemma cueC (i: Axis)(z:ℤ):BQueue (pavilion (nodeC (p+z • step i)) r) (fun j=>Υ i z (F0 j)) (Υ i z F):=by
 have he:reflectedBox i z (reflectedBox i 0 (pavilion (nodeC p) r))⊆ pavilion (nodeC (p+z • step i)) r:=by rw [support_translation,sub_zero]; exact chimes_pav ..
 exact VacuumSelection.VelourWiggle.cueMono ((h.revolve i 0).revolve i z) he
lemma cueMove:BQueue (pavilion (nodeC (movesBy v y p)) r) (fun i=> moving v y (F0 i)) (moving v y F):=by induction v with| nil=> exact h| cons j v ih=> exact cueC ih j (y j)
lemma cueArr : BQueue (pavilion (nodeC (p+y)) r) (fun i=> carriage y (F0 i)) (carriage y F):=by rw [←moved_box ordinate y ordinates ordinate_one]; exact cueMove ordinate y h
omit h
include G in
lemma reach_clock (p:Cover)(j:Axis)(z:ℤ) : Υ j z (carriage p F)= carriage (p+z • step j) F:=by
 unfold carriage; rw [show p+z • step j=z • step j+p from add_comm .., ← move_ticket G ordinate p (z • step j), move_one_axis G ordinate j (ordinates _) ordinate_one z, moving_c G ordinate p j z]
-- test price joint.D raft bind uniform.S Θ. 
end CasaF
end YM.CF.Buffered.Afterglow.Tower
