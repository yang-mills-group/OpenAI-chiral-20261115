import YM.CF.Buffered.Solids
import YM.CF.Buffered.Congress
/-!
# Position both bilinear marks in one level-zero tile with room to spare

Center along ALL axes using a genuine symmetry of the warm trajectory, as
chosen before R? (translation scales here chosen after `R`, before x/n/m).
Keep the entire construction outside any larger periods used downstream.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 23000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory Cube SU Fock Lat Spire Scroll ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Lifted Heat Advance Solid
open Region Roost Ordered
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}
variable {N Q P D B: Side}{R e w:ℕ}
-- pay min with width worst-case at endpoints and an extra whole walk buffer. This cost only at choosing a HUGE d'
lemma step_cap (x z:Cover) (d:Lattice.Step) (g:Damp P (e+1) (x-z)): Damp P e (x+d.vec-z):=by
 intro i; specialize g i; cases d with| mk j q => cases q <;> simp only [Pi.add_apply,Pi.sub_apply, Lattice.Step.vec,step_apply] at * <;> by_cases p:i=j <;> simp [p] at * <;> omega
private lemma cloth_walk (w:ℕ)(x z:Cover)(l:Walk) (g:Damp P (w+l.length) (x-z)) (q:Cover)(h:q∈visits x l): Damp P w (q-z):=by
 induction l generalizing x with
 | nil => rw [show q=x from by simpa [visits] using h]; exact g
 | cons d l ih=>
   simp only [visits,List.mem_cons] at h; rcases h with rfl|h
   · intro i; specialize g i; rw [List.length_cons] at g; omega
   apply ih _ _ h; apply step_cap; rw [List.length_cons,←Nat.add_assoc] at g; exact g
namespace Lead
variable (A:Lead R)(P:Side)(m:ℕ)(z:Cover)
-- buffer payer witness
structure Budgeted : Prop where
 born:Damp P (m+2*R) (nodeC A.birth-z)
 gone:Damp P (m+2*R) (nodeC A.death-z)
private def stripT {N: Side}(A:Lead R) := ((visits (nodeC A.birth) A.traceV).toFinset.image (wrap (More N)))
private lemma upper_half (A:Lead R)(v:SU.Slot) : withinM (Tset N) (A.upper N v) := by unfold withinM upper basisC; rw [map_smul,within_basis _ (Lifted.index N A.birth (upSpin _) v) ((mem_Tset ..).2 (up_half _))]
private lemma lower_half (A:Lead R)(v:SU.Slot) : withinM (Tset N)ᶜ (A.lower N v) :=by unfold withinM lower basisC; rw [map_smul,within_basis _ (Lifted.index N A.death (dnSpin _) v) (mem_compl.mpr fun x=> dn_half A.slot ((mem_Tset ..).1 x))]
lemma chant_support : AtSupport false (stripT (N:=N) A) A.chant := by
 let S:= (visits (nodeC A.birth) A.traceV).toFinset
 have he(x:Cover)(b:SU.Slot)(i:SpinIdx)(h:nodeC x∈S) : withinM (modesIn N (stripT A)) (basisC N x i b):= by
    unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index N x i b)]; rw [modes_at]; change node (wrap N x)∈_; rw [node_of]; exact mem_image_of_mem (wrap _) h
 refine ⟨Env.compact ?_,fun _ _ a _=>?_,fun V=> Reed.Fine.scale (Reed.Fine.sumF _ _ (fun i _=> Reed.Fine.sumF _ _ (fun j _=> ((fine_remove (A.lower N j) (A.lower_half j) (he A.death j _ ?_)).grow (fine_create (A.upper N i) (A.upper_half i) (he A.birth i _ ?_))).scale _))) _⟩
 · unfold chant birthOp; have hi(i j:SU.Slot): Continuous (fun V:Fields N=> A.coil V.1 i j):= ((((matter_cont.comp (Wilson.continuous_travel _ _)).matrix_elem i j).comp (on_cont N)).comp continuous_fst); fun_prop (disch:=exact hi ..)
 · unfold chant birthOp coil laps; rw [show travel (onC N _) (nodeC A.birth) _= _ from travel_local (nodeC A.birth) A.traceV _ _ fun x u v=> (on_agree _ a) x (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v)] -- tune
 · apply List.mem_toFinset.mpr; rw [←A.moves]; apply show ∀ s:Cover, ∀ l:Walk, stop s l∈visits s l from fun s l=>by induction l generalizing s<;> simp_all [stop,visits]
 apply List.mem_toFinset.mpr; cases A.traceV<;> simp [visits]
variable (T:Planck (More N) P D)(r:Rail (Uniform D))
variable {P}
lemma bill (k:Budgeted A P m (T.sail r)) : AtSupport false (wallZ T r m) A.chant:=by
 apply A.chant_support.mono; intro x v; obtain ⟨z',u,rfl⟩:= mem_image.mp v; refine (Solid.seam ..).2 ⟨z'-T.sail r,cloth_walk _ (nodeC A.birth) _ A.traceV (A.costs.symm ▸ k.born) _ (List.mem_toFinset.mp u),?_⟩; unfold Planck.zone; rw [add_sub_cancel]
end Lead
namespace Melody
variable (A:Melody B R)(P:Side)(e:ℕ)(x:Cover)
def Budget := Lead.Budgeted A.first P e x ∧ Lead.Budgeted A.last P e x -- conflict cube?
private lemma bare_cost (s:Side)(T:Support (More N))(t:AtSupport false T (A.first.chant))(u:AtSupport false T (A.last.chant)) (b:Bool) : AtSupport false T (A.goal b):=by
 unfold goal; rw [sub_eq_add_neg,←neg_smul]; split; exact (t.mulM u).addM ((AtSupport.oneM T).smulM _); exact t.addM ((AtSupport.oneM T).smulM _)
lemma global (b:Bool): AtSupport (n:=N) false univ (A.goal b):=bare_cost A B univ ((A.first.chant_support).mono (subset_univ _)) (A.last.chant_support.mono (subset_univ _)) b
variable (T:Planck (More N) P D)(r:Rail (Uniform D))
variable {P}
lemma bill (t: Budget A P e (T.sail r))(b:Bool) : AtSupport false (wallZ T r e) (A.goal b):=bare_cost A P _ (A.first.bill e T r t.1) (A.last.bill e T r t.2) b
lemma mirror_bill (p:Budget A P e (T.sail r))(i:Axis)(g:¬endsAt r i): Budget (A.mirror i (upstairs' P r i)) P e (T.sail (Region.next i r)):=by
 let s:= upstairs' P r i
 have he(z:Cover)(h:Damp P (e+2*R) (z-T.sail r)): Damp P (e+2*R) ((plane i s).motion z-T.sail (Region.next i r)) := by
    have hx:=(next_motion r T g (z-T.sail r)); rw [add_sub_cancel] at hx; intro j; rw [hx,add_sub_cancel_left]; specialize h j; rw [flip_iff]; split<;> omega
 have hp(z:Cover): nodeC ((plane i s).flee z)=(plane i s).motion (nodeC z):=((plane i s).mote z).symm
 refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩; all_goals dsimp only [Lead.mirror,mirror]; rw [hp]; first | exact he _ p.1.born|exact he _ p.2.born|exact he _ p.1.gone|exact he _ p.2.gone
end Melody
-- determine translation, on cover, ignoring size of P; then output sizes that pay this.
namespace Venue -- in Ballad
variable (B:Side)(s:ℤ)
def flightL (A:Lead R)(i:Axis)(s:ℤ) := (A.mirror i 0).mirror i (pitchT B s)
def flight(A:Melody B R)(i:Axis)(s:ℤ) := (A.mirror i 0).mirror i (pitchT B s)
def towards(A:Melody B R)(s:ℤ) := (flight B (flight B (flight B (flight B A 0 s) 1 s) 2 s) 3 s)
abbrev liftL (A:Lead R)(s:ℤ):= flightL B (flightL B (flightL B (flightL B A 0 s) 1 s) 2 s) 3 s
private def changeL (v:Bool)(A: Lead R) := if v then A.birth else A.death
lemma liftLP (b:Bool) (A:Lead R) (i j:Axis) : changeL b (flightL B A i s) j= if j=i then changeL b A j+pitchT B s else changeL b A j:=by
 unfold flightL changeL; dsimp only [Lead.mirror]; by_cases h:j=i <;> cases b <;> simp [h, flee_pos, Ne.symm] <;> ring
lemma ahead (b:Bool)(A:Lead R)(i:Axis): changeL b (liftL B A s) i= changeL b A i+pitchT B s:=by
 simp_rw [liftL,liftLP]
 fin_cases i <;> rfl
lemma warmK (P:Melody B R)(i:Axis)(b:Bool) : reflMark (n:=N) i (pitchT B s) (reflMark i 0 (P.goal b))= (flight B P i s).goal b:=by rw [Melody.mirror_goal, Melody.mirror_goal]; rfl
-- natural archimed: first choose translation so all endpoints fit every sufficiently large d'. This is already after K.vertex & width price,C₁. does not depend on tilt or heat.
lemma heads (w:Cover)(e:ℕ) : ∀ᶠ k:ℕ in atTop, ∀ i:Axis, (e:ℤ) ≤ w i+2*pitchT B k:=by
 rw [eventually_all]; intro i; filter_upwards [eventually_ge_atTop (e+(w i).natAbs)] with k p
 unfold pitchT; have he:0<B.val:=B.property; have hv:(e:ℤ) ≤ w i+k := by omega
 nlinarith
lemma endure (A:Lead R)(v:ℕ) : ∀ᶠ k:ℕ in atTop, ∀ᶠ l:Side in atTop, (liftL B A k).Budgeted (Domain l B) v 0:=by
 let w:=v+2*R
 filter_upwards [heads B (nodeC (A.birth)) w,heads B (nodeC (A.death)) w] with k p h
 have he (b:Bool)(i:Axis) : nodeC (changeL b (liftL B A k)) i=nodeC (changeL b A) i+ 2*pitchT B k:=by unfold nodeC; simp_rw [Pi.add_apply, Pi.smul_apply,Pi.one_apply,ahead,two_smul,two_mul]; abel
 have hp(z:Cover): ∀ᶠ l:Side in atTop, ∀ i:Axis,z i+w ≤ (Domain l B).val :=by
    rw [eventually_all]; intro i; filter_upwards [eventually_ge_atTop (⟨(z i).natAbs+w+1,by omega⟩: Side)] with l hl; change _+w+1 ≤ l.val at hl; unfold Domain CSide More; simp only [PNat.mul_coe, Nat.cast_mul] -- check shape
    have hk: 0<B.val:= B.property; have hv:z i + w ≤ l.val:=by omega
    change z i+w≤ (l.val:ℤ)*2*B.val*2; nlinarith
 filter_upwards [hp (nodeC (liftL B A k).birth),hp (nodeC (liftL B A k).death)] with l b a -- tune
 constructor <;> intro i <;> rw [sub_zero] <;> constructor
 · rw [show nodeC (liftL B A k).birth i=_ from he true i]; exact p i
 · exact b i
 · rw [show nodeC (liftL B A k).death i=_ from he false i]; exact h i
 exact a i
variable {B}
lemma stamp (A:Melody B R)(w:ℕ) : ∀ᶠ v:ℕ in atTop, ∀ᶠ l:Side in atTop, Melody.Budget (towards B A v) (Domain l B) w 0:= ((endure B A.first w).and (endure B A.last w)).mono fun v t=> t.1.and t.2
end Venue
namespace Markwalk
open Burn Crust Grid
variable {C: Conveyor K}{m:Side}{n:ℕ}{h:K.Allowed m n}(Z:Bedded C h) (s:ℤ)
variable (A:Melody K.B K.vertex)
include Z
lemma word_m (i:Axis)(b:Bool): markedRead ((Venue.flight K.B A i s).goal b) (C.loom m 0) (denZ (C.warm m n 0) K.P (C.loom m 0))=markedRead (A.goal b) (C.loom m 0) (denZ (C.warm m n 0) K.P (C.loom m 0)):=by
 rw [←Venue.warmK]; apply Z.warm_move (z:= -s) _ i (A.global b); exact (show 0-pitchT K.B s=pitchT K.B (-s) by unfold pitchT; ring)
lemma at_m (b:Bool): markedRead ((Venue.towards K.B A s).goal b) (C.loom m 0) (denZ (C.warm m n 0) K.P (C.loom m 0))=markedRead (A.goal b) (C.loom m 0) (denZ (C.warm m n 0) K.P (C.loom m 0)):=by unfold Venue.towards; rw [word_m Z, word_m Z, word_m Z, word_m Z]
omit Z
-- assume d' chosen sufficiently large with position A on it. use integer witness instead of threshold specific odd multiples.
variable (J:Tiling K)
-- copy construction via paths. top support propagated by coat_prod; hot orientation from path.
variable {A}
local notation "ℒ" => gaugedTop K J 0
inductive MarkPath (J:Tiling K) (m:Side)(A:Melody K.B K.vertex) : Rail (Uniform (J.qcount m))→ Melody K.B K.vertex→Prop where
 | home : MarkPath J m A 0 A
 | marches {r:Rail (Uniform (J.qcount m))}{T:Melody K.B K.vertex} (p:MarkPath J m A r T) (i:Axis)(v:¬endsAt r i) : MarkPath J m A (Region.next i r) (T.mirror i (upstairs' (gaugedTop K J 0) r i))
variable {J}{r:Rail (Uniform (J.qcount m))}
lemma carrier (t: Melody.Budget A (gaugedTop K J 0) e 0) (P:K.takes m)(D: Melody K.B K.vertex)(f: MarkPath J m A r D): Melody.Budget D (gaugedTop K J 0) e ((orderV K J 0 P).sail r):=by
 induction f with
 | home => rw [show (orderV K J 0 P).sail 0=0 from funext fun i=>by simp [Planck.sail]]; exact t
 | marches _ i v ih=> exact Melody.mirror_bill _ _ (orderV K J 0 P) _ ih i v
lemma allowance (t:Melody.Budget A (gaugedTop K J 0) e 0)(v:K.ℓ ≤ e)(P:K.takes m)(T:Melody K.B K.vertex)(f:MarkPath J m A r T)(b:Bool): AtSupport false (glass J 0 (r:=r) P) (T.goal b):= (Melody.bill T _ (orderV K J 0 P) _ (carrier t P _ f) b).mono (monotoneV _ _ v)
lemma freshV (t:Melody.Budget A (gaugedTop K J 0) e 0)(v:w<e)(P:K.takes m)(Q:Rail (Uniform (J.qcount m))→ Melody K.B K.vertex)(p:∀ r,MarkPath J m A r (Q r)): Payments w (fun x:Single (K.c m)=> Crust.Grid.ledge (orderV K J 0 P) (node x.1.1)) Q:=by
 let V:=orderV K J 0 P
 have ht(r:Rail (Uniform (J.qcount m)))(z:Cover)(u:Damp ℒ (e+2*K.vertex) (nodeC z-V.sail r)): Fresh w (fun x:Single (K.c m)=> ledge V (node x.1.1)) r z:= fun x a=> up_ledge V r (by omega: w<e+2*K.vertex) _ ((Solid.seam ..).2 ⟨_,u,by unfold Planck.zone; rw [add_sub_cancel]⟩) _ a
 intro i; have he:= carrier t P _ (p i); exact ⟨ht _ _ he.1.born, ht _ _ he.1.gone, ht _ _ he.2.born, ht _ _ he.2.gone⟩
private def sumL {L:Axis→Side}(r:Rail L):ℕ:=∑ i,(r i).val
-- induction step on nat decreasing rank sum
private lemma amends (r: Rail (Uniform (J.qcount m)))(P:K.takes m) (g: r ≠ 0): ∃ t i, sumL t < sumL r ∧ ¬endsAt t i ∧ r=Region.next i t := by
 obtain ⟨i,hi⟩:= Function.ne_iff.mp g -- tune
 let L:= Uniform (J.qcount m); have he:= landing_ge (J.native_ord m P 0).onGrid i; change 2≤(L i).val at he
 have hp:¬(r i).val=0:= fun x=> hi (Fin.ext (by change _=(0:Fin _).val; rw [x]; rfl))
 let d:=(r i).val; let u:Fin (L i).val:=⟨d-1,by have h: d<(L i).val:= (r i).isLt; omega⟩; let t:= update r i u
 have hz:(t i).val=d-1:=by rw [show t=update r i u from rfl, update_self]
 have ht:d-1<d:=by unfold d; omega
 have hx:¬endsAt t i:=by unfold endsAt; rw [hz]; have h:d<(L i).val:= (r i).isLt; change ¬_= (L i).val; omega
 refine ⟨t,i,sum_lt_sum (fun j _=>?_) ⟨i,mem_univ _,hz ▸ ht⟩,hx,?_⟩
 · by_cases u:i=j; subst j; exact hz ▸ ht.le; unfold t; rw [update_of_ne (Ne.symm u) _ _]; -- tune
 · funext j; by_cases h:j=i; subst j; apply Fin.ext; unfold endsAt at hx; rw [next_val, if_neg (show ¬_ from hx),hz]; change d=_; omega
   rw [next_at t i h]; unfold t; rw [update_of_ne h]
lemma receives (J:Tiling K)(P:K.takes m)(A:Melody K.B K.vertex)(r:Rail (Uniform (J.qcount m))) : ∃ B, MarkPath J m A r B:=by
 suffices he:∀ k:ℕ,∀ r:Rail (Uniform (J.qcount m)),sumL r=k → ∃ B,MarkPath J m A r B from he _ _ rfl; intro k; induction k using Nat.strong_induction_on with| h k ih=>
 intro r w; by_cases u:r=0; · rw [u]; exact ⟨A,.home⟩
 obtain ⟨t,i,v,p,x⟩:= amends r P u; obtain ⟨Q,z⟩:= ih (sumL t) (by rwa [←w]) t rfl; rw [x]; exact ⟨_,z.marches i p⟩
end Markwalk
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Markwalk.at_m
#print axioms YM.CF.Buffered.Ballad.Markwalk.receives
