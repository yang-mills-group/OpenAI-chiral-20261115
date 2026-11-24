import YM.CF.Buffered.Theater
import YM.CF.Buffered.Smear
/-!
# Need only the ember hypothesis on Bill as comparison of Tickets:
 payments match from the period-list history on PAYER, other readings
 match directly by structure. For one particular Tilt launch at these sizes.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Buffered.Mail
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Reflect Phase RP MeasureTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye Py
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid Wilson
open Colony (pullS pulse)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m n k d l N P B v:Side}
section grammar
variable (T:Planck N P k)(K:Planck N B n)(H:Planck P B m)(a:Rail (Uniform n))
def ret (m:Side){n:Side}(a:Rail (Uniform n))(i:Axis) : Fin m.val := ⟨(a i).val%m.val,Nat.mod_lt _ m.property⟩ -- remove implicit N
lemma scales (u:Cover): (slump T).cut (K.zone a u)= H.zone (ret m a) u:=by
 unfold Planck.zone; rw [show (slump T).cut (wrap N _)= _ from (Macrame.branch .. : _)]; unfold Planck.sail; rw [map_add,map_add]; congr 1
 funext i; simp only [wrap_here]; unfold ret; simp only; have he: ((a i).val:ℤ)=m.val*((a i).val /m.val :ℕ)+(↑((a i).val % m.val):ℤ):=by exact_mod_cast (Nat.div_add_mod (a i).val m.val).symm
 nth_rw 1 [he]; rw [mul_add, ←mul_assoc,H.int_size.symm]; push_cast; simp
lemma ret_zero(m n:Side): ret m (0:Rail (Uniform n))=0:=by funext i; apply Fin.ext; simp [ret]
lemma peek (H: Landing (Uniform m)) : shade (ret m a)=shade a :=by
 ext j; obtain ⟨u,h⟩:= H j; change m.val=u+u at h; have he: 2∣m.val:=⟨u,by omega⟩; simp only [Region.shade,mem_filter,mem_univ,true_and,ret,Nat.mod_mod_of_dvd _ he] -- tune
end grammar
variable (K:Ordered m v d)(H:Ordered n v l) (G:Planck m n k)
local notation "T"=> gauge_plan (SugarGrid G B)
local notation "r" => (pulse G)
def picture (G:Planck m n k) {B:Side}(U:Pack n B): Pack m B:= (Mail.weave (gauge_plan (SugarGrid G B)) (show Config SU.group _ from U.1), pullS G U.2)
lemma encores (x:Locale v B): whole K x= picture G (whole H x):=by
 apply Prod.ext; swap
 · funext i; obtain ⟨⟨a,w⟩,rfl⟩:= K.pebbles.slots.surjective i; let A:= K.pebbles; let B':= H.pebbles; let j:= B'.zone (ret l a) w.val
   change (whole K x).2 (A.zone a w.val)=(whole H x).2 ((pulse G).cut (A.zone a w.val)); rw [show (pulse G).cut _= j from scales (forG m n G) A B' a w.val]; let q:=ofpost ∅ w; rw [← show _ = (whole K x).2 (A.zone a w.val) from Ordered.cand K _ a q,← show _= (whole H x).2 j from Ordered.cand H _ _ q]; unfold whole; rw [atCube,atCube,reeling K.onGrid,reeling H.onGrid,peek]
   exact H.onGrid
 funext ⟨i,g⟩; obtain ⟨⟨a,w⟩,rfl⟩:= (K.sugar B).slots.surjective i; let A:=K.sugar B; let B':=H.sugar B; let p:Rail (Uniform l):=ret l a; let v:=A.zone a w.val; let P:=B'.zone p w.val
 change _= (whole H x).1 ((slump T).cut v,g); rw [show (slump T).cut v=P from scales T A B' a w.val]; let z:= ofpost {g} w; change (whole K x).1 (A.zone a w.val,g)=_; rw [← show _ = (whole K x).1 (A.zone a w.val,g) from K.butter _ a g z, ← show _=(whole H x).1 (P,g) from H.butter _ p g z]; unfold whole; unfold p; rw [atCube,atCube,reeling K.onGrid,reeling H.onGrid,peek _ H.onGrid] -- tune
include G
lemma pond (u: Tor (GridN v))(x:Locale v B): small K u x=small H u x:=by unfold small wholeWater; rw [encores K H G x]; unfold picture; dsimp only; rw [Colony.same_water B G]; rw [show (r).cut _= _ from scales (forG m n G) K.pebbles H.pebbles _ u.val,ret_zero] -- tune
lemma quilt (u:Post (CSide v B))(x:Locale v B) : K.canvas 0 u (whole K x)=H.canvas 0 u (whole H x):=by
 unfold Ordered.canvas grain; rw [encores K H G x]; unfold picture; dsimp only [Function.comp_apply]; rw [Colony.painted B G, up_sends (K:=K),up_sends (K:=H)]; rw [scales T (K.sugar B) (H.sugar B),ret_zero]
lemma payerV {e x:ℝ} (u:Locale v B) (h:u∈permitted K e x): whole H u∈payer n B e:=by apply tallyP (β:=0); apply (permitted_iff H e x u).mp ?_ |>.1; unfold permitted; unfold permitted at h; simp_rw [←pond K H G]; exact h -- tune
variable {e x:ℝ}(U:Ticket m v B d e x)(V:Ticket n v B l e x)
def Ember (G:Planck m n k) (U:Ticket m v B d e x)(V:Ticket n v B l e x): Prop := ∀ F:Pack n B, F∈ payer n B e → picture G F∈ payer m B e → ∀ z:Index m, Region.tab U.pin U.W z (picture G F)=Region.tab V.pin V.W ((pulse G).cut z) F -- tune namespace
lemma sizes (h:Ember G U V): Ticket.Coherent V U:= by
 refine ⟨fun i p=>(pond U.K V.K G i p).symm,fun i p a=>?_,fun i p _=>(quilt U.K V.K G i p).symm⟩
 unfold Ticket.tabV; have he:(pulse G).cut (U.K.pebbles.zone 0 i.val)=V.K.pebbles.zone 0 i.val:=by rw [show (pulse G).cut _= _ from scales (forG m n G) U.K.pebbles V.K.pebbles _ i.val, ret_zero]
 have ht:p∈permitted U.K e x:=by unfold permitted at *; simp_rw [pond U.K V.K G]; exact a
 rw [encores U.K V.K G p]; symm; apply (h (whole V.K p) (tallyP ((permitted_iff V.K ..).mp a).1) (encores U.K V.K G p ▸ tallyP ((permitted_iff U.K ..).mp ht).1) _).trans; rw [he]
end YM.CF.Buffered.Mail
#print axioms YM.CF.Buffered.Mail.sizes

namespace YM.CF.Buffered.Concert
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Reflect Phase RP MeasureTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye Py
open Mail
-- same anchored comparison doesn't demand plus comparisons at top (if providing plus, substitute paired-minus y via common flat & verify using induced repeated comparison).
variable {K:Calibration}{C:Conveyor K}{V:SpanCal K}{J:Tiling K}{x:ℕ}
structure Tickets (K:Calibration)(C:Conveyor K)(J:Tiling K)(n:ℕ) where
 history (m:Side)(p:K.Allowed m n): Bedded C p
 offset (m k:Side)(q: K.Allowed K.q n)(a:K.Allowed m n)(b:m=K.q*k) : |starfare C K.q n-starfare C m n/(k.val:ℝ)^4| ≤ 2
 ember (m k: Side) (p: K.Allowed m n)(q: K.Allowed K.q n)(b:m=K.q*k) : Mail.Ember (screen₂ K n b) ((history m p).permit J) ((history _ q).permit J)
def Tickets.logo (p:Tickets K C J x): Flipbook K J C x:= ⟨p.history, fun m h v=> (by obtain ⟨k,d,b⟩:= h.1; exact Mail.sizes (screen₂ K x b) ((p.history m h).permit J) _ (p.ember m k h v b)), p.offset⟩

-- rates for printing before numerical x. see Guarantor for enough-large packs.
lemma period_payment (A:∃ N:ℕ,∀ i:ℕ, N ≤ i → Nonempty (Tickets K C J i)) (t:enrollment V ≤ K.x) (u:under V K.q) (v:under V (K.q*3)): Printed K C J V :=⟨Eventually.mono (eventually_ge_atTop A.choose) (fun i ih=> ⟨(A.choose_spec i ih).some.logo⟩),t,u,v⟩
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.Tickets.logo
