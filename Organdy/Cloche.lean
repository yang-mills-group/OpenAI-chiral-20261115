import Organdy.Chiara
import Organdy.Sceptre
import Organdy.Grandstand
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry


section
variable {K:Calibration}{N:Side}
/- Chronological alignment. versions of Buffered.Afterglow.Chamber's "twice". -/
private lemma anon_cross (i j:Axis)(e:j ≠ i)(s:ℤ)(x:Seat N) : (plane i s).anon N x j=x j := by
  simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,e,e.symm]

private lemma aligned_before (b:ℤ):
    ∃ z:ℤ, let s:=Heat.gaugeShift K.B z; s+K.ℓ ≤ b ∧ b ≤ s+stepgap K := by
  let c:ℤ:=4*K.B.val
  have hc:0<c:=by unfold c; positivity
  let z:=(b-K.ℓ)/c
  refine ⟨z,?_⟩; change c*z+K.ℓ ≤ b ∧ b ≤ c*z+stepgap K
  have he:=(Int.emod_add_mul_ediv (b-(K.ℓ:ℤ)) c)
  have hv:=Int.emod_nonneg (b-(K.ℓ:ℤ)) hc.ne'
  have h':=Int.emod_lt_of_pos (b-(K.ℓ:ℤ)) hc
  unfold stepgap; push_cast; change _ ∧ b ≤ c*z + ((K.ℓ:ℤ)+c)
  change _ + c*z = _ at he
  omega

/-- Leave room on the other side too. -/
private lemma inhalf {x:Seat N} (i:Axis){d:ℕ}{s b:ℤ}(a:s+K.ℓ ≤ b)(r:b ≤ s+stepgap K)(p:Chord b d (x i)) (h:d+addgap K ≤ (N).val):
    x∈ band N i s K.ℓ := by
  obtain ⟨y,t,e,q⟩:=p
  let n:=N
  have hz: (K.ℓ:ℤ) ≤ y-s := by omega
  have hp: y-s+(K.ℓ:ℤ) ≤ (N).val := by
    unfold addgap stepgap at *; omega
  let Y:=(y-s).toNat
  have hh:Y<(More n).val:=by change _< n.val*2; have w:0<n.val:=n.property; change _≤(n.val:ℤ) at hp; unfold Y; omega
  apply (band_spec ..).mpr
  rw [show x i - (s:Per (More N))=(Y:Per (More n)) from ?_,ZMod.val_natCast_of_lt hh]; swap
  · rw [←Int.cast_natCast,Int.toNat_of_nonneg (by omega),Int.cast_sub,q]
  unfold Y; omega


def chordy (S:Finset (Seat N))(i:Axis)(b:ℤ)(d:ℕ):=
  ∀ x∈S,Chord b d (x i)
lemma lineGrowth (i:Axis){s b:ℤ}(u:s+K.ℓ≤b)(v:b≤ s+stepgap K) {d:ℕ}{S:Finset (Seat N)}(a:chordy S i b d)(h:d+addgap K≤ (N).val) :
           let T:=hyphen i s S ∪ S
           S ⊆ band N i s K.ℓ ∧ chordy T i (2*s-(b+d)) (2*d+addgap K)∧
           ∀ j:Axis,j≠i → ∀ d', cows j S d'→ cows j T d':=by
  refine ⟨fun x p=>inhalf i u v (a x p) h,?_,?_⟩
  · intro x tx; rcases mem_union.mp tx with E|E
    · obtain ⟨p,t,rfl⟩:= mem_image.mp E; obtain ⟨y,hp,e,q⟩:= a p t
      refine ⟨2*s-y,by omega,by unfold addgap; push_cast; omega,?_⟩
      let x:=(plane i s).anon N p
      have ht : x i-(s:Per (More N))=-(p i-(s:Per (More N))) := across_coord i s _
      change ((2*s-y:ℤ):Per (More N)) = x i
      rw [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,q,eq_add_of_sub_eq ht]; ring
    obtain ⟨y,p,v',q⟩:=a _ E; refine ⟨y,by omega,?_,q⟩; unfold addgap; push_cast; omega
  intro j hv d' ⟨b,w⟩; refine ⟨b,?_⟩; intro x hx; rcases mem_union.mp hx with y|y
  · obtain ⟨x,hx',rfl⟩:=mem_image.mp y; rw [anon_cross i j hv]; exact w x hx'
  exact w x y



def boxed (j:Axis)(S:Finset Cover)(b:ℤ)(w:ℕ):=∀ y∈S,b≤y j ∧ y j≤b+w
lemma transportTurn (j:Axis){s b:ℤ}(u:s+K.ℓ≤b)(v:b≤ s+stepgap K){d:ℕ}{S:Finset Cover}
 (x:boxed j S b d):
 boxed j (Tower.reflectedBox j s S∪S) (2*s-(b+d)) (2*d+addgap K):=by
 intro y h
 have p:s≤b:=by omega
 rcases mem_union.mp h with z|z
 · obtain ⟨y,r,rfl⟩:=mem_image.mp z; have hx:=x y r
   -- reflectedBox?
   rw [fling_move _ _ j, if_pos rfl]; unfold addgap; omega
 specialize x y z; unfold addgap; omega
end
variable {I:Type}{P:Spine}{s:ℕ}{i:I→ℕ}
abbrev Tableaux(P:Spine)(s:ℕ)(i:I→ℕ):= ∀ x, List (Hookah (tunnel P s i x))
abbrev Clubs(P:Spine)(s:ℕ)(i:I→ℕ):= ∀ x,Club (tunnel P s i x)
local notation "H"=>P.calibration
local notation "N'" =>tunnel P s i

abbrev follow (P:Spine)(j:Axis)(s:ℕ)(f g:P.Test)(D:ℕ):=
 ∀ x:P.Spectrum0 j,
   ‖P.singleState j s x f‖^(2^D) ≤ (P.singleState j s x g).re


structure Cinema {P:Spine}{s:ℕ}{i:I→ℕ}(l:Filter I)(j:Axis)(w p:ℕ)
 (G:Clubs P s i)(L:Tableaux P s i)(D d:ℕ)(b:ℤ)(S:Finset Cover)
 (F:I→Buffered.Family P.calibration)(g:P.Test):Prop where
 price:Bolt l S (moment P s i) (patronise P s i)
    (fun x=>buffet (L x)) F g.val
 width:d+addgap P.calibration=(2^D)*(w+addgap P.calibration)
 interval:boxed j S b d
 scheduled:∀ᶠ x in l, Romp (G x) p (L x) ∧ (L x).length=2^D ∧
    chordy (Broad p (L x)) j b d ∧
    ∀ a,a≠j→cows a (Broad p (L x)) w

variable {l:Filter I}{k:I→ℕ}{j:Axis}{w p D d:ℕ}
  {G:Clubs P s i}{L:Tableaux P s i}{b:ℤ}{S:Finset Cover}
  {F:I→Buffered.Family P.calibration}{g:P.Test}

/-- Every movie schedules CS relative to itself with exponent 2 and produces
  another movie. -/
lemma Cinema.encore
 (a:Cinema l j w p G L D d b S F g)
 (R:RateNet l P i k):
 ∃ g' L' d' b' S' F', Cinema l j w p G L' (D+1) d' b' S' F' g'∧
   follow P j s g g' 1:=by
 obtain ⟨z,t,q⟩:=aligned_before (K:=P.calibration) b

 let σ:=Heat.gaugeShift P.calibration.B z
 let g':=aureole P.calibration j σ g *g
 let u(x):= (L x).map fun y=>y.twistL j σ
 let L':=fun x=>u x++L x
 let T:=Tower.reflectedBox j σ S ∪ S
 have B:=
   (a.price.revolve j σ).product a.price
 let F':=fun x=>Tower.mirror H j σ (F x) * F x
 have h:Bolt l T (moment P s i) (patronise P s i) (fun x=>buffet (L' x)) F' g'.val:=⟨B.queue,fun r=>by
    dsimp only [L',u]
    rw [buffet_tack,buffet_turn]
    exact B.sees r⟩
 have y:Tower.region j σ (H).ℓ S:= fun x v=>t.trans ((a.interval _ v).1)
 refine ⟨g',L',2*d+addgap H,2*σ-(b+d),T,F',⟨h,?_,transportTurn j t q a.interval,?_⟩, fun x=>prestissimo P s j x S z g a.price.queue.toBe y⟩

 · rw [pow_succ]; calc
      _ = 2*(d+addgap H) := by ring
      _ = _ := by rw [a.width]; ring

 have v: ∀ᶠ x in l, d+addgap H ≤ (N' x).val:=
    R.both (B:=fun i _=>d+addgap H ≤ (side P.run i s).val)
      (((Papal.count_grows P.run s).eventually_ge_atTop _).mono fun _ z=>Eventually.of_forall fun _=>z)

 filter_upwards [v,a.scheduled] with x w₁ ⟨f,c,v₁,d₁⟩
 obtain ⟨e,b₁,y⟩:= lineGrowth j t q v₁ w₁
 dsimp only [L',u]
 rw [Broad_append,Broad_turn]
 refine ⟨(f.away j σ).tack f (by rw [Broad_turn];exact west H j σ _ e),?_,b₁,fun i p=>y i p _ (d₁ i p)⟩
 rw [List.length_append,List.length_map,c,pow_succ,mul_two]

#print axioms Cinema.encore

lemma Cinema.trip
 (a:Cinema l j w p G L 0 d b S F g)
 (R:RateNet l P i k)(r:ℕ):
 ∃ g' L' d' b' S' F', Cinema l j w p G L' (r+1) d' b' S' F' g' ∧
   follow P j s g g' (r+1):=by
 induction r with
 | zero=>exact a.encore R
 | succ r ih=>
    obtain ⟨x,l',d',b',S',F',u,q⟩:=ih
    obtain ⟨y,t,d,z,c,H',w,h⟩:=u.encore R
    refine ⟨_,_,_,_,_,_,w,fun a=>?_⟩
    rw [pow_succ _ (r+1),pow_mul]
    exact (pow_le_pow_left₀ (by positivity) ((q a).trans (Complex.re_le_norm _)) _).trans (h a)

/-- If we can fund every dyadic density with *Common*
    base charge, this authorizes ANY related single at same base charge,
    for any P selected prices by a tail argument. -/
def Fitted (l:Filter I)(j:Axis)(w p:ℕ)(G:Clubs P s i)(a:ℝ):Prop:=
 ∀ (z:ℕ) (b:ℤ) (r:ℕ) (S:Finset Cover) (L:Tableaux P s i)
    (F:I→Buffered.Family P.calibration) (g:P.Test), 
    Cinema l j w p G L z r b S F g →
    ‖P.E s g.val‖ ≤ Real.exp a ^(2^z)

structure Profiled(j:Axis)(w p:ℕ)(b:ℤ) {N:Side}(g:Club N)(y:Mark N):Prop where
 fit: ∃ A,g.accepts A ∧ A.x=y ∧ chordy (Lattice.halo p A.S) j b w ∧
    ∀ a,a≠j→cows a (Lattice.halo p A.S) w
-- need ∀ x,profiled not just eventually (can fallback with singleton x same, dummy S univ)
variable {Y:(z:I)→Mark (tunnel P s i z)}
lemma held {l:Filter I}(g:P.Test)
 (a:Bolt l S (moment P s i) (patronise P s i) Y F g.val)
 (t:∀ᶠ z in l,Profiled j w p b (G z) (Y z))
 (c:boxed j S b w):
 ∃ L,Cinema l j w p G L 0 w b S F g:=by
 have h(z:I): 
     ∃ A:Hookah (N' z),A.x=Y z ∧ (Profiled j w p b (G z) (Y z) →
       (G z).accepts A ∧ chordy (Lattice.halo p A.S) j b w ∧ ∀ a,a≠j→cows a (Lattice.halo p A.S) w):=by
     by_cases g:Profiled j w p b (G z) (Y z)
     · obtain ⟨X,e,r,p⟩:=g.fit; exact ⟨X,r,fun _=>⟨e,p⟩⟩
     exact ⟨{x:=Y z, S:=∅,o:=0},rfl,fun i=>(g i).elim⟩
 choose A q k using h
 let L z:= [A z]
 have u:(fun z=>buffet (L z))=Y:=funext fun z=>by rw [show L z=A z::[] from rfl,buffet_more,buffet_empty,mul_one,q]

 refine ⟨L,?_,by simp,c,?_⟩
 · rw [u];exact a
 filter_upwards [t] with z d; obtain ⟨e,v⟩:=k z d
 exact ⟨Romp.one e,rfl,by simpa [L,Broad_more] using v⟩

theorem festival {δ:ℝ} (Z:P.Register) (R:RateNet l P i k) (fund:Fitted l j w p G δ)
 (g:P.Test)
 (a:Bolt l S (moment P s i) (patronise P s i) Y F g.val)
 (t:∀ᶠ z in l,Profiled j w p b (G z) (Y z))
 (c:boxed j S b w)(x:P.Spectrum0 j):
 ‖P.singleState j s x g‖ ≤ Real.exp δ:=by
 obtain ⟨L,h⟩:=held g a t c
 refine swell P s j x Z g (Real.exp_pos _).le fun n=>?_
 obtain ⟨f,_,_,_,_,_,y,q⟩:=h.trip R n
 rw [←pow_succ']
 exact ⟨f,q,(Complex.re_le_norm _).trans (fund _ _ _ _ _ _ _ y)⟩
#print axioms festival
