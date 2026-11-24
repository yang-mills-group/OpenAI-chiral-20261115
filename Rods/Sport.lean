import YM.SU5.FiniteGaugeData.Pannier.Trefl
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Buffered.Afterglow Buffered.Afterglow.Journey
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{m n:Side}{U B l:ℕ}
open Lifted Reflect Phase
local notation "N"=>K.c m
/- Work on COARSE root labels T. Allow arbitrary fine n. S is a fat safety on N, *not* actual pose support required = R.Sport infers fine band and exact re.Pricing assumes distinct coarse supports cells (tunable via U). At n=N no difference. -/
structure Sport (K:Calibration)(m n:Side)(T:Type) where
 place:T → Support (More (K.c m))
 pose:T → Mark n
 mirror: Axis → ℤ → T → T
 castM:Axis → ℤ → ℤ -- fine heat clock at n corresponding to coarse integer seam gaugeShift
 stage(a:Axis)(d:ℤ)(o:T):place o ⊆ band (K.c m) a (Heat.gaugeShift K.B d) K.ℓ → AtSupport false (band n a (Heat.gaugeShift K.B (castM a d)) K.ℓ) (pose o)
 charge(a:Axis)(d:ℤ)(o:T)(hp:place o ⊆ band (K.c m) a (Heat.gaugeShift K.B d) K.ℓ):pose (mirror a d o)= reflMark a (Heat.gaugeShift K.B (castM a d)) (pose o)
 town(a:Axis)(d:ℤ)(o:T): place (mirror a d o)= (place o).image ((plane a (Heat.gaugeShift K.B d)).anon (K.c m)) -- $hyphen
variable {T:Type}(S:Sport K m n T)(R:Mark n→ℂ)(p:Twosome K n R)
namespace Sport
def film (l:List T) : Mark n:=(l.map S.pose).prod
def hopit : List T → Support (More N) | []=> ∅|i::l=> S.place i ∪ hopit l
def race(l:List T):Prop:=l.Pairwise (fun i j=>Disjoint (S.place i) (S.place j))
set_option linter.unusedTactic false in
lemma hopit_mem {l:List T}{x}: x∈ hopit S l ↔ ∃ t∈l,x∈S.place t:=by induction l with| nil=>simp[hopit]| cons i l h=> simp[hopit,h]
lemma hopit_app (l v:List T):hopit S (l++v)=hopit S l∪ hopit S v:=by ext x; simp [hopit_mem]; aesop
-- $isometry via injectivity of anon, check
lemma anon_inj (a:Axis)(z:ℤ)(W:Side): Injective ((plane a z).anon W):= (show Function.Involutive ((plane a z).anon W) from fling_there a z).injective
lemma hops(a:Axis)(z:ℤ)(l:List T):hopit S (l.map (S.mirror a z))=(hopit S l).image ((plane a (Heat.gaugeShift K.B z)).anon N):=by
 classical
 induction l with|nil=>simp[hopit]| cons i l h=> simp[hopit,h,S.town,Finset.image_union]
lemma duos(a:Axis)(z:ℤ)(l:List T)(pS: hopit S l⊆band N a (Heat.gaugeShift K.B z) K.ℓ) (h:race S l): race S (l.map (S.mirror a z) ++ l):=by
 classical
 let f:Seat N→ Seat N:= (plane a (Heat.gaugeShift K.B z)).anon N
 let t:= anon_inj a (Heat.gaugeShift K.B z) N
 unfold race; refine List.pairwise_append.mpr ⟨List.pairwise_map.mpr ?_,h,?_⟩
 · refine h.imp (fun {i j} b=>?_); simp only [S.town]; apply disjoint_left.mpr; intro x p q
   obtain ⟨y,hj,e⟩:=mem_image.mp p; obtain ⟨w,hi,hq⟩:=mem_image.mp q; rw [show y=w from t (e.trans hq.symm)] at hj; exact (disjoint_left.mp b hj hi)
 · intro i v j w; obtain ⟨a',q,rfl⟩:=List.mem_map.mp v
   have hp:= west K a (Heat.gaugeShift K.B z) _ pS
   rw [S.town]; apply disjoint_left.mpr; intro x hq hj; obtain ⟨y,hA,g⟩:=mem_image.mp hq
   exact disjoint_left.mp hp (mem_image.mpr ⟨_,(hopit_mem S).mpr ⟨_,q,hA⟩,g⟩) ((hopit_mem S).mpr ⟨_,w,hj⟩) -- hyphen= .image
lemma paid(a:Axis)(z:ℤ)(l:List T)(ha:hopit S l⊆ band N a (Heat.gaugeShift K.B z) K.ℓ):AtSupport false (band n a (Heat.gaugeShift K.B (S.castM a z)) K.ℓ) (film S l):=by
 induction l with
 | nil=> exact AtSupport.oneM _
 | cons i l ih=>
   refine AtSupport.mulM (S.stage a z i ((subset_union_left).trans ha)) (ih ((subset_union_right).trans ha)) -- defeq?
lemma recount(a:Axis)(z:ℤ)(l:List T)(ha:hopit S l⊆ band N a (Heat.gaugeShift K.B z) K.ℓ): film S ((l.map (S.mirror a z)) ++ l) = reflMark a (Heat.gaugeShift K.B (S.castM a z)) (film S l)*film S l:=by
 unfold film; rw [List.map_append,List.prod_append]; congr 1
 induction l with
 | nil=>
    simp; ext i:1; exact (theta_one _).symm -- check namespace
 | cons x l ih =>
    simp only [List.map_cons,List.prod_cons,S.charge a z x ((subset_union_left).trans ha),ih ((subset_union_right).trans ha)]
    exact funext fun i=>(theta_mul ..).symm
include p
lemma reach(a:Axis)(k:ℕ)(l:List T){B:ℕ}(e:2^k*(B+addgap K)≤ (K.c m).val) (w:rest K m (hopit S l) a B)(q:race S l):∃ y:List T,race S y ∧ y.length=2^k*l.length ∧ ‖R (film S l)‖^(2^k)≤‖R (film S y)‖ ∧ ∀ i,i≠a → ∀d, rest K m (hopit S l) i d → rest K m (hopit S y) i d:=by
 induction k generalizing l B with
 | zero=> exact ⟨l,q,by simp,by simp,fun _ _ _ g=>g⟩
 | succ k ih=>
    have hg:B+addgap K ≤ (K.c m).val:=e.trans' (Nat.le_mul_of_pos_left _ (by positivity))
    obtain ⟨v,f,i,mh⟩:=twice a w hg
    let L:= l.map (S.mirror a v) ++ l
    have hz:=hopit_app S (l.map (S.mirror a v)) l; rw [hops] at hz
    have ht:2^k*((2*B+addgap K)+addgap K)≤ (K.c m).val:=(le_of_eq (by rw [pow_succ]; ring)).trans (show 2^(k+1)*(B+addgap K)≤_ from e)
    obtain ⟨u,B1,L2,M2,X⟩:= ih L ht (hz.symm ▸ i) (S.duos a v l f q)
    refine ⟨u,B1,?_ ,?_,fun j w i v=> X j w i (hz.symm ▸ mh j w i v)⟩
    · rw [L2,pow_succ,List.length_append,List.length_map]; ring
    rw [pow_succ',pow_mul]; exact (pow_le_pow_left₀ (by positivity) ((p a _ _ (S.paid a v l f)).trans_eq (congrArg norm (congrArg R (recount S a v l f).symm))) _).trans M2
--new
include p
lemma collect (s:Finset Axis)(k:ℕ)(l:List T){B:ℕ}(e:2^k*(B+addgap K)≤ (K.c m).val) (w:∀i∈s, rest K m (hopit S l) i B)(q:race S l):∃ y:List T,race S y ∧ y.length=(2^k)^s.card*l.length ∧ ‖R (film S l)‖^((2^k)^s.card)≤‖R (film S y)‖ :=by
 induction s using Finset.induction_on generalizing l with
 | empty=> exact ⟨l,q,by simp,by simp⟩
 | @insert i s a h=>
    obtain ⟨l',b,c,d,f⟩:= reach S R p i k l e (w _ (mem_insert_self ..)) q
    obtain ⟨y,g,H,j⟩:= h l' (fun n u=>f n (fun v=> a (v ▸ u)) B (w n (mem_insert_of_mem u))) b
    rw [card_insert_of_notMem a,pow_succ']; refine ⟨y,g,?_,?_⟩; rw [H,c]; ring; rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) d _).trans j
omit p
lemma golden {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include p
lemma team (l:List T){B:ℕ}(e:B+addgap K≤ (K.c m).val) (w:∀i, rest K m (hopit S l) i B)(q:race S l):∃ (k:ℕ)(y:List T),let t:=(2^k)^4
                         let n':=More (K.c m); t≤ n'.val^4∧n'.val^4 ≤ t*(4*(B+addgap K))^4 ∧ race S y ∧ y.length=t*l.length ∧ ‖R (film S l)‖^t≤‖R (film S y)‖ :=by
 obtain ⟨k,a,f⟩:= golden (x:=(K.c m).val) (show 0 < B+addgap K from Nat.add_pos_right _ addgap_pos) e
 obtain ⟨y,c,d,r⟩:= collect S R p univ k l a (fun a _=>w a) q; have hw:(univ:Finset Axis).card=4:=by simp [Axis]
 refine ⟨k,y,?_,?_,c,by simpa only [hw] using d,by simpa only [hw] using r⟩
 · change _≤ ((K.c m).val * 2)^4; apply pow_le_pow_left'; have h:= a.trans' (Nat.le_mul_of_pos_right (2^k) (Nat.add_pos_right _ (show 0< addgap K from addgap_pos))); omega
 · change ((K.c m).val*2)^4 ≤_; rw [←mul_pow]; apply pow_le_pow_left'; apply (Nat.mul_le_mul_right 2 f).trans; exact le_of_eq (by ring)

-- Pure volume charge => all low layouts. Don't need upper on l unless switching.Here generic Mark size.From θ_ET
lemma till (d:ℝ)(y:0≤d)(t:∀ l:List T, race S l →‖R (film S l)‖≤Real.exp (d*sites (K.c m))) (l:List T){B:ℕ}(e:B+addgap K≤ (K.c m).val) (w:∀i, rest K m (hopit S l) i B)(q:race S l): ‖R (film S l)‖ ≤ Real.exp (d*(4*((B:ℝ)+(addgap K)))^4):=by
 let Z:=4*((B:ℝ)+(addgap K))
 obtain ⟨k,v,h1,h2,h3,h4,h5⟩:= team S R p l e w q
 refine le_of_pow_le_pow_left₀ (by positivity) (Real.exp_pos _).le (h5.trans ((t v h3).trans ?_))
 rw [←Real.exp_nat_mul]; apply Real.exp_monotone
 have hp:sites (K.c m) ≤ (↑((2^k)^4:ℕ):ℝ)*Z^4:=by unfold Z sites; exact_mod_cast h2
 calc _ ≤ d*(_*Z^4):=mul_le_mul_of_nonneg_left hp y
      _ = _:=by unfold Z; ring
#print axioms till
#check theta_one
end Sport
end YM.CF.Pannier.Chancel
end
