import YM.CF.Buffered.Postmen
/-!
# Forest replication. Argue by exchanging the branches of LARGE assigned to the
 first small tile (by parent) with those of SMALL; not asking for agreement on
 parents of anything leaving the specified strip. Hike chosen in its EXACT ordered
 historical branch points.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Mail
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K V C F k v N P L D M B B' l c f: Side} {G:Gauge} {S:Patch} {q w J:ℕ}
section forest
variable (A:Planck C c D) (h:2 ≤ c.val) {ℓ:F.val=C.val*S.L.val}{d:f.val=c.val*S.L.val}
local notation "r" => decreed ℓ
local notation "t" => decreed d
local notation "Lq" => Lace.project (h:=d) (H:=ℓ) A.ratio h
local notation "Y" => Forest (decreed ℓ)
local notation "T" => Forest (decreed d)
def normalize (x:Site f) := ((Lq).R).assemble (pointO A 0 ((Lq).r.parent x),(Lq).r.residue x)
abbrev trim {ℓ:F.val=C.val*S.L.val}{d:f.val=c.val*S.L.val} (A:Planck C c D)(h:2≤c.val): Planck F f D:=⟨by rw [d,ℓ,A.ratio]; ring⟩
local notation "tN" => trim (ℓ:=ℓ) (d:=d) A h
local notation "nrm" => normalize (ℓ:=ℓ) (d:=d) A h
lemma sting (x:Site f): (slump tN).cut (nrm x)=x:=by
 change (Lq).high.cut ((Lq).R.assemble _)=_; rw [Lace.regions,show (Lq).low.cut _=_ from stepR A 0 _]; exact Ratio.unpack_at ..
lemma certain (x:Site f): (r).parent (nrm x)∈blockF A 0:=by rw [normalize]; apply (atF A _).2; rw [show (r).parent _= _ from Ratio.assemble_parent (r) (pointO A 0 ((t).parent x),(t).residue x)]; exact ledge_of ..
lemma ambitious (x:Site F) (p:(r).parent x∈blockF A 0): nrm ((slump tN).cut x)=x:=by
 change normalize A h ((Lq).high.cut x)=x; unfold normalize; rw [Lace.position,Lace.room,show (pointO A 0) ((Lq).low.cut _)=_ from restep A 0 p]; exact Ratio.unpack_at ..

def chive (V: Forest (decreed ℓ)): Forest (decreed d) where
 up i:= V.up (nrm i)
 height i:= V.height (nrm i)
 bound i:= V.bound _
 rise i p:=by
    let j:= nrm i; let u:=V.up j; have he: (Lq).high.cut j=i:=sting A h i; have hp: leaf (r) j:=((Lq).fork j).mpr (he.symm ▸ p); let z:= j+ u.vec; have hz: (Lq).high.cut z=i+u.vec:=by unfold z; rw [Macrame.Window.uniform,he];
    change V.height (nrm (i+u.vec))<_; rw [← hz,show nrm ((Lq).high.cut z)=z from ambitious A h _ ((V.stays j hp).symm ▸ certain A h i)]; exact V.rise _ hp
 stays i p:=by
    let j:= nrm i; have he : (Lq).high.cut j=i:=sting A h i; have hx:=((Lq).strolls j (V.up j)).1 (V.stays j (((Lq).fork j).mpr (he.symm ▸ p))); rw [he] at hx; exact hx

abbrev sequel (W: Forest (decreed d)) := (Lq).repeater W
private lemma ch_ext {U:Ratio c f} (A B:Forest U) (x:A.up=B.up) (p:A.height=B.height): A=B:=by cases A; cases B; congr
lemma chive_same (W:Y) (X:T) : chive A h (stitchF (blockF A 0) (sequel (ℓ:=ℓ) A h X) W)=X:=by
 apply ch_ext <;> funext j <;> unfold chive stitchF <;> dsimp only <;> rw [if_pos (certain A h j)]
 · exact congrArg X.up (sting A h j)
 exact congrArg X.height (sting A h j)
lemma sequel_back (W:Y)(X:T): stitchF (blockF A 0) (sequel A h (chive (d:=d) A h W)) (stitchF (blockF A 0) (sequel (ℓ:=ℓ) A h X) W)=W:=by
 apply ch_ext <;> funext i <;> unfold stitchF <;> dsimp only <;> split_ifs with u
 all_goals first| rfl | exact congrArg W.height (ambitious A h i u) | exact congrArg W.up (ambitious A h i u)

def exchange : Equiv.Perm (Forest (decreed ℓ) × Forest (decreed d)) :=
 let f:= fun v:Y×T=> (stitchF (blockF A 0) (sequel A h v.2) v.1, chive A h v.1)
 let H_: Involutive f:=fun v=> Prod.ext (sequel_back A h v.1 v.2) (chive_same A h v.1 v.2)
 ⟨f,f,H_,H_⟩
variable {U:Type*}[NormedRing U][NormedAlgebra ℝ U]
lemma reduces (R: Y→ U) (X:T→U) (u:∀ i j, sameForest (blockF A 0) i j→ R i= R j)(v:∀ j, R (sequel A h j)=X j): avgF R=avgF X:=by
 letI:Nonempty (Forest (decreed ℓ)):= Tree.select _ S.odd_side; letI:Nonempty (Forest (decreed d)):= Tree.select _ S.odd_side
 let s:= (Fintype.card (Forest (decreed d)):ℝ); let m:=(Fintype.card (Forest (decreed ℓ)):ℝ)
 have hs:s≠0:=by unfold s; positivity
 have hm:m≠0:=by unfold m; positivity
 let F(v:Y×T):=R v.1; let a:= ∑ i,R i; let b:= ∑ i,X i
 have he : s • a=m • b:=by
    have h(z:Y×T): F (exchange A h z)=X z.2:= (u _ _ (stitch_self (blockF A 0) (sequel (ℓ:=ℓ) A h z.2) z.1)).trans (v z.2)
    have ht: (∑ z:Y×T,F z)=∑ z:Y×T,X z.2:=by rw [←Equiv.sum_comp (exchange (ℓ:=ℓ) (d:=d) A ‹2 ≤ c.val›)]; exact sum_congr rfl fun z _=> h z
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at ht; simpa only [s,a,F,m,b,smul_sum,sum_const,card_univ,Nat.cast_smul_eq_nsmul] using ht -- check m • sum b issue
 change m⁻¹ • a=s⁻¹ • b; nth_rw 1 [← inv_smul_smul₀ hs a,he, smul_comm,inv_smul_smul₀ hm b] -- tune
lemma climb (X:T)(i: Site F): (sequel (ℓ:=ℓ) A h X).hike i=X.hike ((Lq).high.cut i):=by
 let W:= (sequel (ℓ:=ℓ) A h X); induction i using Forest.hike.induct W with
 | case1 i g ih=>
    have he:= ((Lq).fork i).1 g; change W.hike i=_; conv_lhs=>rw [Forest.hike,dif_pos g]
    conv_rhs=> rw [Forest.hike,dif_pos he];
    rw [ih,(Lq).high.uniform]; rfl
 | case2 i p=> rw [Forest.hike,dif_neg p,Forest.hike,dif_neg (fun g=> p (((Lq).fork i).2 g))]
end forest
-- physical forest G ratios specified by sizes
variable (A:Planck N P D)(A':Planck F f D)(a:2 ≤ (More P).val){ℓ:F.val=N.val*S.L.val}{d:f.val=P.val*S.L.val}
abbrev ga {P L K:Side}(d:P.val=L.val*K.val): (More P).val=(More L).val*K.val :=by rw [natM,natM,d]; ring
variable (q:Chi)(u:ℝ) (V: Forest (ratio (decreed d)))
local notation "Lq" => Lace.project (P:=S) (h:=ga (K:=S.L) d) (H:=ga (K:=S.L) ℓ) (Planck.ratio (gauge_plan A)) a -- Patch meta unspecified? adjust
include S
lemma stream (Y:Pane f)(K:Pane P) : seine (decreed ℓ) ((Lq).repeater V) q u (weave (gauge_plan A') (show Config SU.group _ from Y)) (weave (gauge_plan A) (show Config SU.group _ from K))= weave (gauge_plan A') (show Config SU.group _ from seine (decreed d) V q u Y K) :=by
 let H:= Lq; let T:=H.high; let r':=ratio (decreed ℓ); let x:=r'.count; let F':Forest (ratio (decreed ℓ)):=(H).repeater V
 have he(i:Seat F): F'.foldAt (T.links Y) i= V.foldAt Y (T.cut i):=by unfold Forest.foldAt; rw [show F'.hike _= V.hike (T.cut i) from climb (ℓ:=ga (K:=S.L) ℓ) (d:=ga (K:=S.L) d) (gauge_plan A) a V i,T.traveller]
 funext ⟨i,j⟩; have hx:= Lace.Fitted.replicate (G:=SU.group) H K; change Lattice.gauge (F'.foldAt (T.links Y))⁻¹ (portU (decreed ℓ) F' q u (T.links Y) (H.low.links K)) (i,j)=Lattice.gauge (V.foldAt Y)⁻¹ (portU (decreed d) V q u Y K) (T.cut i,j)
 simp only [Lattice.gauge, portU, Pi.inv_apply];  rw [he i,he (i+step j),show Precision.replica (ratio (decreed ℓ)) (H.low.links (show Config SU.group _ from K))= _ from hx,T.step_up]; rfl -- tune
end YM.CF.Buffered.Mail
#print axioms YM.CF.Buffered.Mail.chive_same
#print axioms YM.CF.Buffered.Mail.stream
