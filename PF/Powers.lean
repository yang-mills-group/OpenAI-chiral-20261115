import PF.Slip
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce.WickLabels
open Hake Hive Sault Pastry Set
variable {N:Type}[LinearOrder N][Fintype N]
namespace Bill
open Branch Material
variable {D X : Type}[TopologicalSpace D][Fintype X][DecidableEq X]{H:Host X N D}
variable {ν Δ : D→ℝ}{S T pad:Seal X}{a h c B y:ℝ}
-- Pay across all labels connected to starter pad, even when extension out of declared ledger support due to shots and dgU. physical pencils in linked powers start over each e's pad. Signed actor not assuming any commutation beyond particular formulas.
def Docket (H:Host X N D)(ν:D→ℝ)(pad:Seal X)(a c:ℝ)(f:D→FC N)(B:ℝ):Prop:=
    ∃ (I:Type)(_ :Fintype I)(S:I→Seal X)(L:I→List (Oboe N))(G:I→D→ℂ)(Q:I→ℝ),
      (∀ i, Bill.Tag H ν pad (S i) (G i) (Q i)) ∧ (∀ i:I,Q i≠0→∀ j ∈ L i,H.port j.2∈ S i) ∧
      (∑ i,rent a (S i\pad)*c^(L i).length*Q i) ≤ B ∧ ∀ x,f x=∑ i,G i x • Hive.drum (L i)
variable {C F: D→ FC N}
lemma Bill.Tag.zero {K:D→ℂ}(p:Bill.Tag H ν pad S K c)(h:c=0) (x:D):K x=0:=norm_le_zero_iff.mp ((p.price x).trans_eq (by rw [h,zero_mul]))
private lemma Tag_prod {K Y:D→ℂ}(p:Bill.Tag H ν pad S K c)(v:Bill.Tag H Δ T T Y h)(e:c≠0→h≠0→ (S∩T).Nonempty): Bill.Tag H (ν*Δ) pad (S∪T) (K*Y) (c*h):= by
 refine ⟨mul_nonneg p.pos v.pos,fun x=>?_,p.cont.mul v.cont,fun i j w=> congrArg₂ (·*·) (p.portal _ _ (H.relay Finset.subset_union_left w)) (v.portal _ _ (H.relay subset_union_right w)), fun i=>?_⟩
 · rw [Pi.mul_apply,norm_mul,Pi.mul_apply]; exact (mul_le_mul (p.price _) (v.price _) (norm_nonneg _) ((norm_nonneg _).trans (p.price _))).trans_eq (by ring)
 obtain ⟨hp,hk⟩:= p.resource (left_ne_zero_of_mul i); obtain ⟨_,hg⟩:=v.resource (right_ne_zero_of_mul i); obtain ⟨y,hx⟩:= e (left_ne_zero_of_mul i) (right_ne_zero_of_mul i); exact ⟨hp.trans Finset.subset_union_left,hk.unite hg (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2⟩
lemma Tag_mult {S Z:Seal X}{K Y:D→ℂ}(p:Bill.Tag H ν pad S K c)(v:Bill.Tag H Δ pad Z Y h)(w:pad.Nonempty): Bill.Tag H (ν*Δ) pad (S∪Z) (K*Y) (c*h) := Tag_prod p {v with resource:=fun h=>⟨Finset.Subset.refl _,(v.resource h).2⟩} (fun hc hy=> by obtain ⟨t,g⟩:=w; exact ⟨t,mem_inter.mpr ⟨(p.resource hc).1 g,(v.resource hy).1 g⟩⟩)
namespace Docket
lemma dormant : Docket H ν pad a c 0 0 := ⟨Empty,inferInstance,isEmptyElim,isEmptyElim,isEmptyElim,isEmptyElim,isEmptyElim,isEmptyElim,by simp,by simp⟩
lemma single {g:D→ℂ}(l:List (Oboe N))(h:Bill.Tag H ν pad S g B)(p:B≠0 →∀ i∈l,H.port i.2∈ S): Docket H ν pad a c (fun x=> g x • Hive.drum l) (rent a (S\pad)*c^l.length*B):= ⟨Unit,inferInstance,fun _=>S,fun _=>l,fun _=>g,fun _=>B,fun _=>h,fun _=>p,by simp,by simp⟩
lemma one (p:Grove H.space pad) : Docket H (fun _=>1) pad a c (fun _=> (1:FC N)) 1:=by
 have h : Bill.Tag H (fun _=>1) pad pad (fun _=>1) 1:=⟨zero_le_one,fun i=> by simp,continuous_const,fun _ _ _=>rfl,fun i=>⟨Finset.Subset.refl _,p⟩⟩
 convert single [] h (fun _ _ h=>by simp at h) (a:=a) (c:=c) using 1; funext x; change _=(1:ℂ) • (1:FC N); rw [one_smul]; simp [Branch.rent]
lemma up (p:Docket H ν pad a c F y)(u:y≤B):Docket H ν pad a c F B:=by obtain ⟨I,i,S,L,F,Q,T,p,V,U⟩:=p; exact ⟨I,i,S,L,F,Q,T,p,V.trans u,U⟩
lemma reduce (p:Docket H ν pad a c F y)(t:0≤h)(u:h≤c):Docket H ν pad a h F y:=by
 obtain ⟨I,i,S,L,F,Q,T,p,V,U⟩:=p; exact ⟨I,i,S,L,F,Q,T,p,(sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t u _) (rent_pos ..).le) (T i).pos)).trans V,U⟩
lemma scale (p:Docket H ν pad a c F B)(z:ℂ):Docket H ν pad a c (fun x=>z • F x) (‖z‖*B):=by
 obtain ⟨I,i,S,L,Y,Q,T,h,V,U⟩:=p
 refine ⟨I,i,S,L,fun i x=>z*Y i x,fun i=>‖z‖*Q i,fun i=>⟨mul_nonneg (norm_nonneg _) (T i).pos,fun x=>?_,continuous_const.mul (T i).cont,fun x y v=>congrArg _ ((T i).portal x y v),fun h=> (T i).resource (right_ne_zero_of_mul h)⟩,fun i v=> h i (right_ne_zero_of_mul v), ?_,?_⟩
 · rw [norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left ((T i).price _) (norm_nonneg _)
 · apply le_trans _ (mul_le_mul_of_nonneg_left V (norm_nonneg z)); rw [mul_sum]; exact le_of_eq (sum_congr rfl fun i _=>by dsimp only; ring)
 intro x; change z • F x=_; rw [U,Finset.smul_sum]; exact sum_congr rfl fun i _=> by simp [smul_smul]
lemma nn (p:Docket H ν pad a c F B)(e:0≤c):0 ≤ B:=by obtain ⟨I,i,S,L,G,Q,T,_,A,B⟩:=p; exact (sum_nonneg fun i (_:i∈(univ:Finset I))=> by have hv:0≤Q i:=(T i).pos; have hp:=Branch.rent_pos a ((S i)\pad); exact mul_nonneg (mul_nonneg hp.le (pow_nonneg e (L i).length)) hv).trans A
lemma plus (p:Docket H ν pad a c F B)(v:Docket H ν pad a c C y):Docket H ν pad a c (fun x=> F x+C x) (B+y) :=by
 obtain ⟨I,i,S,L,F0,Ft,Fh,hk,H0,B0⟩:=p; obtain ⟨J,j,T,R,Y,Yt,Yg,hr,M0,M⟩:=v
 refine ⟨I⊕J,inferInstance,Sum.elim S T, Sum.elim L R, Sum.elim F0 Y,Sum.elim Ft Yt,(fun i=>by cases i; apply Fh; apply Yg),(fun i=>by cases i; apply hk; apply hr), ?_,?_⟩
 · rw [Fintype.sum_sum_type]; exact add_le_add H0 M0
 intro x; rw [Fintype.sum_sum_type]; exact congrArg₂ (·+·) (B0 _) (M _)
lemma summers {Y:Type}(L:Finset Y)(f:Y→D→FC N)(B:Y→ℝ)(h:∀ i∈L,Docket H ν pad a c (f i) (B i)): Docket H ν pad a c (fun x=>∑ i∈L,f i x) (∑ i∈L,B i):=by
 classical
 induction L using Finset.induction_on with|empty=>simp_rw [Finset.sum_empty]; exact dormant|insert a L hl ih=> simp_rw [sum_insert hl]; exact (h _ (mem_insert_self ..)).plus (ih fun i p=>h i (mem_insert_of_mem p))
lemma product (p:Docket H ν pad a c F B)(v:Docket H Δ pad a c C y)(w:pad.Nonempty)(e:0≤c)(h:0≤a): Docket H (ν*Δ) pad a c (fun x=> F x*C x) (B*y):=by
 have hp:= p.nn e
 obtain ⟨I,i,S,W,L,Np,Yp,Lp,K,A⟩:=p; obtain ⟨J,j,T,Qg,Q,Kq,Yq,Lq,Wq,Aq⟩:=v
 let M (i:I×J):= S i.1∪ T i.2; let R(i:I×J):=W i.1++Qg i.2; let m(i:I×J):= Np i.1*Kq i.2
 refine ⟨I×J,inferInstance,M,R,fun i=> L i.1 * Q i.2,m,fun i=> Tag_mult (Yp i.1) (Yq i.2) w,fun i h j hj=> Finset.mem_union.mpr ((List.mem_append.mp hj).imp (Lp _ (left_ne_zero_of_mul h) _) (Lq _ (right_ne_zero_of_mul h) _)), ?_,?_⟩
 · refine le_trans ?_ (mul_le_mul K Wq (sum_nonneg fun i _=>mul_nonneg (mul_nonneg (rent_pos ..).le (pow_nonneg e _)) (Yq i).pos) hp)
   rw [Fintype.sum_prod_type, sum_mul]; simp_rw [mul_sum]; apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
   unfold M R m; rw [Finset.union_sdiff_distrib,List.length_append,pow_add]; have hx:= (Yp i).pos; have hv:0≤ Kq j:=(Yq j).pos
   refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (rent_join ((S i)\pad) ((T j)\pad) h) (by positivity)) (mul_nonneg hx hv)).trans_eq ?_; dsimp only; ring
 intro x; change F x*C x=_; rw [A,Aq,sum_mul]; simp_rw [mul_sum]; rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; unfold R Hive.drum; simp [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,mul_comm]
lemma cashier {P:D→Op N}{v:D→Wave N}{k:ℝ} (h:∀ x,IsStarProjection (P x))(p:∀ x,Fock.Sea (P x) (v x))(Sg:Shot H (fun _=>1) ∅ a k P)(g:0 ≤ a)(t:Docket H ν pad a (Real.exp a+k) F B)(b:pad.Nonempty) : Cred H ν pad a (fun x=> inner ℂ (v x) (acts (F x) (v x))) B:=by
 let c:=Real.exp a+k; have hc:1≤c:=(Real.one_le_exp g).trans (le_add_of_nonneg_right Sg.cost_pos)
 obtain ⟨I,i,S,L,Xg,T,p0,p1,ℓ,V⟩:=t
 let f(i)(x:D):= Xg i x * inner ℂ (v x) (acts (Hive.drum (L i)) (v x)); let G(i):=Branch.rent a (S i \ pad)*c^(L i).length*T i
 have hE (i:I): Cred H ν pad a (f i) (G i):=by
   let P0:=p0 i
   by_cases hx:T i=0
   · convert Bill.dormant (a:=a) (H:=H) (pad:=pad) (ν:=ν) using 1
     · funext; simp [f,Bill.Tag.zero P0 hx]; -- lemma name
     simp [G,hx]
   obtain ⟨u,q⟩:= (p0 i).resource hx; have hv:= supplied h p Sg g q (b.mono u) (L i) (p1 i hx)
   obtain ⟨χ,o,Y,W,TW,K,hs,he⟩:=hv
   refine ⟨χ,o,Y,fun j x=> Xg i x*W j x,fun j=>T i*TW j,fun j=>?_,?_,?_⟩
   · by_cases hp:TW j=0
     · have hh(x):W j x=0:=Bill.Tag.zero (K j) hp _
       simp only [hh,mul_zero,hp]; exact ⟨le_rfl,fun x=>by simp,continuous_const,fun _ _ _=>rfl,by simp⟩
     have hh:=((K j).resource hp).1
     have hg:=Tag_prod P0 { K j with resource:=fun _=>⟨Finset.Subset.refl _,((K j).resource hp).2⟩} (fun _ _=> let ⟨i,t⟩:=b.mono u; ⟨i,mem_inter.mpr ⟨t,hh t⟩⟩)
     convert hg using 1; ext; simp; exact (Finset.union_eq_right.mpr hh).symm; rfl
   · unfold G; rw [mul_right_comm]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hs (mul_nonneg (rent_pos a (S i \pad)).le P0.pos)); rw [mul_sum]; apply sum_le_sum; intro j _
     by_cases hp:TW j=0; simp [hp]
     have hh:= ((K j).resource hp).1
     have hg:(Y j)\ pad= (Y j \ S i)∪ (S i \ pad):=by ext z; simp; constructor <;> grind
     apply le_trans (mul_le_mul_of_nonneg_right (show rent a ((Y j)\pad) ≤ _ from Eq.trans_le (congrArg (Branch.rent a) hg) (rent_join (Y j\ S i) (S i\ pad) g)) (mul_nonneg P0.pos (K j).pos)); apply Eq.le; ring
   intro x; unfold E Fock.chime at he; unfold f -- f not he
   have ht: inner ℂ (v x) (acts (Hive.drum (L i)) (v x)) = _:=he x; rw [ht,mul_sum]
 have Q(t:Finset I):Cred H ν pad a (fun x=> ∑ i∈t,f i x) (∑ i∈t,G i):=by induction t using Finset.induction_on with|empty=> exact Bill.dormant|insert i s g ih=> simp_rw [sum_insert g]; exact (hE i).plus ih
 convert (Q univ).up ℓ using 1; funext x; rw [V,act_sum,inner_sum]; exact sum_congr rfl fun i _=>by rw [act_smul,inner_smul_right]
-- package scalar powers before grouping exp sum. shrink ambient triangle via δ ≤ r independently of i.
lemma blur(p:Docket H ν pad a c F B){w:ℝ}(e:0≤w)(t:∀ x,ν x≤w*Δ x):Docket H Δ pad a c F (w*B):=by
 obtain ⟨I,k,S,L,Y,T,v,h,Z,A⟩:=p; refine ⟨I,k,S,L,Y,fun i=>w*T i,fun i=>{v i with pos:=mul_nonneg e (v i).pos,price:=fun t'=> ((v i).price _).trans ((mul_le_mul_of_nonneg_left (t t') (v i).pos).trans_eq (by ring)),resource:=fun q=>(v i).resource (right_ne_zero_of_mul q)},fun i g=>h i (right_ne_zero_of_mul g),?_,A⟩
 apply le_trans ?_ (mul_le_mul_of_nonneg_left Z e); rw [mul_sum]; exact le_of_eq (sum_congr rfl fun i _=>by dsimp only; ring)
lemma powers (p:Docket H ν pad a c F B)(e:pad.Nonempty)(hp:0 ≤ a)(hv:0 ≤ c)(hx:∀ x,0 ≤ ν x){w:ℝ}(hy:0≤w)(ht:∀ x,ν x≤w)(n:ℕ):Docket H ν pad a c (fun x=>F x^(n+1)) (B*(w*B)^n):=by
 induction n with|zero=> simpa using p|succ n ih=>
  have hk:= (ih.product p e hv hp).blur hy (Δ:=ν) (fun x=>mul_le_mul_of_nonneg_right (ht x) (hx x)); rw [pow_succ (w*_ ),show B*((w*B)^n*(w*B))= w*(B*(w*B)^n*B) by ring]; simp_rw [pow_succ _ (n+1)]; exact hk
end Docket
-- Collapse anchored scalar family, preserving rate even for converging sums.
variable {f:D→ℂ}{k:ℝ}
namespace Cred
lemma bound (p:Cred H ν pad a f k)(e:0≤a)(u:∀ x,0≤ν x)(x:D): ‖f x‖ ≤ k*ν x:=by
 obtain ⟨I,i,S,F,K,V,Z,R⟩:=p; rw [R]; apply (norm_sum_le ..).trans; refine le_trans ?_ (mul_le_mul_of_nonneg_right Z (u x)); rw [sum_mul]; exact sum_le_sum fun i _=> ((V i).price x).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (V i).pos (rent_one e _)) (u x))
-- `compress` with same I=Seal.
lemma compress (p:Cred H ν pad a f k):∃ (Y:Seal X→D→ℂ)(T:Seal X→ℝ), (∀ S,Bill.Tag H ν pad S (Y S) (T S)) ∧ (∑ S:Seal X,rent a (S\pad)*T S) ≤ k ∧ ∀ x,f x=∑ S,Y S x :=by
 obtain ⟨I,i,T,F,W,J,G,E⟩:=p
 let S(A:Seal X):=dest T A
 let f(A:Seal X)(v:D):=∑ i∈S A,F i v; let t(A:Seal X):=∑ i∈S A,W i
 refine ⟨f,t,fun A=>⟨sum_nonneg (fun i _=>(J i).pos),fun x=>?_,continuous_finsetSum _ (fun i _=>(J i).cont),fun x y h=>?_ ,fun h=>?_⟩,?_ ,fun x=> (E _).trans (Branch.lump T _)⟩
 · unfold f t; rw [sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun i _=>(J i).price _)
 · exact sum_congr rfl fun i u=>(J i).portal x y ((mem_filter.mp u).2.symm ▸ h)
 · by_contra t; exact h (sum_eq_zero fun i u=> Classical.not_not.mp fun v=> t ((mem_filter.mp u).2 ▸ (J i).resource v))
 unfold t; simp only [mul_sum]; apply le_trans _ G; rw [Branch.lump T (fun i=>Branch.rent a (T i\ pad)*W i)]; exact Eq.le (sum_congr rfl fun i _=> sum_congr rfl fun j u=> by rw [show T j=i from (mem_filter.mp u).2])
-- note `f` binder missing!
lemma infinite {u:ℕ→ℝ}{g:ℕ→D→ℂ}(p:∀ i,Cred H ν pad a (g i) (u i))(o:Summable u)(ha:0≤ a)(h: ℝ)(hp:0≤h)(hv:∀ x,0≤ν x ∧ ν x ≤ h): Cred H ν pad a (fun x=>∑' i,g i x) (∑' i,u i) := by
 choose F T L W V using fun i=>compress (p i)
 have hm i := (p i).nn
 have hx (i S): T i S ≤ u i := (le_mul_of_one_le_left (L i S).pos (rent_one ha _)).trans ((single_le_sum (f:=fun S=>Branch.rent a (S\pad)*T i S) (fun S _=>mul_nonneg (rent_pos ..).le (L i S).pos) (mem_univ _)).trans (W i))
 have hT(S):Summable (fun i=>T i S):= o.of_nonneg_of_le (fun i=>(L i S).pos) (fun i=>hx i S)
 have hL S x:Summable (fun i=> ‖F i S x‖):= ((hT S).mul_right (ν x)).of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> (L i S).price x)
 let y (S:Seal X)(x:D):= ∑' i,F i S x; let z (S:Seal X):=∑' i,T i S
 refine ⟨Seal X,inferInstance,id,y,z,fun s=>⟨tsum_nonneg (fun i=> (L i s).pos),fun i=>?_,continuous_tsum (fun i=>(L i s).cont) ((hT s).mul_right h) (fun i x=> ((L i s).price x).trans (mul_le_mul_of_nonneg_left (hv x).2 (L i s).pos)), fun x y t=> tsum_congr fun i=>(L i s).portal x y t,fun i=>?_⟩,?_,?_⟩
 · exact (norm_tsum_le_tsum_norm (hL s i)).trans (((hL s i).tsum_le_tsum (fun j=> (L j s).price i) ((hT s).mul_right _)).trans_eq ((hT s).tsum_mul_right _))
 · by_contra h; have hc(o:ℕ):T o s=0:= Classical.not_not.mp fun hf=> h ((L o s).resource hf); apply i; unfold z; simp_rw [hc]; simp
 · have he(S:Seal X):Summable (fun i=>Branch.rent a (S\pad)*T i S):= (hT S).mul_left _
   have hh:Summable fun i=>∑ S:Seal X,Branch.rent a (S\pad)*T i S:=summable_sum fun S _=>he S
   unfold z; simp_rw [id_eq,←(hT _).tsum_mul_left]; rw [← Summable.tsum_finsetSum (f:=fun S i=> Branch.rent a (S\pad)*T i S) (hf:=fun S _=>he S)]; exact hh.tsum_le_tsum W o
 intro x; simp only [V]; exact Summable.tsum_finsetSum (f:=fun S i=>F i S x) (fun S _=> (hL _ _).of_norm)

end Cred
end Bill
end PureForce.WickLabels
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
