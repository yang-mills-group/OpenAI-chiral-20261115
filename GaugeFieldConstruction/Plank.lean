import GaugeFieldConstruction.Plaid
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
open TableF.Lenten.Loden Haro Tap Hove Moto
attribute [local instance] opCStarAlgebra
abbrev hart_X(n:Side):Type:=Pane n→ Op (Single n)
variable {h v:ℝ}
-- h weight. bool=false means remove, left spin matrix stored transposed and negated.
def plac (F:hart_X n)(b: Bool): Paper n
| none=>0
| some (x,i,j)=>if x=b then fun A=> if b then F A i j else -(F A j i) else 0
lemma plac_ℓ (F:hart_X n)(b:Bool) (A:Pane n): AlphaY (plac F b) A= pulseH (F A):=by
 rw [AlphaY,Fintype.sum_option,show plac F b none A=0 from rfl,zero_smul, zero_add,Fintype.sum_prod_type, sum_eq_single b]
 · rw [Fintype.sum_prod_type]; apply Subtype.ext; let L:Cipher n →+ FC (LeanV (Single n)):=⟨⟨Subtype.val,rfl⟩,fun _ _=>rfl⟩; change L (∑ i:Single n,∑ j:Single n,plac F b (some (b,i,j)) A • civic_K _)=faceD true false (F A); simp_rw [map_sum L]; unfold faceD twinD
   cases b; swap; · unfold plac; simp only [ite_true]; rfl
   rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; change (plac F false (some (false,j,i)) A) • (put (false,j)*put (true,i))= _; unfold plac; simp only [ite_true,Bool.false_eq_true,ite_false, ite_self]; rw [eq_neg_of_add_eq_zero_left (put_put ..),neg_smul,smul_neg, neg_neg]
 · intro c _ p; exact sum_eq_zero fun ⟨j,k⟩ _=>by rw [show plac F b _ A=0 from (show plac F b (some (c,j,k)) A=0 from by simp [plac,p]),zero_smul]
 simp
-- sums
lemma port_pack (F:hart_X n)(b:Bool)(H:∀ (A:Pane n)(g:Agora n), twist (tradew n g) (F A)=F (GA g A)): portable (plac F b):=by
 intro A g; let U:=tradew n g; let Z:=GA g A; let X:=plac F b; let B:= steerZ U false false (αLines X A); funext j; rcases j with _|⟨i,l,k⟩; · rfl
 let v(i:Bool)(A:Pane n):= if i=b then if b then F A else -(F A)ᵀ else 0
 have he(i A):sealC (αLines X A) i=v i A:=by ext x y; cases i <;>cases b <;> simp only [X,αLines,sealC,plac,v,ite_false,ite_true,Bool.false_eq_true,Bool.true_eq] <;> rfl -- tune split
 have hp(t:Bool):sealC (αLines X Z) t= sealC B t:=by
    have hh:=seal_D U false false (αLines X A) t; rw [Bool.xor_false,Bool.xor_false,he,show ∀ A:Op (Single n),windX false A=A from fun _=>rfl] at hh; rw [he,show sealC B t=_ from hh]; by_cases q:t=b; swap
    · simp [v,q]
    subst t; 
    have hH:F Z=U.val*F A*star U.val:=(H _ _).symm.trans (twist_formula ..)
    unfold v; rw [if_pos rfl, if_pos rfl]
    cases b
    · simp only [Bool.false_eq_true, ite_false,hH]; change -(U.val*F A*star U.val)ᵀ=cc U.val * (- (F A)ᵀ) * U.valᵀ; rw [Matrix.transpose_mul,Matrix.transpose_mul,←mul_assoc,mul_neg,neg_mul]; rfl
    · change F (GA g A) = U.val* F A*(cc U.val)ᵀ; exact hH
 exact Matrix.ext_iff.mpr (hp i) l k
lemma oneCκ (A B:ChartP n) (U:UNI (Single n))(p t: Bool): steerZ U p t (A+B)=steerZ U p t A + steerZ U p t B:=by
 funext i; rw [Pi.add_apply]; simp only [stripeQ,←sum_add_distrib]; apply sum_congr rfl; intro k _; cases p <;>cases t <;> simp [cSignX,mul_add]
lemma scaleCκ (A:ChartP n)(U:UNI (Single n))(p t:Bool)(x:ℂ): steerZ U p t (x • A)=cSignX (p.xor t) x • steerZ U p t A:=by
 funext i; simp only [stripeQ, Pi.smul_apply,smul_eq_mul,mul_sum]; apply sum_congr rfl; intro j _; cases p<;> cases t<;>simp [cSignX, mul_left_comm]
lemma port_add {A B: Paper n}(u:portable A)(v:portable B): portable (A+B):=by
 intro X g; change αLines A _ + αLines B _=steerZ _ _ _ (αLines A _ + αLines B _); rw [u X g,v X g,oneCκ] -- tune
lemma port_m {A:Paper n}(u:portable A)(x:ℂ):portable (x • A):=by intro X g; change x • αLines A _ = steerZ _ _ _ (x • αLines A _); rw [u X g,scaleCκ]; rfl
lemma port_Z : portable (0:Paper n):=by intro X g; funext i; rw [stripeQ]; simp [αLines,cSignX]
lemma port_sum {I:Type*}(S:Finset I)(F:I→Paper n)(w:∀ i∈S,portable (F i)): portable (∑ i∈S,F i):=by
 induction S using Finset.induction_on with|empty=>rw [sum_empty]; exact port_Z|@insert i S t ih=>rw [sum_insert t]; exact port_add (w i (mem_insert_self ..)) (ih fun j p=>w j (mem_insert_of_mem p))
-- packaging plac Cost
lemma haw_s(f:Lit n)(t:Haw p o (Pax o) f v):Micro p (Pach o) f v:=⟨(t.rends 1 (ping_f p _)).grade,Env.compact t.swift,t.live,milk_H o t⟩ -- tune
lemma kinViewP (A: Pane n→Pal)(k:lotV) (s:∀ V: Pane n,∀ g:Agora n,A (GA g V)=KinX (g o)* A V*star (KinX (g o))) (b:Bool): portable (plac (beamer o k A h) b):= port_pack _ _ (mark_kin (A:=A) _ _ s)
abbrev edgeB(b:Bool)(x y:Site n)(V: vendors): Wa n:= some (if b then (true,Moto.hailV x V.1,Moto.hailV y V.2) else (false,Moto.hailV y V.2,Moto.hailV x V.1))
lemma edge_inj(b:Bool)(x y:Site n):Injective (edgeB b x y):=by
 intro i j e; let F: Pairs n→ vendors:= fun ⟨p,i,j⟩=> if p then (portB i,portB j) else (portB j,portB i); cases b
 · exact congrArg F (Option.some.inj e)
 exact congrArg F (Option.some.inj e)
lemma transitA(b:Bool)(x y:Site n)(u: node x∈ Pach o)(t:node y∈ Pach o)(F:Pane n→Pal)(v': Haw p o (Pax o) F v):TrackD p (Pach o) h (plac (fun A=> seed_k x y (F A)) b) (h^2*(∑ i:vendors, crustP i*v)):=by
 let Q(i):= edgeB b x y i; let P:= plac (fun A:Pane n=> seed_k x y (F A)) b; let W(i:vendors):= P (Q i); let Z:= (univ:Finset vendors).image Q; have hv:Injective Q:=edge_inj ..
 have hx(i):DomainP (Pach o) (Q i):=by cases b; exact ⟨t,u⟩; exact ⟨u,t⟩
 have hp(i:vendors): TrackD p (Pach o) h (isolate (Q i) (W i)) (h^2*(crustP i*v)):=by
    have hA(a:ℂ)(q:‖a‖=1): Micro p (Pach o) (fun U=> a* F U i.1 i.2) (crustP i*v):= haw_s o _ ((Cargo x y F v p o v' a i.1 i.2) |> fun t=> Housing.gum t (by rw [q,one_mul])) -- rewrite below
    let X:=(if b then 1 else -1:ℂ); have he: W i=fun U=> X* F U i.1 i.2:=by
       unfold W Q P; funext u; cases b <;> simp [X,plac,edgeB,Moto.hailV,Hove.portB,seed_k]
    rw [show h^2=papW n h (Q i) from rfl]; apply moorage _ (hx i) _; rw [he]; exact hA X (by cases b <;> simp [X])
 have he:P=∑ i:vendors,isolate (Q i) (W i):=by
    funext j; rw [Finset.sum_apply]; by_cases a:j∈ Z; · obtain ⟨i,u,rfl⟩:= Finset.mem_image.mp a; simp only [isolate,Pi.single_apply,hv.eq_iff]; simp [W]
    rw [sum_eq_zero fun i _=> by rw [isolate,Pi.single_apply, if_neg (show j≠ Q i from fun e=> a (e.symm ▸ mem_image.mpr ⟨i,mem_univ _,rfl⟩))]]
    cases j with
    | none=> rfl
    | some j=>
       rcases j with ⟨c,i,j⟩; by_cases v:c=b; swap; · simp [P,plac,v]
       subst c; cases b
       · have he: ¬ (x=j.1.1∧ y=i.1.1):= fun e=> a (mem_image.mpr ⟨(portB j,portB i),mem_univ _,by unfold Q; rw [e.1,e.2]; rfl⟩); funext i'; simp [P,plac,seed_k,he]
       have he: ¬ (x=i.1.1∧ y=j.1.1):= fun e=> a (mem_image.mpr ⟨(portB i,portB j),mem_univ _,by unfold Q; rw [e.1,e.2]; rfl⟩); funext i'; simp [P,plac,seed_k,he] -- tune
 change TrackD _ _ _ P _; rw [he,Finset.mul_sum]; exact track_sum univ _ _ fun i _=>hp i
abbrev tentRate:ℝ:= (∑ i:vendors,crustP i)*palCost
lemma marked_w (b:Bool)(A:Pane n→Pal)(k:lotV)(g: Haw p o (Pax o) A v)(r:h≠0)(u:20<n.val)(hX:p.power ≤3)(hY:p.order ≤6):TrackD p (Pach o) h (plac (beamer o k A h) b) (tentRate*v):=by
 let F:=RegPay o k hX hY g h; have hx(t:Cover)(c:lateral t ≤4): node (parked o t)∈ Pach o:=halo_spec.mpr ⟨o,mem_singleton_self _, (spot_gap o t c u).trans (by decide)⟩
 apply track_p (transitA o b (landX o k) (landY o k) (hx _ (knot_rad k).1) (hx _ (knot_rad k).2) _ F); unfold tentRate; rw [← Finset.sum_mul]; apply le_of_eq; field_simp
end MastTin
end YM.CF.XGarden
end
