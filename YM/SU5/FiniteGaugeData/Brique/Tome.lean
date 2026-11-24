import YM.SU5.FiniteGaugeData.Brique.Dress
import YM.SU5.FiniteGaugeData.Hierarchy.Rigid
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Tint Window.Brique
-- Narrative with continuous RAW gauge mark; no geometric hypotheses hidden. t reports charge taps. `S` measured housing, `U` removal house. Combine with declarations of contents and separations. every term B is product of |t| separated chiral bilinears, left-handed for a single SU species (multiplicity elsewhere). No annihilation contact contribution has slipped past equality between S spaces.
inductive Tableau (K:Calibration)(σ:Window.Family)(U S:Finset Cover): List Cover → Family K → Prop where
 | ident : Tableau K σ U S [] 1
 | zero (t:List Cover): Tableau K σ U S t 0
 | pair {t:List Cover}{F:Family K}(p:Tableau K σ U S t F)(x y:Cover)(h:nodeC y∈U)(i j:SpinIdx)(a b:SU.Slot) (upper:i∈plusHalf)(lower:j∉plusHalf)(e:family a=σ)(f:family b=σ): Tableau K σ U S (x::t) (F*(creation K x i a * removal K y j b))
 | add {t:List Cover} {F G:Family K} : Tableau K σ U S t F → Tableau K σ U S t G → Tableau K σ U S t (F+G)
 | scale {t : List Cover}{F:Family K}(p:Tableau K σ U S t F)(c:ℂ): Tableau K σ U S t (c • F)
 | gauge {t : List Cover}{F:Family K}(p:Tableau K σ U S t F)(W:PairsC→ℂ) (q:Coeff false S W) : Tableau K σ U S t (scalar K W * F)

namespace Tableau
variable {K:Calibration}{σ:Window.Family}{U S:Finset Cover}{t:List Cover}{F G:Family K}(p:Tableau K σ U S t F)(v:U⊆S)(u:∀ x∈t,nodeC x∈S)
lemma sum {I:Type*}(S':Finset I)(f:I→Family K)(h:∀ i∈ S',Tableau K σ U S t (f i)): Tableau K σ U S t (∑ i∈ S',f i):=by classical
                                                                                                        induction S' using Finset.induction_on with
                                                                                                          | empty=> rw [sum_empty]; exact .zero _
                                                                                                          | insert i t z ih=> rw [sum_insert z]; exact (h i (mem_insert_self ..)).add (ih (fun v x=>h v (mem_insert_of_mem x)))
include p v u
lemma tier : InTest K false S false F:= by
 induction p with
 | ident=>exact .one
 | zero=>exact .zero
 | pair _ x y t i j a b h p _ _ ih=> exact .mul (ih (fun i h=>u i (List.mem_cons_of_mem _ h))) (.mul (.creator a h (u _ List.mem_cons_self)) (.remover b p (v t)))
 | add _ _ a b=> exact (a u).add (b u)
 | scale _ c a=>exact .smul c (a u)
 | gauge _ W t a=>exact .mul (.seed t) (a u)
omit v u
lemma native (i:Side)(w:Fields (K.c i)): Trio σ (K.c i) (region U (K.c i)) (t.map (wrap (K.c i))) (F i w):= by -- u and v not needed? remove incl
 induction p with
 | ident=>exact .unit
 | zero t=>exact .zero _
 | pair h x y t I J a b e f r s ih=>
    let x':= wrap (K.c i) x; let N:=K.c i
    let θ(x:Cover)(a:SpinIdx)(b:SU.Slot):= basisC N x a b
    have hx:withinM (capU σ x') (θ x I a):=by unfold θ basisC withinM; rw [map_smul, within_basis (capU σ x') (Lifted.index N x I a) ((is_cap x' _).2 ⟨(grade_one ..).2 e,r,rfl⟩)]
    have hz:withinM (lumen σ (region U N)) (θ y J b):=by unfold θ basisC withinM; rw [map_smul, within_basis _ (Lifted.index _ _ _ _) ((is_lumen ..).2 ⟨fun p=>f ((grade_one ..).1 p),s,(node_of N y).symm ▸ mem_image_of_mem (wrap (More N)) t⟩)]
    exact ih.action x' (θ x I a) (θ y J b) hx hz
 | add _ _ a b=>exact a.add b
 | scale _ c a=>exact a.mul c
 | gauge _ W h a => rw [Pi.mul_apply,Pi.mul_apply,scalar,Algebra.smul_mul_assoc,one_mul]; exact a.mul _
end Tableau

variable (K:Calibration) (σ:Window.Family)(U S:Finset Cover) (t:List Cover){m:Side}
set_option quotPrecheck false
local notation "N" => K.c m
local notation "P"=> Tableau K σ U S
private lemma rent (y:Cover) : Lifted.winding N y≠0:= norm_pos_iff.mp (by unfold Lifted.winding; rw [Rush.fee_norm]; exact zero_lt_one)
section
private lemma sparksUp (x:Cover)(a:Single N)(p:a∈capU σ (wrap N x)): ∃ i∈plusHalf,∃ b:SU.Slot,family b=σ ∧ a=Lifted.index N x i b ∧ (∀ z,(creation K x i b m z)= Lifted.winding N x • put a):=by
 obtain ⟨⟨x',t⟩,b⟩:=a; obtain ⟨f,v,h⟩:((x',t),b)∈Tset N ∧ family b=σ ∧ x'=wrap N x := (is_cap ..).1 p
 subst x'; refine ⟨t,(grade_one t b).1 f,b,v,rfl,fun z=>?_⟩; rw [creation,basisC,map_smul,create_put]; -- tune
 rfl
lemma sparksLow (a:Single N)(h: Hosp U N)(p:a∈lumen σ (region U N)): ∃ y:Cover,nodeC y∈U ∧ ∃ i:SpinIdx, i∉plusHalf∧ ∃ b:SU.Slot,family b=σ ∧ a=Lifted.index N y i b ∧ (∀ z,(removal K y i b m z)= star (Lifted.winding N y) •takeF a):=by
 obtain ⟨w,rfl⟩:= occupy_surj U h a ((modes_at ..).2 ((is_lumen ..).1 p).2.2); obtain ⟨⟨x,i,b⟩,hp⟩:=w; change Lifted.index N x i b∈ _ at p
 obtain ⟨z,g,_⟩:= (is_lumen ..).1 p; refine ⟨x,hp,i,fun u=>z ((grade_one ..).2 u),b,g,rfl,fun z=>?_⟩; rw [removal,basisC,Fock.remove,map_smul,star_smul,create_put]
 rfl
-- Exactly synthesizing tableau from native geometry evidence. Per-phase support & narrow class. chosen AFTER election but consistent at all periods, both Links.
lemma scaled_pair(F:Family K)(v:Tableau K σ U S t F)(x y:Cover)(h:nodeC y∈U)(i j:SpinIdx)(u: i∈plusHalf)(p:j∉plusHalf)(a b:SU.Slot)(z:family a=σ)(q:family b=σ):∃ f:Family K,Tableau K σ U S (x::t) f ∧ ∀ w, f m w= F m w * (put (Lifted.index N x i a)* takeF (Lifted.index N y j b)):=by
 let r:= Lifted.winding N x; let s:= star (Lifted.winding N y); refine ⟨(r*s)⁻¹ • _,(v.pair x y h i j a b u p z q).scale _, fun w=>?_⟩; let g:= Lifted.index N x i a; let y':= Lifted.index N y j b; have hz: removal K y j b m w = s • takeF y':=by unfold removal Fock.remove basisC; rw [map_smul,star_smul, create_put]
 have hx: creation K x i a m w = r • put g:=by unfold creation basisC; rw [map_smul,create_put]
 rw [Pi.smul_apply,Pi.smul_apply,Pi.mul_apply,Pi.mul_apply,Pi.mul_apply,Pi.mul_apply,hz,hx, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.mul_smul_comm, Algebra.mul_smul_comm]; change (r*s)⁻¹ • r • s • (F m w*(put g*takeF y'))=_; rw [smul_smul r s]; exact inv_smul_smul₀ (mul_ne_zero (rent K (m:=m) x) (show s ≠ 0 from by unfold s; simpa using rent (m:=m) K y)) _
include t
private lemma spread_low {w:List (Site (K.c m))} {v:FC (Single (K.c m))} (p:Trio σ (K.c m) (region U (K.c m)) w v) (h:Hosp U (K.c m))(q:w=t.map (wrap (K.c m))): ∃ f:Family K, Tableau K σ U S t f ∧ ∀ x:Fields _, f m x=v:=by
 induction p generalizing t with
 | unit=> refine ⟨1, ?_, fun _=>rfl⟩; rw [List.map_eq_nil_iff.mp q.symm]; exact .ident
 | zero=> exact ⟨0,.zero _,fun _=>rfl⟩
 | @grow t' A p i x hx y hy ih=>
    obtain _|⟨j,s⟩:=t; contradiction
    have hz:= List.cons.inj q; obtain ⟨a,sA,f⟩:= ih s hz.2; obtain ⟨b,pB,c,c0,e,-⟩:= sparksUp K σ j x (hz.1 ▸ hx); obtain ⟨y,p',y2,g,d,e',x',_⟩:= sparksLow K σ U _ h hy
    obtain ⟨f',v,H⟩:= scaled_pair (m:=m) K σ U S s a sA j y p' b y2 pB g c d c0 e'; refine ⟨f',v,fun z=>?_⟩; rw [H, f, ←e, ←x']
 | @add t' A B l y h x=> obtain ⟨j,k,u⟩:=h t q; obtain ⟨i,v,g⟩:=x t q; exact ⟨j+i,k.add v,fun a=>congrArg₂ (·+·) (u a) (g a)⟩
 | mul _ c a=> obtain ⟨f,z,g⟩:= a t q; exact ⟨c•f,z.scale c,fun i=>congrArg (fun x:FC (Single N)=>c•x) (g i)⟩
end
-- attach support of U for tier. synthesis chooses basis of allowed `Trio`, so only genuine words. Uses CONTINUITY; Borel variant via same. No reliance on links consistency beyond Roomy 
lemma press4 {F:Family K} (v:InTest K true S false F) (h:Roomy S (K.c m))(p:U ⊆ S)(r:∀ x∈t,nodeC x∈ S)(B:Window.Brique.Free (region S (K.c m)) (F m))(g:∀ x,Trio σ (K.c m) (region U (K.c m)) (t.map (wrap (K.c m))) (F m x)): Tableau K σ U S t F := by
 let M:= syllabus σ (K.c m) (region U (K.c m)) (t.map (wrap (K.c m))); let W:= Fin (Module.finrank ℂ M)
 let β:= Module.finBasis ℂ M; let X (z:Fields N):↥M:=⟨F m z,g z⟩; have he:Hosp U N:=hosp_mono (roomy_hosp S h) p
 have hv:∀ i:W,∃ A:Family K,Tableau K σ U S t A∧∀ x:Fields N,A m x=(β i).val:= fun i=> spread_low K σ U S t (β i).property he rfl
 choose A a ha using hv; let f (i:W) (x:LinksC):ℂ:= β.coord i (X (replant S _ (x,x))); let cx (i:W):Coeff false S (f i ∘ Prod.fst):= by
    refine .fromC _ _ ((β.coord i).continuous_of_finiteDimensional.comp ?_) ?_; · have he:Continuous (Satin.graft S N):=(by apply continuous_pi; intro i; unfold Satin.graft; split; exact continuous_apply _; exact continuous_const); exact (Continuous.subtype_mk B.cont _) |>.comp (he.prodMk he)
    intro x y t; have hz:= graft_agrees S h t; exact congrArg (β.coord i) (Subtype.ext (B.zone.dep (replant S N (x,x)) (replant S N (y,y)) hz hz) : X _= X _)
 let Y:= fun i:W=> scalar K (f i ∘ Prod.fst)* A i; have H: Tableau K σ U S t (∑ i:W,Y i) := Tableau.sum _ _ fun i _=> (a i).gauge _ (cx i)
 refine (family_eq K S (roomy_hosp S h) (H.tier p r).widen v ?_) ▸ H; funext x; simp_rw [Finset.sum_apply,Y,Pi.mul_apply,ha, scalar,Function.comp_apply, Algebra.smul_mul_assoc,one_mul]; -- Pi.mul of inner too?
 let a':=X x; have ht:X (replant S N (onC N x.1,onC N x.1))=X x:=Subtype.ext (by have hz:= graft_preserves S (roomy_hosp S h) x.1; exact (B.zone.dep _ (x.1,x.1) hz hz).trans (B.fixed x.1 x.2).symm)
 simp_rw [f,ht]; exact (map_sum M.subtype (fun i:W=>β.repr a' i • β i) _).symm.trans (congrArg Subtype.val (β.sum_repr a')) -- tune
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
