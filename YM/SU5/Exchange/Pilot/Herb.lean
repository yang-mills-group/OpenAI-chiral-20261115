import YM.SU5.Exchange.Pilot.Plying
import YM.SU5.Exchange.Ward.Coat
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}

variable {q:ℕ}{h a b d e:ℝ}
open Rill Branch Tenant Drapes Leaf
structure Herb (P:BudgetPoint)(q:ℕ)(Y:Aura n)(h:ℝ)(V:Firing n)(a:ℝ):Prop where
 price : 0 ≤ a
 offer: ∀ X:Aura n, Y.val⊆ X.val→∀ D⊆ X.val, halo (cipherK q) D⊆ X.val→ Marque P X Y D V h a
 clean: ∀ X:Aura n, Y.val⊆ X.val→∀ i:Orbit n,i.1∈Sour.σX P X ∅→∀ t:Ids n,V (i.1,t)=V i
namespace Herb
variable (f:Herb P q Y h V a)(g:Herb P q Y h W b)
lemma scalar (y:ℂ):Herb P q Y h (y • 1) ‖y‖:=⟨norm_nonneg _,fun _ _ _ _ _=> Marque.scalarR _,fun _ _ _ _ _=>rfl⟩
lemma zeroR :Herb P q Y h 0 0:=by simpa using (Herb.scalar (P:=P) (q:=q) (Y:=Y) (h:=h) 0)
include f g
lemma addR : Herb P q Y h (V+W) (a+b):=⟨add_nonneg f.price g.price,fun X u D v k=> (f.offer _ u _ v k).addR (g.offer _ u _ v k),fun _ p v u i => congrArg₂ (·+·) (f.clean _ p v u i) (g.clean _ p v u i)⟩
lemma mulR : Herb P q Y h (V*W) (a*b):=⟨mul_nonneg f.price g.price,fun X u D v k=> (f.offer _ u _ v k).multR (g.offer _ u _ v k) f.price,fun _ p v u i => congrArg₂ (·*·) (f.clean _ p v u i) (g.clean _ p v u i)⟩
omit g
lemma scR (x:ℂ):Herb P q Y h (x • V) (‖x‖*a):=⟨mul_nonneg (norm_nonneg _) f.price,fun X u D v k=> (f.offer _ u _ v k).scR x, fun _ p v u i=>by rw [Pi.smul_apply,Pi.smul_apply,f.clean _ p v u i]⟩
lemma negR: Herb P q Y h (-V) a:=by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using f.scR (-1)
lemma large_r (w:0 ≤ h)(k:a≤b):Herb P q Y h V b:=⟨le_trans f.price k,fun X u D v l=> (f.offer _ u _ v l).bigger w k, f.clean⟩
lemma mantle (u:Y.val⊆Z.val):Herb P q Z h V a:=⟨f.price,fun X v D w k=> (f.offer X (u.trans v) D w k).riseSup u,fun X v=> f.clean X (u.trans v)⟩
lemma mask (S:Support (More n))(g:S⊆Y.val): Herb P q Y h (capR P S V) a:=by
 refine ⟨f.price,fun X u D v k=> (f.offer _ u _ v k).capMask _ (g.trans u),?_⟩; intro X u i p t; by_cases k:i∈ pingMask P S; · rw [capR, Set.indicator_of_mem (show (i.1,t)∈_ from k),Set.indicator_of_mem k]; exact f.clean _ u i p t
 rw [capR,Set.indicator_of_notMem (show (i.1,t)∉_ from k),Set.indicator_of_notMem k] -- likely rw targets
lemma body(V':Orbit n): Fock.Sector (camp Y.val) false (V V'):= (f.offer Y le_rfl ∅ (empty_subset _) (by simp [Lattice.halo])).body V'
omit f
lemma whole {ι:Type*}(S:Finset ι)(V:ι→Firing n)(a:ι→ℝ)(t:∀ i∈S,Herb P q Y h (V i) (a i)): Herb P q Y h (∑ i∈S,V i) (∑ i∈S,a i):=by
 induction S using Finset.induction_on with |empty=>rw [sum_empty,sum_empty]; exact Herb.zeroR|insert i S v ih=>rw [sum_insert v,sum_insert v]; exact (t i (mem_insert_self ..)).addR (ih fun i p=>t i (mem_insert_of_mem p))
lemma growth {F:InkD n}{i:Scree.Hub n}(u:1≤h)(r:PressB P i F h a)(t:i.val.2⊆Y.val):Herb P q Y h (wetPC P i F) (chi_f P.order*a):= ⟨((rimR r (zero_le_one.trans u)).wage (zero_le_one.trans u)),fun X x _ _ _=> wetR r u t x, fun _ _ _ _ _=>rfl⟩
lemma kernelR {d m a t:ℝ}{S:Support (More n)}{L:Scree.Loom n}{F:Raw (Openc (More n) d) (Single n)}{C:Toll (Single n)} (p:Roof n t d q L) (x:0<d)(Jf:Op (Single n)→FC (Dwell n))(Z:Single n→ Single n → FC (Dwell n))(u:Suite (badge _) (bail n d) (bail n d) S C F)(Φ:Glyph Jf Z h)
 (v:P.threshold ≤ t)(w:HopeT d m a P.order) (hv:P.threshold ≤ a)(b0:cipherK q ≤ 5*P.B)(b1:3≤P.B)(hS:halo (q+10) S ⊆ Y.val) :Herb P q Y h (Glyph.cure Jf p x F) (Glyph.vest P h C):=by
 refine ⟨mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun i _=> sum_nonneg fun j _=> u.nonn i j)) (by positivity),fun X v0 D _ r=> Glyph.sail_p Φ p x u v r b0 b1 hS v0 w hv,?_⟩
 intro X t i pi l; unfold Glyph.cure; refine congrArg Jf ?_; apply Rill.pact_p x p u _ _; intro j r _; rw [Rill.fern p v S (Subset.trans hS t) _ pi _ r rfl l]; rcases i with ⟨i,g⟩; exact (Rill.fern p v S (Subset.trans hS t) _ pi _ r rfl g).symm -- no case refs
end Herb
-- weight specifically earned for empty first derivative column (includes X or larger, but
-- no flags/D). This doesn't claim rank on V, or that V≈W. W pays only this birth!
structure Flight (P:BudgetPoint)(q:ℕ)(Y:Aura n)(h:ℝ)(V:Firing n)(a b:ℝ) : Prop where
    tube: Herb P q Y h V a
    forms: ∃ W:Firing n, Herb P q Y h W b ∧ ∀ X:Aura n,Y.val⊆ X.val→∀ U:Orbit n,U.1∈ Sour.σX P X ∅ →Sault.rind (V U)=Sault.rind (W U)
namespace Flight
variable (p:Flight P q Y h V a b)(t:Flight P q Y h W d e)
lemma once (p:Herb P q Y h V a): Flight P q Y h V a a:=⟨p,V,p,fun _ _ _ _=>rfl⟩
lemma laidR (t:Herb P q Y h V a)(v:∀ X:Aura n,Y.val⊆ X.val→∀ U:Orbit n,U.1∈ Sour.σX P X ∅→ acts (V U) (vacuum (Dwell n))=0):Flight P q Y h V a 0:=by
 refine ⟨t,0,Herb.zeroR,?_⟩; intro X y U w; apply Sault.sky (Sault.skit _) (Sault.skit _); rw [Sault.tileL, Sault.tileL,Pi.zero_apply,act_zero,v _ y U w]
lemma zeroR :Flight P q Y h 0 0 0:= Flight.once Herb.zeroR
include p t
lemma addR : Flight P q Y h (V+W) (a+d) (b+e):=by
 obtain ⟨A,B,C⟩:=p.forms; obtain ⟨G,H,I⟩:= t.forms; refine ⟨p.tube.addR t.tube, A+G,B.addR H,?_⟩; intro X z i w; rw [Pi.add_apply, Pi.add_apply, Sault.rind,Sault.rind,map_add,map_add]; exact congrArg₂ (·+·) (C _ z i w) (I _ z i w)
omit t
lemma scR (x:ℂ): Flight P q Y h (x • V) (‖x‖*a) (‖x‖*b):=by
 obtain ⟨A,B,C⟩:= p.forms; refine ⟨p.tube.scR x,x • A,B.scR x,?_⟩; intro X z i w; unfold Sault.rind; rw [Pi.smul_apply, Pi.smul_apply,map_smul,map_smul]; exact congrArg (x • ·) (C _ z i w)
lemma negR : Flight P q Y h (-V) a b:=by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using p.scR (-1)
lemma mantle (w:Y.val⊆ Z.val): Flight P q Z h V a b:=by
 obtain ⟨A,B,C⟩:=p.forms; exact ⟨p.tube.mantle w,A,B.mantle w,fun X v=> C _ (w.trans v)⟩
lemma large_r (hv:0≤h)(u:a≤d)(v:b≤e):Flight P q Y h V d e:=by
 obtain ⟨A,B,C⟩:= p.forms; exact ⟨p.tube.large_r hv u,A,B.large_r hv v,C⟩ -- tune '_'
lemma mask (S:Support (More n))(u:S⊆Y.val): Flight P q Y h (capR P S V) a b:=by
 obtain ⟨A,B,C⟩:=p.forms; refine ⟨p.tube.mask S u,capR P S A,B.mask S u,?_⟩; intro X v i w; have hz:i∈pingMask P S := (pingFix (u.trans v) w).mpr (by simp); rw [capR,capR,Set.indicator_of_mem hz,Set.indicator_of_mem hz]; exact C X v i w
omit p
lemma whole {ι:Type*}(S:Finset ι)(V:ι→ Firing n)(a b:ι→ℝ)(w:∀ i∈S,Flight P q Y h (V i) (a i) (b i)):Flight P q Y h (∑ i∈S,V i) (∑ i∈S,a i) (∑ i∈S,b i):=by
 induction S using Finset.induction_on with
 |empty=> rw [sum_empty,sum_empty,sum_empty]; exact Flight.zeroR
 | insert i S v ih=> rw [sum_insert v,sum_insert v,sum_insert v]; exact (w i (mem_insert_self ..)).addR (ih fun i p=>w i (mem_insert_of_mem p))
end Flight
end YM.CF.Sour
