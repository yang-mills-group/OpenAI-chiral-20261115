import YM.SU5.FiniteGaugeData.Pannier.Cliques
/-!
# Tomes of the witness across all cutoffs.

`CRow`: texture of a **fixed** list of anchors — bare matter word span with spin/chiral support. `Filigree`: finite combinations with continuous first coefficients, **list nonempty nodup**, even. In application keep β period-dependent but coherent
 gauge law; use fixed-separation (NO CONTACT WITH ANY ANCHOR) cover formula, including
 the limit. Separation at this observing scale; not asserting that these are point-local
 fields or that any of their stencils fit smaller relativistic diamonds.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Window (mem_Tset family)
open Py.Rate.Pannier
open Lifted
open Reed (Fine)
open Afterglow
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{k:ℕ}{b:Fin k→ Cover}{S:Finset Cover}{s:SU.Slot}{W:Window.Family}{L:List (Fin k)}{v:Buffered.Family K}
inductive CRow (K:Calibration) (W:Window.Family)(b:Fin k→ Cover)(S:Finset Cover): List (Fin k)→ Buffered.Family K →Prop where
 | gave : CRow K W b S [] 1
 | pair (j:Fin k)(y:Cover)(c d:SpinIdx)(g a:SU.Slot){f l} : family a=W→ family g=W → c∉plusHalf→ d∈plusHalf→ nodeC y∈ S→ nodeC (b j)∈S→ (∀ t,y≠b t)→ CRow K W b S l f → CRow K W b S (j::l) ((removal K (b j) c a*creation K y d g)*f)
 | zip {l}: CRow K W b S l 0
 | glaze(x:ℂ){l f}: CRow K W b S l f → CRow K W b S l (x • f)
 | fuse {f g l}: CRow K W b S l f → CRow K W b S l g → CRow K W b S l (f+g)
def Lode (K:Calibration) (W:Window.Family)(b:Fin k→ Cover)(S:Finset Cover) := Submodule.span ℂ {v|∃ L,L ≠ []∧ L.Nodup ∧ CRow K W b S L v}
def Filigree (K:Calibration) (W:Window.Family)(b:Fin k→ Cover)(S:Finset Cover) := Submodule.span ℂ {v|∃ (x:Buffered.Family K) (z:PairsC→ℂ), x∈ Lode K W b S ∧ Coeff false S z∧ v=scalar K z*x}
lemma CRow.inTest (h:CRow K W b S L v): InTest K false S false v:=by
 induction h with
 | gave=>exact .one
 | zip=>exact .zero
 | glaze _ _ ih=>exact .smul _ ih
 | fuse _ _ p q=>exact .add p q
 | pair j y i d g a _ _ x v u p _ _ ih=> exact .mul (.mul (.remover _ x p) (.creator _ v u)) ih
lemma Lode_test (p:v∈ Lode K W b S): InTest K false S false v:=by
 refine Submodule.span_induction (p:=fun v _=> InTest _ _ _ _ v) (fun v h=>?_) (.zero) (fun _ _ _ _ p q=> .add p q) (fun a b _ h=> .smul a h) p
 obtain ⟨_,_,_,t⟩:=h; exact t.inTest
lemma FilTest (p:v∈ Filigree K W b S): InTest K false S false v:=by
 refine Submodule.span_induction (p:=fun v _=> InTest _ _ _ _ v) (fun v h=>?_) (.zero) (fun _ _ _ _ p q=> .add p q) (fun a b _ h=> .smul a h) p
 obtain ⟨x,z,g,q,rfl⟩:= h; exact .mul (.seed q) (Lode_test g)

namespace Filigree
open Tapestry Satin Tapestry.Roomy -- introduces names
variable {m n:Side}{v':Cover}
private lemma nodeSend {o:Cover}{p:Site n}(h:(node p)=wrap (More n) o) : ∃ c: Cover,o=nodeC c ∧ wrap n c=p:=by
 let u:=nodeC (Rush.natural p); let k:= periods (More n) o-periods (More n) u
 let b:= Rush.natural p + n.val • k
 have hp:wrap (More n) o=wrap (More n) u:= by unfold u; rw [←node_of,Rush.nat_true]; exact h.symm
 have he:o=u+(More n).val • k:=by
    have e:= carrying (More n) o; have g:=carrying (More n) u
    unfold k; rw [hp] at e; rw [smul_sub]; calc
    _ = (natural ((wrap (More n)) u)+(More n).val • periods (More n) u) + ((More n).val • periods (More n) o - (More n).val • periods (More n) u) := e.symm.trans (by abel)
    _ = _:= by rw [g]
 have hf:o=nodeC b:=by rw [he,show (More n).val= (2:ℕ)*n.val from (mul_comm ..),mul_smul]; unfold u b nodeC; rw [smul_add]; abel
 exact ⟨b,hf,Tenant.needle (by rw [node_of,←hf]; exact h.symm)⟩
variable (K W b S m) -- implicit b binder dependent k
private def Chamber (l:List (Fin k)): Submodule ℂ (FC (Single (K.c m))) where
 carrier:={f|∃ x:Buffered.Family K,CRow K W b S l x ∧ ∀ y,x m y=f}
 zero_mem':= ⟨0,CRow.zip,fun _=>rfl⟩
 smul_mem' a i e:=by obtain ⟨f,h,v⟩:= e; exact ⟨a • f,h.glaze a,fun y=> congrArg (a • ·) (v y)⟩
 add_mem' {f g} h u:=by obtain ⟨f',p,v⟩:=h; obtain ⟨g',s,w⟩:=u; exact ⟨f'+g',p.fuse s,fun y=> congrArg₂ (· + ·) (v y) (w y)⟩
-- ensure one-call linear reconstruction
variable {W b S} {f: Buffered.Family K}{k' :Fin k} {l:List (Fin k)}
private lemma one_r (P:FC (Single (K.c m)))(i j:Single (K.c m))(a:Fin k)(g: P∈ Chamber K b S W m l)
    (hx:Removal W ((wrap (K.c m))∘ b) a (basisKet i))(he:Creator W ((wrap (K.c m))∘ b) (region S (K.c m)) (basisKet j))(q:∀ i,nodeC (b i)∈ S): (remove (basisKet i)*create (basisKet j))*P ∈ Chamber K b S W m (a::l):=by
 let n:=K.c m; have hp{T:Finset (Single n)}(i)(p:withinM T (basisKet i)) : i∈ T:=by by_contra h; unfold withinM at p; rw [cut_basis,if_neg h] at p; exact zero_ne_one (α:=ℝ) (by rw [← show ‖basisKet i‖=1 by simp [basisKet],←p,norm_zero]) -- tune
 have hb:= (modes_at ..).1 (hp _ hx.venue); have h1:= (mem_compl.mp (hp _ hx.spin)); have h2:= (labelAt ..).1 (hp _ hx.foot); have hγ:(wrap n ∘b) a= i.1.1:= Tenant.needle (mem_singleton.mp hb)|>.symm -- tune
 obtain ⟨⟨x,i⟩,z⟩:=i; obtain ⟨⟨y,j⟩,c⟩:=j; change wrap n (b a)=x at hγ; obtain rfl:= hγ
 have ht:= he.banned; obtain ⟨F,g,p⟩:= g; obtain ⟨w,d,r⟩:= Finset.mem_image.mp ((modes_at ..).1 (hp _ he.venue)); obtain ⟨y',k,rfl⟩:= nodeSend r.symm -- rewrite occurrence lhs? get rfl issue
 have hy: nodeC y'∈ S:= k ▸ d; let A:= b a;
 refine ?_
 have ht':(∀ i,y'≠b i):=fun i hx=> mem_compl.mp (hp _ ht) ((modes_at ..).2 (by exact hx ▸ mem_image_of_mem (node (N:=n) ∘ (wrap n) ∘ b) (mem_univ i)))
 have hR:= CRow.pair a y' i j c z h2 ((labelAt ..).1 (hp _ he.foot)) (mt (mem_Tset ..|>.2) h1) ((mem_Tset ..).1 (hp _ he.spin)) hy (q a)  ht' g
 let t:=Lifted.winding n (b a); let u:= Lifted.winding n y'; refine ⟨_,(hR.glaze (t*u)),fun x=>?_⟩; rw [Pi.smul_apply,Pi.smul_apply,Pi.mul_apply,Pi.mul_apply,Pi.mul_apply,Pi.mul_apply,p x];
 let P':= basisKet (Lifted.index n (b a) i z); let Q:=basisKet (Lifted.index n y' j c); change (t*u) • ((remove (t • P')*create (u • Q))*P)= _; unfold remove; rw [map_smul,map_smul,star_smul, show star t=t from fee_real _, Algebra.smul_mul_assoc,Algebra.mul_smul_comm, smul_smul,Algebra.smul_mul_assoc, smul_smul,mul_mul_mul_comm,show t*t=_ from fee_one _,show u*u=_ from fee_one _,one_mul,one_smul]; rfl
lemma CLine_mend (C:FC (Single (K.c m)))(u:Line W (wrap (K.c m) ∘ b) (region S (K.c m)) L C) (x:∀ i,nodeC (b i)∈ S) : ∃ v, CRow K W b S L v∧∀ y:Fields _, v m y=C:=by
 change _∈ Chamber K b S W m L; let n:=K.c m; induction u with
 |nil=> exact ⟨1,.gave,fun _=>rfl⟩
 |push i h q t g=>
    rename_i a b' X F -- check inaccessible L V P
    -- linear op equation via ket expansions
    let R:=Chamber K b S W m (i::a)
    nth_rw 1 [←basis_expand b',←basis_expand X]; unfold remove; rw [map_sum,map_sum,star_sum,sum_mul,sum_mul]; apply Submodule.sum_mem; intro j _; rw [mul_sum,sum_mul]; apply Submodule.sum_mem; intro k _; rw [map_smul,map_smul,star_smul]; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc];
    by_cases y:b'.ofLp j=0; · rw [y,star_zero,zero_smul]; exact Submodule.zero_mem _
    apply Submodule.smul_mem; by_cases p:X.ofLp k=0; · rw [p,zero_smul]; exact Submodule.zero_mem _
    have ht{A:Finset (Single n)}{u:Ket (Single n)}{ξ:Single n}(p:withinM A u)(he:u.ofLp ξ ≠ 0) : withinM A (basisKet ξ):=within_basis _ _ (Classical.byContradiction (fun t=> he ((within_test ..).1 p _ t)))
    exact Submodule.smul_mem _ _ (one_r K m F j k i g ⟨ht h.1 y,ht h.2 y,ht h.3 y⟩ ⟨ht q.1 p,ht q.2 p,ht q.3 p,ht q.4 p⟩ x)

lemma hap_one {C:FC (Single (K.c m))}(p:C∈ Hap W ((wrap (K.c m)) ∘ b) (region S (K.c m)))(x:∀ i,nodeC (b i)∈ S) : ∃ F:Buffered.Family K, F∈ Lode K W b S∧ ∀ i,F m i=C:=by
 let U:= Lode K W b S
 refine Submodule.span_induction (p:=fun x _=> ∃ F:Buffered.Family K, F∈ U ∧ ∀ i,F m i=x) (fun f p=>?_) ⟨0,U.zero_mem,fun _=>rfl⟩ ?_ ?_ p
 · obtain ⟨L,p,r,c⟩:= p; obtain ⟨V,x,y⟩:=CLine_mend K m f c x; exact ⟨V,Submodule.subset_span (show _∈ _ from ⟨L,p,r,x⟩),y⟩ -- tune
 · intro a v _ _ h u; obtain ⟨V,v₁,x⟩:=h; obtain ⟨F,h,f⟩:=u; exact ⟨_,U.add_mem v₁ h,fun i=>congrArg₂ (· + ·) (x i) (f i)⟩
 intro l h _ t; obtain ⟨V,v₁,f⟩:=t; exact ⟨_,U.smul_mem l v₁,fun i=>congrArg (l • ·) (f i)⟩
end Filigree
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Filigree.hap_one
