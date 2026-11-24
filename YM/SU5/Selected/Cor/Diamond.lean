import YM.SU5.Selected.Cor.Micah
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Lifted
open Window (family) -- maybe syntax invalid
open Py.Rate.Pannier
open Afterglow Afterglow.Tapestry
set_option synthInstance.maxSize 22000
attribute [local instance] opCStarAlgebra
namespace Rubric
-- native comparator; T location of Ward pulse; all creation necessarily outside. Row allows any later and earlier union. orientation remove north. today issue matter bands measured via gauge units for X.
-- Period extension will guarantee label, charge, ALL coordinates. use when compiled AtSupport Mark. no assumption prior m beyond roster construction.
open Tapestry Satin
variable (K:Calibration)(W:Window.Family)(D X Y S:Finset Cover)(N:Side) (r m n:ℕ)
def Reach: Submodule ℂ (FC (Single (K.c N))) where
 carrier:= {f|∃ F, Row K W D X Y S r m n F∧ ∀ x,F N x=f}
 zero_mem':=⟨0,.zero,fun _=>rfl⟩
 add_mem' h g:=by obtain ⟨F,f,t⟩:=h; obtain ⟨F',v,z⟩:=g; exact ⟨F+F',f.adds v,fun x=> congrArg₂ (·+·) (t x) (z x)⟩
 smul_mem' x y h:=by obtain ⟨F,f,g⟩:= h; exact ⟨x • F,f.coeff x,fun j=> congrArg (x • ·) (g j)⟩
namespace Reach
variable {K W D X Y S N r m n} {a b c:ℕ} {f g:FC (Single (K.c N))}
local notation "α"=> K.c N
local notation "σ"=> Reach K W D X Y S N
lemma hold (h:f∈ σ r m n)(p:g∈ σ a b c): f*g∈ σ (r+a) (m+b) (n+c):=by obtain ⟨F,v,t⟩:=h; obtain ⟨G,p,x⟩:=p; exact ⟨F*G,v.grip p,fun y=> congrArg₂ (·*·) (t y) (x y)⟩
lemma oneR : 1∈ σ 0 0 0:=⟨1,.polo,fun _=>rfl⟩
lemma nodePel {N':Side}{o:Cover}{p:Site N'}(h: wrap (More N') o = (node p)) : ∃ c: Cover,o=nodeC c ∧ wrap N' c=p:=by
 let u:=nodeC (Rush.natural p); let k:= periods (More N') o-periods (More N') u
 let b:= Rush.natural p + N'.val • k
 have hp:wrap (More N') o=wrap (More N') u:= by unfold u; rw [←node_of,Rush.nat_true]; exact h
 have he:o=u+(More N').val • k:=by
    have e:= carrying (More N') o; have g:=carrying (More N') u
    unfold k; rw [hp] at e; rw [smul_sub]; calc
    _ = (natural ((wrap (More N')) u)+(More N').val • periods (More N') u) + ((More N').val • periods (More N') o - (More N').val • periods (More N') u) := e.symm.trans (by abel)
    _ = _:= by rw [g]
 have hf:o=nodeC b:=by rw [he,show (More N').val= (2:ℕ)*N'.val from (mul_comm ..),mul_smul]; unfold u b nodeC; rw [smul_add]; abel
 exact ⟨b,hf,Tenant.needle (by rw [node_of,←hf,h])⟩
lemma remove_zone {f:Ket (Single α)} (v:withinM (labelQ α W) f)(h:withinM (Tset α)ᶜ f) (P:Finset Cover) (u:withinM (modesIn α (park α P)) f)(g:P⊆X)(z:P⊆ S)(q:∀ t∈P,(if t∈ D then 1 else 0)=r):
    Fock.remove f∈ σ 1 0 r:=by
 nth_rw 1 [←basis_expand f]; let U:= σ 1 0 r; unfold Fock.remove; rw [map_sum, star_sum]; apply U.sum_mem
 rintro ⟨⟨x,j⟩,t⟩ _; let i:= ((x,j),t); by_cases hp:f.ofLp i=0; · rw [map_smul,star_smul,hp,star_zero,zero_smul]; exact U.zero_mem
 have hk(L:Finset (Single α))(p:withinM L f):i∈ L:= Classical.byContradiction fun z=> hp ((within_test ..).1 p _ z)
 rw [map_smul,star_smul]; apply U.smul_mem; obtain ⟨w,d,e⟩:= mem_image.mp ((modes_at ..).1 (hk _ u)); obtain ⟨k,a,b⟩:= nodePel e; subst w; have ht:(wrap (K.c N)) k = x:= b; let p:=winding (α) k
 refine ⟨(p • removal K k j t),?_ ,?_⟩ -- U
 · have hr:= Row.pull (K:=K) (W:=W) (D:=D) (Y:=Y) k j t ((labelAt ..).1 (hk _ v)) (fun v=> mem_compl.mp (hk _ h) ((Window.mem_Tset ..).2 v)) (z d) (g d); rw [q _ d] at hr; exact hr.coeff p
 intro y; unfold removal basisC Fock.remove; simp only [Pi.smul_apply,map_smul,star_smul]; rw [show star (winding (α) k)=p from fee_real _, smul_smul, show p*p=1 from fee_one _,one_smul]; unfold Lifted.index; rw [ht]
lemma create_zone {f:Ket (Single α)} (v:withinM (labelQ α W) f) (h:withinM (Tset α) f)(P:Finset Cover) (u:withinM (modesIn α (park α P)) f) (g:P⊆Y)(z:P⊆ S)(q:Disjoint D P):
    create f∈ σ 0 1 0:=by
 nth_rw 1 [←basis_expand f]; rw [map_sum]; let U:=σ 0 1 0; apply U.sum_mem
 rintro ⟨⟨x,j⟩,t⟩ _; let i:= ((x,j),t); rw [map_smul]; by_cases hp:f.ofLp i=0; · rw [hp,zero_smul]; exact U.zero_mem
 have hk(L:Finset (Single α))(p:withinM L f):i∈ L:= Classical.byContradiction fun z=> hp ((within_test ..).1 p _ z)
 apply U.smul_mem; obtain ⟨w,d,e⟩:= mem_image.mp ((modes_at ..).1 (hk _ u)); obtain ⟨k,p,b⟩:= nodePel e; subst w; have ht:(wrap (α)) k=x:= b; let P₀:=winding α k
 refine ⟨ P₀ • creation K k j t,(Row.push _ _ _ ((labelAt ..).1 (hk _ v)) ((Window.mem_Tset ..).1 (hk _ h)) (fun u=> Finset.disjoint_left.mp q u d) (z d) (g d)).coeff P₀,?_⟩
 intro y; unfold creation basisC; simp only [Pi.smul_apply,map_smul,smul_smul]; rw [show P₀*(winding α k)=1 from fee_one _,one_smul]; unfold Lifted.index; rw [ht]
open Stencil(rake)
-- orientation $b centroid. assemble count for both.
lemma rake_reserves {e:Type}(f g:e→FC (Single α))(hf:∀ x,f x∈ σ r m a)(hg:∀ x,g x∈ σ r m 0)(L:List e)(n:ℕ): Stencil.rake f g L n ∈ σ (L.length*r) (L.length*m) (n*a):=by
 induction L generalizing n with
 | nil=>cases n with|zero=> simp only [Stencil.rake,List.length_nil, zero_mul]; exact oneR| succ a=> rw [Stencil.rake]; exact Submodule.zero_mem _
 | cons i L h=>
    have hx(n k:ℕ){t:FC (Single α)}(p:t∈ σ r m k): t*Stencil.rake f g L n∈ σ ((i::L).length*r) ((i::L).length*m) (k+n*a):=by rw [List.length_cons,add_mul,add_mul,one_mul,one_mul,add_comm _ r,add_comm _ m]; exact hold p (h _)
    cases n; · rw [Stencil.rake]; exact zero_add (0*a) ▸ hx 0 0 (hg i)
    next n=>
     unfold Stencil.rake; apply Submodule.add_mem; · rw [Nat.succ_mul, add_comm _ a]; exact hx n a (hf i)
     exact zero_add ((n+1)*a) ▸ hx _ 0 (hg i) -- `n+1`

-- extension to Marble by basis aggregation at one m. Roomy instead of large count. supports need narrow continuous. use also for any rung. 
open Satin Tapestry Tapestry.Roomy
variable {f:Mark (K.c N)}
private lemma touchCont (N': Side) : Continuous (graft S N') := by
 apply continuous_pi; intro t; unfold Satin.graft; split; exact continuous_apply _; exact continuous_const
lemma extensionA (w:Roomy S α) (p:AtSupport false (park α S) f)(u:Continuous f) (g:∀ x y:Fields _, x.1=y.1 → f x=f y) (h:∀ x,f x∈ σ r m n): ∃ F:Buffered.Family K, F∈ Marble K W D X Y S r m n ∧ F N=f:= by
 classical
 let U:= σ r m n; let B:= Module.finBasis ℂ U; let I:= Fin (Module.finrank ℂ U); let A (i:Pane α):↥U:=⟨f (i,i), h _⟩; choose Z v a using (fun i:I=> (show ∃ F, Row K W D X Y S r m n F∧ ∀ x, F N x= (B i).val from (B i).property))
 let X'(i:I)(t:LinksC):= B.coord i (A (graft S α t)); let Z'(i:I):= X' i ∘ (fun x:PairsC=>x.1); have ht(i:I):Coeff false S (Z' i):= by
    refine Coeff.fromC false S ((B.coord i).continuous_of_finiteDimensional.comp (((u.comp (continuous_id.prodMk continuous_id)).subtype_mk (fun _=> h _)).comp (touchCont _))) (fun x y u=> congrArg (B.coord i) (Subtype.ext (p.dep _ _ (tack S α w x y u) (tack S α w x y u))))
 let T:=∑ i,scalar K (Z' i)* Z i; refine ⟨T, Submodule.sum_mem _ (fun i _=> Marble.entry (ht i) (v i)),?_⟩; funext t; let k:= A t.1; have hp: A (graft S α (onC α t.1))= k:= Subtype.ext (p.dep _ _ (untack S α (seats w) t.1) (untack S α (seats w) t.1)); have hx(i:I): (scalar K (Z' i)*Z i) N t= B.coord i k • (B i).val:= by rw [Pi.mul_apply,Pi.mul_apply,a]; change (X' i _ • (1: FC _))* _= _; unfold X'; rw [hp, Algebra.smul_mul_assoc,one_mul]
 unfold T; simp_rw [Finset.sum_apply,hx]; rw [show f t = k.val from g t _ rfl]; have he : k= ∑ i, B.coord i k • B i:= (B.sum_repr k).symm; conv_rhs=>rw [he];
 rw [Submodule.coe_sum]
 try rfl
end Reach
end Rubric
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Rubric
#print axioms Reach.remove_zone
#print axioms Reach.extensionA
#print axioms Reach.rake_reserves
