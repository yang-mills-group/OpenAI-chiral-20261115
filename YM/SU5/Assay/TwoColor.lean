import YM.SU5.Assay.Intaglio
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
variable (K:Calibration)
local notation "Ω"=> Dome K
variable (W:Bool)(S T D:Finset Cover)(g:Cover→SU.E)
/-!
# A charged factorization basis with the physical support budget.
We supply paired pure components; no claim that *arbitrary* bases
in the original pure sectors present the charge term-by-term.
-/
variable {x y:Dome K}
def etched (q:ℂ):Submodule ℂ Ω:= Submodule.span ℂ {x|∃ a b:Ω,PureGauge K a ∧PureMatter K b∧a∈bay K D true∧b∈bay K D true∧pennant K g b=q•b∧x=a*b}

lemma etched_dressed (u:S∪T⊆D)(a:∀ i∈S,g i=1)(b:∀ i∈T,g i=SU.central)(p:x.val∈DressedPair K W S T D):x∈ etched K D g (phaseName W):=by
 let Q:=etched K D g (phaseName W)
 let M:= Q.map (screenHall K).val.toLinearMap
 have he:DressedPair K W S T D≤M:=by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨w,t,x,h,rfl⟩
    let c:Ω:=⟨scalar K w,broadCompile K D (.seed t)⟩
    have hx: InTest K true D false x:= (raw_test K W S T h).1.mono u
    let l:Ω:=⟨x,broadCompile K D hx⟩
    have Hc:pennant K g l=phaseName W • l:=appointed K D g _ _ (pocket_charge K W S T D g u a b h) (show InTest K true D false (phaseName W • x) from InTest.smul _ hx)
    exact ⟨c*l,Submodule.subset_span (show _∈_ from ⟨c,l,⟨D,w,t,rfl⟩,(show PureMatter K l from (raw_test K W S T h).2),InTest.seed t,hx,Hc,rfl⟩),rfl⟩
 obtain ⟨X,h,t⟩:=he p; exact (show X=x from Subtype.ext t) ▸ h
lemma fixed_etched (r:∀ i∈S,g i=1)(p:y∈bay K S true): y∈ etched K S g 1:=by
 obtain ⟨X,h⟩:=circulation S K ((locates ..).1 p)
 let L(i:Evens S):=tagWord S i.val
 have ht(i:Evens S): InTest K true S false (Sound.sing K (L i)):=i.property ▸ sung K (L i) (Satin.brand S _)
 let b(i:Evens S): Ω:= ⟨Sound.sing K (L i), broadCompile K S (ht i)⟩
 let a(i:Evens S):Ω:= ⟨scalar K (X i).val,broadCompile K S (.seed (X i).property)⟩
 let v:=∑ i:Evens S,a i*b i
 have hv:y=v:= Subtype.ext (h.trans (map_sum (screenHall K).val (fun i:Evens S=>a i*b i) univ).symm)
 rw [hv]; refine Submodule.sum_mem _ fun i _=>Submodule.subset_span (show _∈_ from ⟨a i,b i,⟨S,(X i).val,(X i).property,rfl⟩,wordIndependent K _,InTest.seed (X i).property,ht i,(fixed_local K S g r (x:=b i) (ht i)).trans (one_smul ..).symm,rfl⟩)
lemma etched_mul (q:ℂ)(p:x∈ etched K S g q)(h:y∈etched K T g 1)(j:S⊆D)(k:T⊆D) : x*y∈ etched K D g q:=by
 let Q:=etched K D g q
 refine Submodule.span_induction (p:=fun x _=>x*y∈Q) (fun x w=>?_) (by rw [zero_mul]; exact Q.zero_mem) (fun _ _ _ _ p q=>by rw [add_mul]; exact Q.add_mem p q) (fun a _ _ p=>by rw [smul_mul_assoc]; exact Q.smul_mem a p) p
 refine Submodule.span_induction (p:=fun y _=>x*y∈Q) (fun y p=>?_) (by rw [mul_zero]; exact Q.zero_mem) (fun _ _ _ _ p q=>by rw [mul_add]; exact Q.add_mem p q) (fun a _ _ p=>by rw [mul_smul_comm]; exact Q.smul_mem a p) h
 obtain ⟨f,b,p,v,e,r,u,rfl⟩:=p; obtain ⟨F,B,n,a,m,l,t,rfl⟩:=w
 refine Submodule.subset_span (show _∈_ from ⟨F*f,B*b,gaugePure_mul K n p,matterPure_mul K a v, (bay K D true).mul_mem (tallerBay _ _ _ j m) (tallerBay _ _ _ k e), (bay K D true).mul_mem (tallerBay _ _ _ j l) (tallerBay _ _ _ k r),?_,mul_mul_mul_comm ..⟩)
 rw [map_mul,t,u,one_smul,smul_mul_assoc]

local notation "q"=>phaseName W
def PureSplit (a b:Dome K) :Prop:= PureGauge K a∧PureMatter K b ∧ a∈bay K D true∧ b∈bay K D true ∧ ∃g:Cover→SU.E,pennant K g a=(q)⁻¹•a∧pennant K g b=q•b
lemma PureSplit.smul {a b:Dome K}(p:PureSplit K W D a b)(c:ℂ): PureSplit K W D (c•a) b:=by
 obtain ⟨h,t,x,y,g,w,z⟩:=p
 exact ⟨gaugePure_smul K h c,t,(bay K D true).smul_mem x _,y,g,by rw[map_smul,w,smul_comm],z⟩
def TwoColor (K:Calibration)(W:Bool)(D:Finset Cover):Submodule ℂ (Dome K):=
 Submodule.span ℂ {x|∃ a b:Dome K,PureSplit K W D a b ∧ x=a*b}
lemma bindColor (z:pennant K g x=x)(p:x∈etched K D g q)(h:g^5=1):x∈TwoColor K W D:=by
 let R:=TwoColor K W D
 rw [intaglio_full _ _ _ z]
 apply R.smul_mem
 refine Submodule.span_induction (p:=fun f _=>intaglio K g 1 f∈R) (fun f w=>?_) ?_ ?_ ?_ p
 · obtain ⟨a,b,k,t,u,v,w,rfl⟩:=w
   rw [intaglio_factor K g _ _ _ w]
   obtain ⟨v',u'⟩:=intaglio_pure K D g q _ u k
   exact Submodule.subset_span (show _∈_ from ⟨_,_,⟨u',t,v',v,g,intaglio_charge K g _ _ h (pname_period W),w⟩,rfl⟩)
 · rw [show (0:Ω)= (0:ℂ)•1 from by simp, intaglio_scale, zero_smul]; exact R.zero_mem
 · intro f a _ _ r t; rw [intaglio_add]; exact R.add_mem r t
 intro c a _ r;rw [intaglio_scale]; exact R.smul_mem c r
lemma TwoColor.dressed_visit (U V:Finset Cover)(p:x.val∈DressedPair K W S T V)(m:x∈enclave K)(z:y∈bay K U true)
    (s:S∪T⊆V)(v:V⊆D)(u:U⊆D)(h:Disjoint S T)(e:Disjoint V U): x*y∈TwoColor K W D:=by
 let f:Cover→SU.E:=fun i=> if i∈T then SU.central else 1
 have k:∀ i∈U,f i=1:=fun i w=>if_neg fun t=>Finset.disjoint_left.mp e (s (mem_union_right _ t)) w
 apply bindColor K W D f (by rw [map_mul,(colorFixed K).mp m f,fixed_local K U f k z])
    (etched_mul K V U D f _ (etched_dressed K W S T V f s (fun _ w=>if_neg fun b=> Finset.disjoint_left.mp h w b) (fun _ a=>if_pos a) p) (fixed_etched K U f k z) v u)
 funext i; rw [Pi.pow_apply,Pi.one_apply]; unfold f; split
 · exact royal_period
 exact one_pow _
def Presented (K:Calibration)(W:Bool)(D:Finset Cover)(x:Dome K)(L:List (Dome K × Dome K)): Prop:= x=(L.map (fun i=>i.1*i.2)).sum ∧ ∀ i∈ L,PureSplit K W D i.1 i.2
lemma TwoColor.list (p:x∈TwoColor K W D):∃ l,Presented K W D x l:=by
 let F(i:Ω×Ω):=i.1*i.2
 refine Submodule.span_induction (p:=fun f _=>∃ l,Presented K W D f l) (fun f h=>?_) ⟨[],by simp,by simp⟩ ?_ ?_ p
 · obtain ⟨a,b,v,rfl⟩:=h
   exact ⟨[(a,b)],by simp, by simpa using v⟩
 · rintro a b _ _ ⟨l,rfl,u⟩ ⟨y,rfl,v⟩
   exact ⟨l++y,by simp,fun i t=>Or.elim (List.mem_append.mp t) (u i) (v i)⟩
 rintro c a HH ⟨l,rfl,u⟩
 let A(i:Ω×Ω):=(c•i.1,i.2)
 refine ⟨l.map A,?_,fun i h=>?_⟩
 · clear u HH; change c• (l.map F).sum=_ ; induction l with
   | nil=> simp
   | cons a l ih=>
    change c• (F a+(l.map F).sum)= (c•a.1)*a.2+_
    rw [smul_add,smul_mul_assoc,ih];rfl
 obtain ⟨x,v,rfl⟩:=List.mem_map.mp h; exact (u x v).smul _ _ _ _
end YM.CF.Buffered.Afterglow.Six
