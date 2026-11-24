import YM.SU5.Relativistic.Rime
/-!
# Requires opening. Terms cancellation before cost.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m d Q:ℕ} {V:Waxy} {W:Finset ℤ} {E:ℂ} (K:Calibration) {j:Fin 3}
private lemma crossB {b q:Bool}{f g:Buffered.Family K}(V:∃ S,InTest K false S b f)(p:∃ T,InTest K false T q g):∃ z:ℂ,f*g=z • (g*f):=by
 obtain ⟨S,h⟩:=V; obtain ⟨T,v⟩:=p; refine ⟨Sector.grainB b q,funext fun m=>funext fun x=>?_⟩
 have hs:= ((h.mono (Finset.subset_union_left (s₂:=T))).support m).allV x; have hv:= ((v.mono (Finset.subset_union_right (s₁:=S))).support m).allV x; exact hs.sign_com hv
lemma occurence (X:Buffered.Family K→ℂ)(h:∀ D:Finset Cover,Scopes K D X)(A M:ℕ)
    (p:A ≤ Q) (s:∀ i∈W,(A:ℤ) ≤ i) (e:W⊆ TwistT Q)(v:∀ i∈plusHalf,∀ y:ℤ,y∉W→ V i y=0)
    (b: d+d ≥ zig K M)(x:A+A≥ zig K M)(u:0<d)(cost: X (billboard K V (baseX m d Q) j Q (archH Q))≠1): Stout K m d Q V j M W X:=by
 classical
 by_contra U
 let P:=baseX m d Q; let A0:=labB m d Q V W; let G:=Toes m d Q K j; let F:=Spring5 m d Q K j V; let S:=loftH m d Q 0 V
 have hx(L:List (XGr m))(p':L≠[])(z:L.Nodup): X (rolls G L*rolls F L)=0:=by
    obtain ⟨a,v'⟩:=(zig_here (K:=K) (floorline m Q d L) A0 M TA (8*(Q:ℤ)+1) (fun y k=> by obtain ⟨i,t,rfl⟩:= mem_image.mp k; exact (base_right ..).le) (fun y k=> by have he:= (withheld m d Q V (A:ℤ) W (by exact_mod_cast p) s e y k).1; change _ ≤ y TA; omega))
    let L₁:=rolls G L; let L₂:=rolls F L
    have hv: X (L₁*L₂)=price X (stripeP L.length) L₁*price X (stripeP L.length) L₂:=by by_contra e; apply U; exact ⟨L,L,L₂,A0,TA,a,p',p',z,z,rfl,.out rfl rfl,v',e⟩
    exact hv.trans (by rw [show price X (stripeP L.length) L₁= _ from quench V j W M X h b u U L p' z,zero_mul])
 let f(i):= G i*F i; have ht(i:XGr m):InTest K false S false (f i):= ((gyre_T ..).mono (singleton_subset_iff.mpr (base_stay m d Q 0 V i).2)).mul ((glebe_T K (archH Q) (baseX m d Q i) V Q j W v).mono ((via_pass m d Q V W i).trans (via_fur m d Q 0 V W e))) -- dot
 have hp(L:List (XGr m)):∃ z:ℂ, rolls f L = z • (rolls G L * rolls F L):=by
    induction L with
    | nil=> exact ⟨1,by simp [rolls]⟩
    | cons i L ih=>
       obtain ⟨w,u⟩:= ih; obtain ⟨s,e⟩:= crossB K (f:=F i) (g:=rolls G L) ⟨_,glebe_T K (archH Q) (baseX m d Q i) V Q j W v⟩ ⟨_,topsB j K m d Q L⟩
       refine ⟨w*s,?_⟩
       change (G i * F i)*(rolls f L)= _ • ((G i * rolls G L)*(F i * rolls F L)); rw [u,Algebra.mul_smul_comm,mul_assoc,←mul_assoc (F i),e]; simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,mul_smul,mul_assoc]
 have hz(L:List (XGr m))(p:L≠[])(u:L.Nodup):X (rolls f L)=0:=by
    let D:=floorline m Q d L; have he:InTest K true (D∪ A0) false (rolls G L*rolls F L):=by
       apply InTest.widen; exact (Bool.xor_self (stripeP L.length)) ▸ ((topsB j K m d Q L).mono subset_union_left).mul ((wingB V j K m d Q W v L).mono (subset_union_right (s₁:=D)))
    obtain ⟨w,r⟩:= hp L; rw [r,(h (D∪A0)).scale _ he,hx L p u]; exact smul_zero _
 let f'(i):= 1+ f i
 -- lifting identity dropout recursively with paid prefix of compulsory inclusions. use suffix chosen.
 have hC:(∀ i,InTest K true S false (f' i)):=fun i=> ((InTest.one).add (ht i)).widen
 have hu (L R:List (XGr m))(t:(L++R).Nodup): X (rolls f L*rolls f' R) = X (rolls f L):=by
    induction R generalizing L with
    | nil=> simp [rolls]
    | cons i R ih=>
       have ht': (L++R).Nodup:=t.sublist (List.Sublist.append (List.Sublist.refl L) (List.Sublist.cons _ (List.Sublist.refl R)))
       let x:=rolls f L; let y:=rolls f (L++[i]); let z:=rolls f' R
       have p'(L:List (XGr m)):InTest K false S false (rolls f L):=vat_even f L S (fun i _=> ht i)
       have hs:InTest K false S false z:= vat_even f' R _ (fun i _=> (InTest.one).add (ht i)); have hP:rolls f (L++[i])=x*f i:=by simp [rolls,x]
       have hv:(L++[i]).Nodup:= (List.nodup_append.mp (show ((L++[i])++R).Nodup from by simpa using t)).1
       change X (x*((1+ f i)*z))= _; rw [show x*((1+ f i)*z)=x*z+y*z from (by change _= _+rolls f (L++[i])*z; rw [hP,add_mul,one_mul,mul_add]; unfold f; simp only [mul_assoc]),(h S).plus_v _ _ ((p' L).mul hs).widen ((p' (L++[i])).mul hs).widen,show X (x*z)=_ from ih L ht',show X (y*z)=_ from ih (L++[i]) (by simpa using t),hz _ (by simp) hv,add_zero]
 apply cost; rw [show billboard K V P j Q (archH Q)=rolls f' (List.ofFn id) from ?_]; swap; · unfold billboard rolls; rw [List.map_ofFn]; rfl
 exact (show X (rolls f' (List.ofFn id))=1 from by have he:=hu [] (List.ofFn id) (by simp only [List.nil_append]; exact List.nodup_ofFn_ofInjective injective_id); rw [show rolls f []=1 from rfl, one_mul,(h S).unit] at he; exact he)
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.occurence
