import YM.SU5.FiniteGaugeData.Marked.Variation.Sounds

/-! # Optional stronger norm: full fixed cover language at common op bound
across embedding m. Inspect coefficients on an actual host where box S fits,
in the rotated exterior basis for all actual generators. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)

def Tag := {a:Blot//nodeC a.1∈S}
abbrev who (a:Tag S):Blot:= (show {a:Blot//nodeC a.1∈S} from a).val
lemma nodeC_inj : Injective nodeC := by
 intro a b h; ext i; have he:=congrFun h i; unfold nodeC at he; simp at he; omega
private lemma pins_inj:Injective (fun a:Tag S=> (show ↥S×SpinIdx × SU.Slot from (⟨nodeC (who S a).1,(show {a:Blot//nodeC a.1∈S} from a).property⟩,(who S a).2))):=by
 rintro ⟨⟨x,i,j⟩,p⟩ ⟨⟨y,k,l⟩,q⟩ t; suffices h:(x,i,j)=(y,k,l) by cases h; rfl
 simp only [Prod.mk.injEq, Subtype.mk.injEq, who] at t ⊢; exact ⟨nodeC_inj t.1,t.2⟩
instance tagType: Fintype (Tag S):=letI : Finite (Tag S):= Finite.of_injective _ (pins_inj S); Fintype.ofFinite _
instance tagLIN:LinearOrder (Tag S):= LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

def tagWord (i:Finset (Tag S)):Chorus:= (i.sort (·≤·)).map (who S)
lemma brand (i: Finset (Tag S)): staves (tagWord S i) S := fun x p => by
 obtain ⟨b,h,rfl⟩:= List.mem_map.mp p; exact (show {x:Blot//_} from b).2

-- actual alternating Poly
private lemma thread_in (n:Side)(x:Blot):Reed.Fine (Tset n) univ true (thread n x):=by simpa [spool_cons,spool,Sound.treble] using (spool_fine n [x]) -- fix simpl

def velvet (n:Side): Poly (Tag S) (Single n) := ⟨fun i=>thread n (who S i), fun i j=>by
 rw [antiB,(thread_in n _).sign_com (thread_in n _)]; simp [Sector.grainB] ⟩
variable (K:Calibration)
lemma velvetTag (i:Finset (Tag S))(m:Side):spool (K.c m) (tagWord S i) =(velvet S (K.c m)).tag i:=by unfold Poly.tag spool; simp only [tagWord,List.map_map]; rfl
abbrev Evens := {i:Finset (Tag S)//treble (tagWord S i)=false}
variable {F:Family K}
-- span of notes compressed to these evens

def stock (x:Tag S):=(who S x)
private lemma pearl (a:Tag S):nodeC (stock S a).1∈ S:= (show {x:Blot//_} from a).2
private lemma vase (W:List (Tag S)): sing K (W.map (stock S)) = 0 ∨ ∃ (v:ℂ)(r:Finset (Tag S)), W.length = r.card ∧ sing K (W.map (stock S))=v • sing K (tagWord S r):=by
 induction W with
 | nil=> refine Or.inr ⟨1,∅,by simp,?_⟩; simp only [tagWord,List.map_nil,sort_empty,one_smul]
 | cons x W ih=>
    have he:sing K ((x :: W).map (stock S))=Sound.chord K (stock S x)*sing K (W.map (stock S)):=rfl
    rw [he]; rcases ih with ih|⟨c,r,v,e⟩
    · left; rw [ih,mul_zero]
    simp only [e]; have hu:Sound.chord K (stock S x) * c • sing K (tagWord S r)= c • (Sound.chord K (stock S x) *sing K (tagWord S r)):=funext fun i=> funext fun t=> Algebra.mul_smul_comm c ((Sound.chord K (stock S x)) i t) (sing K (tagWord S r) i t); rw [hu]
    have hx(i:Side)(t:Fields (K.c i)): Sound.chord K (stock S x) i t=(velvet S (K.c i)).term x:=by
       change Sound.chord _ _ _ _=thread _ _; unfold Sound.chord thread stock; split <;> rfl
    by_cases h:x∈r
    · left; rw [show Sound.chord _ _ * _ = 0 from ?_,smul_zero]; funext i t; change Sound.chord _ _ _ _*_= 0; rw [hx,spool_sing,velvetTag]; exact (velvet ..).tag_mute r x h
    right; refine ⟨c*Fock.parity x r,insert x r,by rw [List.length_cons,v,card_insert_of_notMem h],?_⟩
    funext i t; simp only [Pi.smul_apply,Pi.mul_apply,hx,spool_sing,velvetTag]; rw [Poly.tag_any (velvet S (K.c i)) r x h, smul_smul,mul_assoc,parity_sq,mul_one]
private lemma treble_size (u v:Chorus)(h:u.length = v.length): treble u=treble v:=by
 induction u generalizing v with
 | nil=> rw [show v=[] from List.length_eq_zero_iff.mp h.symm]
 | cons i u ih=>
    obtain _ | ⟨j,v⟩:=v
    · simp at h
    rw [Sound.treble,Sound.treble,ih v (by simpa using h)] -- indentation
private lemma retail (x: PairsC→ℂ)(u:Chorus)(v:Bracket S u)(c:Coeff true S x) : note K x u=0 ∨ ∃ (y:ℂ)(r:Evens S),note K x u= y • note K x (tagWord S r.val):=by
 have he(u:Chorus)(g:staves u S): ∃ W:List (Tag S), u=W.map (stock S):=by
    induction u with
    | nil => exact ⟨[],rfl⟩
    | cons i u ih=> let j:Tag S:= ⟨i,g i List.mem_cons_self⟩; obtain ⟨V,p⟩:= ih fun a t=> g a (List.mem_cons_of_mem _ t); exact ⟨j::V,congrArg (i::·) p⟩
 obtain ⟨W,rfl⟩:=he _ v.tines; unfold note; rcases vase S K W with eq|⟨a,r,h,eq⟩
 · left; rw [eq,mul_zero]
 have ht: Sound.treble (tagWord S r)=false:= (treble_size _ (W.map (stock S)) (by simp [tagWord,h])).trans v.harmony
 exact Or.inr ⟨a,⟨r,ht⟩,by rw [eq]; exact funext fun i=> funext fun t=> Algebra.mul_smul_comm a (scalar K x i t) (sing K (tagWord S r) i t)⟩
lemma bracketV (t:Evens S):Bracket S (tagWord S t.val):= ⟨brand S t.val,t.property⟩
lemma swindle (x:Purse S)(a:Chorus)(v:Bracket S a)(z:ℂ): z • note K x.val a=note K (hue S x z).val a:=by
 funext i t; rw [Pi.smul_apply,Pi.smul_apply,note_v,note_v,show (hue S x z).val _=z*_ from rfl,mul_smul]
lemma circulation {x:Family K}(h:InTest K true S false x):∃ a:Evens S → Purse S,x=∑ t:Evens S,note K (a t).val (tagWord S t.val):=by
 let Z:Purse S:=⟨0,⟨fun _=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩⟩
 have q(u): note K (Z.val) u=0:=by funext i t; rw [note_v]; change (0:ℂ) • _=0; rw [zero_smul]
 have q'(f:Family K)(p:f=0):∃ a:Evens S→Purse S,f=∑ t:Evens S,note K (a t).val (tagWord S t.val):=⟨fun _=>Z,by simp [q,p]⟩
 refine Submodule.span_induction (p:=fun x _=>∃ a:Evens S→Purse S,x=∑ t:Evens S,note K (a t).val (tagWord S t.val)) (fun i p=> ?_) (q' _ rfl) ?_ ?_ (whole h)
 · obtain ⟨F,u,v,w,P,rfl⟩:=p; rcases retail S K F u ⟨w,P⟩ v with e|⟨a,t,h⟩; exact q' _ e
   classical
   let d:Purse S:=⟨F,v⟩
   refine ⟨fun r=> if r=t then hue S d a else Z,?_⟩
   rw [sum_eq_single t,h]; simp only [ite_true]; exact swindle S K d _ (bracketV ..) a
   · intro j _ m; simp only [m,ite_false,q]
   simp
 · rintro i j _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
   let z(t:Evens S): Purse S:=⟨(a t).val+(b t).val,⟨fun _=>by contradiction,Girt.kitE _ _ (fun (i j:ℂ)=>i+j) (by fun_prop) (a t).property.env (b t).property.env,fun x y p q=> congrArg₂ (fun (i j:ℂ)=> i+j) ((a t).property.locus _ _ p q) ((b t).property.locus _ _ p q)⟩⟩
   refine ⟨z,?_⟩; change _=∑ t:Evens S,note K ((a t).val+(b t).val) _; simp_rw [note_plus,sum_add_distrib]
 rintro i t _ ⟨a,rfl⟩; exact ⟨fun t=>hue S (a t) i, by rw [Finset.smul_sum]; exact sum_congr rfl fun t _=>swindle S K (a t) _ (bracketV ..) i⟩
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.circulation
