import YM.SU5.FiniteGaugeData.Marked.Variation.Hearth
/-! Based on Hearth / Vitrine evaluation, identifying parity odd tag span & evaluation basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)

variable (K:Calibration)
abbrev Singles:={i:Finset (Satin.Tag S)//Sound.treble (tagWord S i)=true}
private lemma vase (W:List (Tag S)): sing K (W.map (stock S)) = 0 ∨ ∃ (v:ℂ)(r:Finset (Tag S)), W.length = r.card ∧ sing K (W.map (stock S))=v • sing K (tagWord S r):=by
 induction W with
 | nil=> refine Or.inr ⟨1,∅,by simp,?_⟩; simp only [tagWord,List.map_nil,sort_empty,one_smul]
 | cons x W ih=>
    have he:sing K ((x :: W).map (stock S))=Sound.chord K (stock S x)*sing K (W.map (stock S)):=rfl
    rw [he]; rcases ih with ih|⟨c,r,v,e⟩
    · left; rw [ih,mul_zero]
    simp only [e]; have hu:Sound.chord K (stock S x) * c • sing K (tagWord S r)= c • (Sound.chord K (stock S x) *sing K (tagWord S r)):=funext fun i=> funext fun t=> Algebra.mul_smul_comm c ((Sound.chord K (stock S x)) i t) (sing K (tagWord S r) i t); rw [hu]
    have hx(i:Side)(t:Fields (K.c i)): Sound.chord K (stock S x) i t=(Satin.velvet S (K.c i)).term x:=by
       change Sound.chord _ _ _ _=Satin.thread _ _; unfold Sound.chord Satin.thread stock; split <;> rfl
    by_cases h:x∈r
    · left; rw [show Sound.chord _ _ * _ = 0 from ?_,smul_zero]; funext i t; change Sound.chord _ _ _ _*_= 0; rw [hx,spool_sing,velvetTag]; exact (Satin.velvet ..).tag_mute r x h
    right; refine ⟨c*Fock.parity x r,insert x r,by rw [List.length_cons,v,card_insert_of_notMem h],?_⟩
    funext i t; simp only [Pi.smul_apply,Pi.mul_apply,hx,spool_sing,velvetTag]; rw [Poly.tag_any (Satin.velvet S (K.c i)) r x h, smul_smul,mul_assoc,parity_sq,mul_one]
private lemma treble_size (u v:Chorus)(h:u.length = v.length): treble u=treble v:=by
 induction u generalizing v with
 | nil=> rw [show v=[] from List.length_eq_zero_iff.mp h.symm]
 | cons i u ih=>
    obtain _ | ⟨j,v⟩:=v
    · simp at h
    rw [Sound.treble,Sound.treble,ih v (by simpa using h)] -- indentation
private lemma retail (x: PairsC→ℂ)(u:Chorus)(v:staves u S)(c:treble u=true) : note K x u=0 ∨ ∃ (y:ℂ)(r:Singles S),note K x u= y • note K x (tagWord S r.val):=by
 have he(u:Chorus)(g:staves u S): ∃ W:List (Tag S), u=W.map (stock S):=by
    induction u with
    | nil => exact ⟨[],rfl⟩
    | cons i u ih=> let j:Tag S:= ⟨i,g i List.mem_cons_self⟩; obtain ⟨V,p⟩:= ih fun a t=> g a (List.mem_cons_of_mem _ t); exact ⟨j::V,congrArg (i::·) p⟩
 obtain ⟨W,rfl⟩:=he _ v; unfold note; rcases vase S K W with eq|⟨a,r,h,eq⟩
 · left; rw [eq,mul_zero]
 have ht: Sound.treble (tagWord S r)=true:= (treble_size _ (W.map (stock S)) (by simp [tagWord,h])).trans c
 exact Or.inr ⟨a,⟨r,ht⟩,by rw [eq]; exact funext fun i=> funext fun t=> Algebra.mul_smul_comm a (scalar K x i t) (sing K (tagWord S r) i t)⟩
lemma swindleSingle (x:Purse S)(a:Chorus)(z:ℂ): z • note K x.val a=note K (hue S x z).val a:=by
 funext i t; rw [Pi.smul_apply,Pi.smul_apply,note_v,note_v,show (hue S x z).val _=z*_ from rfl,mul_smul]
lemma circSingle {x:Family K}(h:InTest K true S true x):∃ a:Singles S → Purse S,x=∑ t:Singles S,note K (a t).val (tagWord S t.val):=by
 let Z:Purse S:=⟨0,⟨fun _=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩⟩
 have q(u): note K (Z.val) u=0:=by funext i t; rw [note_v]; change (0:ℂ) • _=0; rw [zero_smul]
 have q'(f:Family K)(p:f=0):∃ a:Singles S→Purse S,f=∑ t:Singles S,note K (a t).val (tagWord S t.val):=⟨fun _=>Z,by simp [q,p]⟩
 refine Submodule.span_induction (p:=fun x _=>∃ a:Singles S→Purse S,x=∑ t:Singles S,note K (a t).val (tagWord S t.val)) (fun i p=> ?_) (q' _ rfl) ?_ ?_ (whole h)
 · obtain ⟨F,u,v,w,P,rfl⟩:=p; rcases retail S K F u w P with e|⟨a,t,h⟩; exact q' _ e
   classical
   let d:Purse S:=⟨F,v⟩
   refine ⟨fun r=> if r=t then hue S d a else Z,?_⟩
   rw [sum_eq_single t,h]; simp only [ite_true]; exact swindleSingle S K d _ a
   · intro j _ m; simp only [m,ite_false,q]
   simp
 · rintro i j _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
   let z(t:Singles S): Purse S:=⟨(a t).val+(b t).val,⟨fun _=>by contradiction,Girt.kitE _ _ (fun (i j:ℂ)=>i+j) (by fun_prop) (a t).property.env (b t).property.env,fun x y p q=> congrArg₂ (fun (i j:ℂ)=> i+j) ((a t).property.locus _ _ p q) ((b t).property.locus _ _ p q)⟩⟩
   refine ⟨z,?_⟩; change _=∑ t:Singles S,note K ((a t).val+(b t).val) _; simp_rw [note_plus,sum_add_distrib]
 rintro i t _ ⟨a,rfl⟩; exact ⟨fun t=>hue S (a t) i, by rw [Finset.smul_sum]; exact sum_congr rfl fun t _=>swindleSingle S K (a t) _ i⟩

variable {N m:Side} (F:Family K)
lemma rubySingle (a:Singles S→Purse S)(t:F=∑ x:Singles S,note K (a x).val (tagWord S x.val))(p:Hosp S (K.c m))(y:ℝ)(hy:∀ x, ‖F m x‖ ≤ y): ∀ t:Singles S,∀ x:PairsC, ‖(a t).val x‖ ≤ y:=by
 let n:=K.c m; let φ0:=star (flake (Tset n)ᶜ); let J0:= occupy S n p
 intro i r
 choose u hu v using museum S n p
 let D:= replant S n r; let R(x:PairsC):=Prod.map (onC n) (onC n) (replant S n x)
 have hr(x:Singles S): (a x).val (R r)=(a x).val r:= by apply (a x).property.locus <;> exact fun i has _=>tail S n p _ _ has
 have he: twist (star (flake (Tset n)ᶜ)) (F m D)=∑ i:Singles S, (a i).val r • (u i.val • poke (i.val.map J0)) := by
    rw [t]; simp_rw [Finset.sum_apply,map_sum,note_v,spool_sing,velvetTag,twist_scalar]; apply sum_congr rfl; intro x _; change (a x).val (R r) • (twist (star (flake (Tset n)ᶜ))) ((Satin.velvet S n).tag _)=_; rw [v,hr]
 let T:= i.val.map J0
 have hp:crumb (twist φ0 (F m D)) T=((a i).val r)*(u i.val):=by
    rw [he, crumb_sum,sum_eq_single i, crumb_scale,crumb_scale,Pastry.chip,if_pos rfl,mul_one]
    · intro j _ K; rw [crumb_scale,crumb_scale,Pastry.chip,if_neg ?_,mul_zero,mul_zero]; exact fun x=> K (Subtype.ext (Finset.map_injective J0 x.symm))
    simp
 have hz:=calc
    ‖crumb (twist φ0 (F m D)) T‖ ≤ ‖twist φ0 (F m D)‖ := norm_entry _ _ _
    _ ≤ y:= by rw [twist_norm]; exact hy D
 rwa [hp,norm_mul,hu,mul_one] at hz

end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
