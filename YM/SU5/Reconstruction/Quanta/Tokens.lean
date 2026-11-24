import YM.SU5.FiniteGaugeData.Tower.Atlas

/-! # Both-grade cover lifting. Generalizing Marked/Variation/Vitrine and Tower/Atlas. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)

variable (K:Calibration)
abbrev Tokens (g₀ : Bool):= {i:Finset (Tag S)//treble (tagWord S i) = g₀}
variable {F:Family K}
-- span of notes compressed to these evens

private lemma lotBundle (W:List (Tag S)): sing K (W.map (stock S)) = 0 ∨ ∃ (v:ℂ)(r:Finset (Tag S)), W.length = r.card ∧ sing K (W.map (stock S))=v • sing K (tagWord S r):=by
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
private lemma trebled_size (u v:Chorus)(h:u.length = v.length): treble u=treble v:=by
 induction u generalizing v with
 | nil=> rw [show v=[] from List.length_eq_zero_iff.mp h.symm]
 | cons i u ih=>
    obtain _ | ⟨j,v⟩:=v
    · simp at h
    rw [Sound.treble,Sound.treble,ih v (by simpa using h)] -- indentation
variable {g₀:Bool}
private lemma retailed (x: PairsC→ℂ)(u:Chorus)(hT:staves u S)(v:treble u=g₀)(c:Coeff true S x) : note K x u=0 ∨ ∃ (y:ℂ)(r:Tokens S g₀),note K x u= y • note K x (tagWord S r.val):=by
 have he(u:Chorus)(g:staves u S): ∃ W:List (Tag S), u=W.map (stock S):=by
    induction u with
    | nil => exact ⟨[],rfl⟩
    | cons i u ih=> let j:Tag S:= ⟨i,g i List.mem_cons_self⟩; obtain ⟨V,p⟩:= ih fun a t=> g a (List.mem_cons_of_mem _ t); exact ⟨j::V,congrArg (i::·) p⟩
 obtain ⟨W,rfl⟩:=he _ hT; unfold note; rcases lotBundle S K W with eq|⟨a,r,h,eq⟩
 · left; rw [eq,mul_zero]
 have ht: Sound.treble (tagWord S r)=g₀:= (trebled_size _ (W.map (stock S)) (by simp [tagWord,h])).trans v
 exact Or.inr ⟨a,⟨r,ht⟩,by rw [eq]; exact funext fun i=> funext fun t=> Algebra.mul_smul_comm a (scalar K x i t) (sing K (tagWord S r) i t)⟩
lemma vanc (x:Purse S)(a:Chorus)(z:ℂ): z • note K x.val a=note K (hue S x z).val a:=by
 funext i t; rw [Pi.smul_apply,Pi.smul_apply,note_v,note_v,show (hue S x z).val _=z*_ from rfl,mul_smul]
lemma tokenC {x:Family K}(h:InTest K true S g₀ x):∃ a:Tokens S g₀ → Purse S,x=∑ t:Tokens S g₀,note K (a t).val (tagWord S t.val):=by
 let Z:Purse S:=⟨0,⟨fun _=>by contradiction,Girt.rite_c _,fun _ _ _ _=>rfl⟩⟩
 have q(u): note K (Z.val) u=0:=by funext i t; rw [note_v]; change (0:ℂ) • _=0; rw [zero_smul]
 have q'(f:Family K)(p:f=0):∃ a:Tokens S g₀→Purse S,f=∑ t:Tokens S g₀,note K (a t).val (tagWord S t.val):=⟨fun _=>Z,by simp [q,p]⟩
 refine Submodule.span_induction (p:=fun x _=>∃ a:Tokens S g₀→Purse S,x=∑ t:Tokens S g₀,note K (a t).val (tagWord S t.val)) (fun i p=> ?_) (q' _ rfl) ?_ ?_ (whole h)
 · obtain ⟨F,u,v,w,P,rfl⟩:=p; rcases retailed S K F u w P v with e|⟨a,t,h⟩; exact q' _ e
   classical
   let d:Purse S:=⟨F,v⟩
   refine ⟨fun r=> if r=t then hue S d a else Z,?_⟩
   rw [sum_eq_single t,h]; simp only [ite_true]; exact vanc S K d _ a
   · intro j _ m; simp only [m,ite_false,q]
   simp
 · rintro i j _ _ ⟨a,rfl⟩ ⟨b,rfl⟩
   let z(t:Tokens S g₀): Purse S:=⟨(a t).val+(b t).val,⟨fun _=>by contradiction,Girt.kitE _ _ (fun (i j:ℂ)=>i+j) (by fun_prop) (a t).property.env (b t).property.env,fun x y p q=> congrArg₂ (fun (i j:ℂ)=> i+j) ((a t).property.locus _ _ p q) ((b t).property.locus _ _ p q)⟩⟩
   refine ⟨z,?_⟩; change _=∑ t:Tokens S g₀,note K ((a t).val+(b t).val) _; simp_rw [note_plus,sum_add_distrib]
 rintro i t _ ⟨a,rfl⟩; exact ⟨fun t=>hue S (a t) i, by rw [Finset.smul_sum]; exact sum_congr rfl fun t _=>vanc S K (a t) _ i⟩
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.tokenC

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open Reed (Fine think)
open Fock Pastry Tenant

variable {g₀:Bool}
section extend
variable (S:Finset Cover)(K':Calibration)(n:Side)
local notation "s₀"=> K'.c n
local notation "l₀"=> Satin.region S (K'.c n)

variable (t:Tivoli S (K'.c n))
local notation "φ"=> star (flake (Tset (K'.c n))ᶜ)
local notation "J"=> occupy S (K'.c n) (t.hosp)
noncomputable def sonata (t:Tivoli S (K'.c n))(q:Tokens S g₀):ℂ:= (museum S (K'.c n) t.hosp q.val).choose
local notation "σ"=> sonata S K' n t
lemma sonata_unit (q:Tokens S g₀): ‖σ q‖=1:= (museum S (K'.c n) t.hosp q.val).choose_spec.1
lemma sonata_ne (q:Tokens S g₀): σ q≠0:= norm_pos_iff.mp ((sonata_unit S K' n t q).symm ▸ zero_lt_one)
lemma sonata_expands (q:Tokens S g₀): twist φ ((velvet S (K'.c n)).tag q.val)= σ q • poke (q.val.map J):= (museum S (K'.c n) _ q.val).choose_spec.2

def tint(A:FC (Single (K'.c n))) (q:Tokens S g₀):= (σ q)⁻¹ * crumb (twist φ A) (q.val.map J)
local notation "sliceA"=> tint S K' n t
lemma quoteToken (A:FC (Single (K'.c n)))(q:Tokens S g₀):‖sliceA A q‖≤‖A‖:= by unfold tint; rw [norm_mul,norm_inv,sonata_unit,inv_one,one_mul]; exact (norm_entry ..).trans_eq (twist_norm ..)
lemma lengthline{q:Tokens S g₀}(x y:FC (Single (K'.c n)))(z:ℂ):sliceA (z • x+y) q=z*sliceA x q+sliceA y q:=by unfold tint; rw [map_add,twist_scalar,Pastry.crumb_add,Pastry.crumb_scale]; ring
lemma tintscont{q:Tokens S g₀}:Continuous (fun A=>tint S K' n t A q):=by
 unfold tint Pastry.crumb; apply Continuous.mul continuous_const; exact (breeze _).matrix_elem _ _
variable {f : Family K'}
lemma places (a:Tokens S g₀→Purse S)(h:f=∑ q:Tokens S g₀,note K' (a q).val (tagWord S q.val))(x:Fields (K'.c n)): twist φ (f n x)=∑ q:Tokens S g₀,(a q).1 (Prod.map (onC _) (onC _) x) • (σ q • poke (q.val.map J)):=by
 rw [h]; simp_rw [Finset.sum_apply,map_sum,note_v,spool_sing,velvetTag,twist_scalar]; exact Finset.sum_congr rfl fun q _=> congrArg ((a q).val (Prod.map (onC _) (onC _) x) • ·) (sonata_expands S K' n t q)
lemma charged_both (a:Tokens S g₀→Purse S)(h:f=∑ q:Tokens S g₀,note K' (a q).val (tagWord S q.val))(x:Fields (K'.c n))(q:Tokens S g₀): sliceA (f n x) q=(a q).val (Prod.map (onC _) (onC _) x):=by
 unfold tint
 rw [places S K' n t a h x,crumb_sum,sum_eq_single q,crumb_scale,crumb_scale,Pastry.chip,if_pos rfl,mul_one,mul_left_comm,inv_mul_cancel₀ (sonata_ne S K' n t q),mul_one]
 · intro j _ K0; rw [crumb_scale,crumb_scale,Pastry.chip,if_neg ?_,mul_zero,mul_zero]; exact fun x=> K0 (Subtype.ext (Finset.map_injective J x.symm))
 simp
lemma grades_stitch {A:FC (Single (K'.c n))}(p: Fine (Tset s₀) (modesIn s₀ l₀) g₀ A): A=∑ q:Tokens S g₀,sliceA A q • (velvet S (K'.c n)).tag q.val:=by
 obtain ⟨f,h,e⟩:= realizes_modes S K' n p; obtain ⟨a,v⟩:= tokenC S K' h
 let x:Fields (K'.c n):=(1,1)
 rw [←e x]; trans (∑ q:Tokens S g₀,note K' (a q).val (tagWord S q.val)) n x
 · rw [←v]
 simp_rw [Finset.sum_apply,note_v,spool_sing,velvetTag,charged_both S K' n t a v x]

-- measurable Borel lifting of coefficients
variable (fP:Mark (K'.c n)) (h:AtSupport g₀ (Satin.region S (K'.c n)) fP)
abbrev pielet (q:Tokens S g₀)(x:PairsC):ℂ:= sliceA (fP (replant S (K'.c n) x)) q
include h
lemma brushToken (q:Tokens S g₀):Coeff true S (pielet S K' n t fP q):=by
 refine ⟨fun _=>by contradiction,Girt.pole_w (fun v:PairsC=>fP (replant S (K'.c n) v)) (fun x=>tint S K' n t x q) (tintscont S K' n t) (Env.along (g:=replant S (K'.c n)) h.env (replant_b S _)),?_⟩
 intro x y a b; exact congrArg (fun z=>tint S K' n t z q) (h.dep _ _ (based S _ t _ _ a) (based S _ t _ _ b)) -- tune `..`
omit h
noncomputable def outAtlas (g₀:Bool):Family K':=∑ q:Tokens S g₀,note K' (pielet S K' n t fP q) (tagWord S q.val)
local notation "Ξ"=>outAtlas S K' n t fP g₀
include h
lemma gradeBook: InTest K' true S g₀ Ξ:=by
 refine .sum _ _ fun (q:Tokens S g₀) _=>?_
 have ht:=Sound.note_t K' _ (brushToken S K' n t fP h q) (brand S q.val); rw [q.property] at ht; exact ht
lemma payed_both: Ξ n=fP:=by
 funext x
 have hr: fP (replant S (K'.c n) (Prod.map (onC _) (onC _) x))= fP x:= h.dep _ _ (graft_native S _ t _) (graft_native S _ t _)
 unfold outAtlas; simp_rw [Finset.sum_apply,note_v,pielet,spool_sing,velvetTag,hr]; exact (Tower.grades_stitch S K' n t (h.allV x)).symm

end extend
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.gradeBook
#print axioms YM.CF.Buffered.Afterglow.Tower.payed_both
